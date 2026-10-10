import WotsLamport.Submission.JointOracleTrace

namespace WotsLamport.Submission
open SecretRelease OracleComp MeasureTheory

theorem measure_target_mem_list_le {Ω R : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) (target : Ω → R) (ε : ENNReal)
    (mass : ∀ r, μ {ω | target ω = r} ≤ ε) (values : List R) :
    μ {ω | target ω ∈ values} ≤ (values.length : ENNReal)*ε := by
  classical
  induction values with
  | nil => simp
  | cons value rest ih =>
    have he : {ω | target ω ∈ value::rest} =
        {ω | target ω = value} ∪ {ω | target ω ∈ rest} := by ext ω; simp
    rw [he]
    calc
      _ ≤ μ {ω | target ω = value} + μ {ω | target ω ∈ rest} := measure_union_le _ _
      _ ≤ ε + (rest.length : ENNReal)*ε := add_le_add (mass value) ih
      _ = ((value::rest).length : ENNReal)*ε := by
        simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
        ring

theorem measure_exists_finset_le {Ω I : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) (events : I → Set Ω) (bounds : I → ENNReal)
    (s : Finset I) (bound : ∀ i ∈ s, μ (events i) ≤ bounds i) :
    μ {ω | ∃ i ∈ s, ω ∈ events i} ≤ ∑ i ∈ s, bounds i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have he : {ω | ∃ j ∈ insert i s, ω ∈ events j} =
        events i ∪ {ω | ∃ j ∈ s, ω ∈ events j} := by ext ω; simp
    rw [he, Finset.sum_insert hi]
    exact (measure_union_le _ _).trans (add_le_add (bound i (by simp))
      (ih (fun j hj => bound j (by simp [hj]))))

/-- Several hidden targets may be correlated with one another. Only their
individual point masses enter this bound. The baseline oracle and program
are fixed independently of the whole target sample; an application must
establish that separation from the actual public view. -/
theorem multi_target_run_difference_bound {Ω I R A : Type}
    [MeasurableSpace Ω] [Fintype I]
    (μ : Measure Ω) (target : I → Ω → R) (ε : ENNReal)
    (mass : ∀ i r, μ {ω | target i ω = r} ≤ ε)
    (parse : I → ByteArray → Option R) (baseline : Hash) (changed : Ω → Hash)
    (offTargets : ∀ ω input, (∀ i, parse i input ≠ some (target i ω)) →
      baseline input = changed ω input)
    (p : Program A) (q : Nat) (bound : IsTotalQueryBound p q) :
    μ {ω | ROM.run baseline p ≠ ROM.run (changed ω) p} ≤
      (Fintype.card I : ENNReal) * (q : ENNReal) * ε := by
  classical
  let hit : I → Set Ω := fun i => {ω | target i ω ∈ traceTargets (parse i) baseline p}
  have hs : {ω | ROM.run baseline p ≠ ROM.run (changed ω) p} ⊆
      {ω | ∃ i ∈ (Finset.univ : Finset I), ω ∈ hit i} := by
    intro ω hbad
    by_contra hnone
    apply hbad
    apply run_eq_of_trace_agreement
    intro input hin
    apply offTargets ω input
    intro i he
    apply hnone
    exact ⟨i, Finset.mem_univ i, List.mem_filterMap.mpr ⟨input, hin, he⟩⟩
  have hh : ∀ i, μ (hit i) ≤ (q : ENNReal)*ε := by
    intro i
    have hlen : ((traceTargets (parse i) baseline p).length : ENNReal) ≤ q := by
      exact_mod_cast traceTargets_length_le (parse i) baseline p q bound
    calc
      _ ≤ ((traceTargets (parse i) baseline p).length : ENNReal)*ε :=
        measure_target_mem_list_le μ (target i) ε (mass i) _
      _ ≤ (q : ENNReal)*ε := by gcongr
  calc
    _ ≤ μ {ω | ∃ i ∈ (Finset.univ : Finset I), ω ∈ hit i} := measure_mono hs
    _ ≤ ∑ i ∈ (Finset.univ : Finset I), (q : ENNReal)*ε :=
      measure_exists_finset_le μ hit (fun _ => (q : ENNReal)*ε) Finset.univ (fun i _ => hh i)
    _ = _ := by simp [nsmul_eq_mul, mul_assoc]

end WotsLamport.Submission
