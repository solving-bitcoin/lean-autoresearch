import WotsLamport.Submission.OraclePrograms

namespace WotsLamport.Submission
open SecretRelease OracleSpec OracleComp MeasureTheory

/-- Queries on one execution path, including repeats. Unlike the support over
all possible answers, this trace is bounded by the adversary's query budget. -/
def queryTrace {A : Type} (h : Hash) (p : Program A) : List ByteArray :=
  OracleComp.construct (C := fun _ => List ByteArray) (fun _ => [])
    (fun input _ tail => input :: tail (h input)) p

@[simp] theorem queryTrace_pure {A : Type} (h : Hash) (a : A) :
    queryTrace h (pure a : Program A) = [] := rfl

@[simp] theorem queryTrace_query_bind {A : Type} (h : Hash) (input : ByteArray)
    (next : Label → Program A) :
    queryTrace h ((oracleQuery input : Program Label) >>= next) = input :: queryTrace h (next (h input)) := rfl

theorem queryTrace_length_le {A : Type} (h : Hash) (p : Program A) (q : Nat)
    (bound : IsTotalQueryBound p q) : (queryTrace h p).length ≤ q := by
  induction p using OracleComp.inductionOn generalizing q with
  | pure a => simp
  | query_bind input next ih =>
    rw [isTotalQueryBound_query_bind_iff] at bound
    simp only [queryTrace_query_bind, List.length_cons]
    have ht := ih (h input) (q-1) (bound.2 (h input))
    omega

/-- Agreement on the reference execution path suffices, even if the second
oracle would have had a different trace after a first disagreement. -/
theorem run_eq_of_trace_agreement {A : Type} (h g : Hash) (p : Program A)
    (agreement : ∀ input ∈ queryTrace h p, h input = g input) : ROM.run h p = ROM.run g p := by
  revert agreement
  induction p using OracleComp.inductionOn with
  | pure a => intro _; rfl
  | query_bind input next ih =>
    intro agreement
    have hi : h input = g input := agreement input (by simp)
    rw [run_query_bind, run_query_bind, ← hi]
    apply ih (h input)
    intro input' hinput'
    exact agreement input' (by simp [hinput'])

def traceTargets {R A : Type} (parse : ByteArray → Option R) (h : Hash) (p : Program A) : List R :=
  (queryTrace h p).filterMap parse

theorem traceTargets_length_le {R A : Type} (parse : ByteArray → Option R)
    (h : Hash) (p : Program A) (q : Nat) (bound : IsTotalQueryBound p q) :
    (traceTargets parse h p).length ≤ q :=
  (List.length_filterMap_le _ _).trans (queryTrace_length_le h p q bound)

theorem run_eq_of_target_miss {R A : Type} (parse : ByteArray → Option R) (target : R)
    (baseline changed : Hash) (p : Program A)
    (offTarget : ∀ input, parse input ≠ some target → baseline input = changed input)
    (miss : target ∉ traceTargets parse baseline p) : ROM.run baseline p = ROM.run changed p := by
  apply run_eq_of_trace_agreement
  intro input hi
  apply offTarget input
  intro he
  apply miss
  exact List.mem_filterMap.mpr ⟨input, hi, he⟩

theorem measure_mem_list_le {R : Type} [MeasurableSpace R] (μ : Measure R)
    (ε : ENNReal) (mass : ∀ r, μ {r} ≤ ε) (values : List R) :
    μ {r | r ∈ values} ≤ (values.length : ENNReal)*ε := by
  classical
  induction values with
  | nil => simp
  | cons value rest ih =>
    have he : {r | r ∈ value::rest} = {value} ∪ {r | r ∈ rest} := by ext r; simp
    rw [he]
    calc
      μ ({value} ∪ {r | r ∈ rest}) ≤ μ {value}+μ {r | r ∈ rest} := measure_union_le _ _
      _ ≤ ε+(rest.length : ENNReal)*ε := add_le_add (mass value) ih
      _ = ((value::rest).length : ENNReal)*ε := by
        simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
        ring

/-- Reprogramming only inputs containing one hidden target changes an
arbitrary bounded program with probability at most q times the target's
maximum singleton mass. The reference trace is independent of that target. -/
theorem reprogrammed_run_difference_bound {R A : Type} [MeasurableSpace R]
    (μ : Measure R) (ε : ENNReal) (mass : ∀ r, μ {r} ≤ ε)
    (parse : ByteArray → Option R) (baseline : Hash) (changed : R → Hash)
    (offTarget : ∀ target input, parse input ≠ some target → baseline input = changed target input)
    (p : Program A) (q : Nat) (bound : IsTotalQueryBound p q) :
    μ {target | ROM.run baseline p ≠ ROM.run (changed target) p} ≤ (q : ENNReal)*ε := by
  classical
  have hs : {target | ROM.run baseline p ≠ ROM.run (changed target) p} ⊆
      {target | target ∈ traceTargets parse baseline p} := by
    intro target hbad
    by_contra hmiss
    exact hbad (run_eq_of_target_miss parse target baseline (changed target) p (offTarget target) hmiss)
  calc
    μ {target | ROM.run baseline p ≠ ROM.run (changed target) p} ≤
        μ {target | target ∈ traceTargets parse baseline p} := measure_mono hs
    _ ≤ ((traceTargets parse baseline p).length : ENNReal)*ε := measure_mem_list_le μ ε mass _
    _ ≤ (q : ENNReal)*ε := by
      have hlen := traceTargets_length_le parse baseline p q bound
      have hc : ((traceTargets parse baseline p).length : ENNReal) ≤ (q : ENNReal) := by exact_mod_cast hlen
      gcongr

end WotsLamport.Submission
