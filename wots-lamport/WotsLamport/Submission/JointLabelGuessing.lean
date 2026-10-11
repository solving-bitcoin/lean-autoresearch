import WotsLamport.Submission.LabelGuessing
import WotsLamport.Submission.ChainPartitionLaw

namespace WotsLamport.Submission
open SecretRelease MeasureTheory ProbabilityTheory

noncomputable def pivotTableEquiv {I A : Type} (i : I) :
    (I → A) ≃ A × ({j : I // j ≠ i} → A) := by
  classical
  exact {
    toFun := fun table => (table i, fun j => table j.val)
    invFun := fun sample j => if hj : j = i then sample.1 else sample.2 ⟨j,hj⟩
    left_inv := by intro table; funext j; by_cases hj : j = i <;> simp [hj]
    right_inv := by
      intro sample
      refine Prod.ext (by simp) ?_
      funext j
      simp [j.property] }

noncomputable def selectedPivotTable {I : Type} (i : I) (bits : I → Bool)
    (rest : {j : I // j ≠ i} → Pair) (value : Label) : I → Label := by
  classical
  exact fun j => if hj : j = i then value else (rest ⟨j,hj⟩).get (bits j)

theorem selected_pivot_table {I : Type} (i : I) (bits : I → Bool)
    (rest : {j : I // j ≠ i} → Pair) (pivot : Pair) :
    (fun j => ((pivotTableEquiv i).symm (pivot,rest) j).get (bits j)) =
      selectedPivotTable i bits rest (pivot.get (bits i)) := by
  classical
  funext j
  by_cases hj : j = i <;> simp [pivotTableEquiv, selectedPivotTable, hj]

theorem uniform_selected_table_guess_fixed {I : Type} [Fintype I]
    (bits : I → Bool) (guess : (I → Label) → I × Label) (i : I) :
    uniformOn (Set.univ : Set (I → Pair))
      {table | (guess (fun j => (table j).get (bits j))).2 = (table i).get (!(bits i))} ≤
        (2 : ENNReal)/2^256 := by
  classical
  letI := Fintype.ofFinite Pair
  let e := pivotTableEquiv (A := Pair) i
  let event : Set (Pair × ({j : I // j ≠ i} → Pair)) :=
    {sample | (guess (fun j => (e.symm sample j).get (bits j))).2 =
      (e.symm sample i).get (!(bits i))}
  have reindex : {table : I → Pair |
      (guess (fun j => (table j).get (bits j))).2 = (table i).get (!(bits i))} = e ⁻¹' event := by
    ext table
    simp only [Set.mem_preimage, Set.mem_setOf_eq, event, Equiv.symm_apply_apply]
  rw [reindex, Shamir.uniform_event_equiv e, uniform_product,
    Measure.prod_apply_symm MeasurableSet.of_discrete]
  calc
    _ ≤ ∫⁻ _ : ({j : I // j ≠ i} → Pair), (2 : ENNReal)/2^256
        ∂uniformOn (Set.univ : Set ({j : I // j ≠ i} → Pair)) := by
      apply lintegral_mono
      intro rest
      have he : {pivot : Pair | (pivot,rest) ∈ event} =
          {pivot | (guess (selectedPivotTable i bits rest (pivot.get (bits i)))).2 =
            pivot.get (!(bits i))} := by
        ext pivot
        simp only [Set.mem_setOf_eq, event, e, selected_pivot_table]
        simp [pivotTableEquiv]
      rw [he]
      exact uniform_labelGuess_bound (bits i)
        (fun value => (guess (selectedPivotTable i bits rest value)).2)
    _ = (2 : ENNReal)/2^256 := by simp

/-- The attacker may select its target wire after seeing every authorized
label. A union over wires is sufficient; there is no union over messages. -/
theorem uniform_selected_table_guess {I : Type} [Fintype I]
    (bits : I → Bool) (guess : (I → Label) → I × Label) :
    uniformOn (Set.univ : Set (I → Pair))
      {table | let claim := guess (fun j => (table j).get (bits j))
        claim.2 = (table claim.1).get (!(bits claim.1))} ≤
        (Fintype.card I : ENNReal) * (2 : ENNReal)/2^256 := by
  classical
  let event : I → Set (I → Pair) := fun i =>
    {table | (guess (fun j => (table j).get (bits j))).2 = (table i).get (!(bits i))}
  have subset : {table : I → Pair | let claim := guess (fun j => (table j).get (bits j))
      claim.2 = (table claim.1).get (!(bits claim.1))} ⊆
        {table | ∃ i ∈ (Finset.univ : Finset I), table ∈ event i} := by
    intro table win
    exact ⟨(guess (fun j => (table j).get (bits j))).1, Finset.mem_univ _, win⟩
  calc
    _ ≤ uniformOn (Set.univ : Set (I → Pair))
        {table | ∃ i ∈ (Finset.univ : Finset I), table ∈ event i} := measure_mono subset
    _ ≤ ∑ i ∈ (Finset.univ : Finset I), (2 : ENNReal)/2^256 :=
      measure_exists_finset_le _ event (fun _ => (2 : ENNReal)/2^256) Finset.univ
        (fun i _ => uniform_selected_table_guess_fixed bits guess i)
    _ = _ := by simp [nsmul_eq_mul, div_eq_mul_inv, mul_assoc]

end WotsLamport.Submission
