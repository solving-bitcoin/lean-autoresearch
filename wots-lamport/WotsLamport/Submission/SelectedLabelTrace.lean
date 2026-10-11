import WotsLamport.Submission.JointLabelGuessing

namespace WotsLamport.Submission
open SecretRelease MeasureTheory ProbabilityTheory

/-- A whole bounded query-derived list may depend on every selected label.
Each list position is still a guess function of only those selected labels.
This avoids falsely asserting independence of opposite labels and the view. -/
theorem uniform_selected_table_list_hit {I : Type} [Fintype I]
    (bits : I → Bool) (values : (I → Label) → List Label) (q : Nat)
    (bound : ∀ selected, (values selected).length ≤ q) :
    uniformOn (Set.univ : Set (I → Pair))
      {table | ∃ i, (table i).get (!(bits i)) ∈ values (fun j => (table j).get (bits j))} ≤
        (Fintype.card I : ENNReal) * q * (2 : ENNReal)/2^256 := by
  classical
  let fallback : Label := Vector.replicate 32 0
  let event : I × Fin q → Set (I → Pair) := fun index =>
    {table | (values (fun j => (table j).get (bits j)))[index.2.val]?.getD fallback =
      (table index.1).get (!(bits index.1))}
  have subset : {table : I → Pair | ∃ i,
      (table i).get (!(bits i)) ∈ values (fun j => (table j).get (bits j))} ⊆
      {table | ∃ index ∈ (Finset.univ : Finset (I × Fin q)), table ∈ event index} := by
    rintro table ⟨i,member⟩
    obtain ⟨n,hn,he⟩ := List.mem_iff_getElem.mp member
    refine ⟨(i,⟨n,lt_of_lt_of_le hn (bound _)⟩),Finset.mem_univ _,?_⟩
    change (_[n]?).getD fallback = _
    rw [getElem?_pos (values (fun j => (table j).get (bits j))) n hn,
      Option.getD_some, he]
  have mass (index : I × Fin q) :
      uniformOn (Set.univ : Set (I → Pair)) (event index) ≤ (2 : ENNReal)/2^256 :=
    uniform_selected_table_guess_fixed bits
      (fun selected => (index.1, (values selected)[index.2.val]?.getD fallback)) index.1
  calc
    _ ≤ uniformOn (Set.univ : Set (I → Pair))
        {table | ∃ index ∈ (Finset.univ : Finset (I × Fin q)), table ∈ event index} :=
      measure_mono subset
    _ ≤ ∑ index ∈ (Finset.univ : Finset (I × Fin q)), (2 : ENNReal)/2^256 :=
      measure_exists_finset_le _ event (fun _ => (2 : ENNReal)/2^256) Finset.univ
        (fun index _ => mass index)
    _ = _ := by
      simp [Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul, div_eq_mul_inv, mul_assoc]

/-- Before release, a fixed guess can target either member of its chosen pair.
Any artifact/oracle dependence of this guess must first be removed by the
actual oracle comparison; that is not a premise hidden in this statement. -/
theorem uniform_no_label_guess {I : Type} [Fintype I] (claim : I × Label) :
    uniformOn (Set.univ : Set (I → Pair))
      {table | claim.2 = (table claim.1).get false ∨ claim.2 = (table claim.1).get true} ≤
        (4 : ENNReal)/2^256 := by
  classical
  have left := uniform_selected_table_guess_fixed (fun _ : I => true)
    (fun _ => claim) claim.1
  have right := uniform_selected_table_guess_fixed (fun _ : I => false)
    (fun _ => claim) claim.1
  change uniformOn (Set.univ : Set (I → Pair))
    ({table | claim.2 = (table claim.1).get false} ∪
      {table | claim.2 = (table claim.1).get true}) ≤ _
  calc
    _ ≤ uniformOn (Set.univ : Set (I → Pair)) {table | claim.2 = (table claim.1).get false} +
        uniformOn (Set.univ : Set (I → Pair)) {table | claim.2 = (table claim.1).get true} :=
      measure_union_le _ _
    _ ≤ (2 : ENNReal)/2^256 + (2 : ENNReal)/2^256 := add_le_add left right
    _ = _ := by rw [ENNReal.div_add_div_same]; norm_num

end WotsLamport.Submission
