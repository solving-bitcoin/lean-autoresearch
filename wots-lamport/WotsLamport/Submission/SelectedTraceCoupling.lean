import WotsLamport.Submission.SelectedLabelTrace
import WotsLamport.Submission.ProductEventBounds

namespace WotsLamport.Submission
open SecretRelease MeasureTheory ProbabilityTheory OracleComp

/-- Hidden table entries remain independent of a query list chosen from all
selected labels. Opposite labels are handled by a separate conditional bound. -/
theorem uniform_hidden_selected_list_hit {I J : Type} [Fintype I] [Fintype J]
    (bits : J → Bool) (values : (J → Label) → List Label) (q : Nat)
    (bound : ∀ selected, (values selected).length ≤ q) :
    uniformOn (Set.univ : Set ((I → Label) × (J → Pair)))
      {sample | ∃ i, sample.1 i ∈ values (fun j => (sample.2 j).get (bits j))} ≤
        (Fintype.card I : ENNReal)*q/2^256 := by
  classical
  letI := Fintype.ofFinite Label
  letI := Fintype.ofFinite Pair
  rw [uniform_product, Measure.prod_apply_symm MeasurableSet.of_discrete]
  calc
    _ ≤ ∫⁻ _ : J → Pair, (Fintype.card I : ENNReal)*q/2^256
        ∂uniformOn (Set.univ : Set (J → Pair)) := by
      apply lintegral_mono
      intro labels
      let guesses := values (fun j => (labels j).get (bits j))
      have mass (i : I) :
          uniformOn (Set.univ : Set (I → Label)) {table | table i ∈ guesses} ≤
            (q : ENNReal)/2^256 := by
        have h := measure_target_mem_list_le (uniformOn (Set.univ : Set (I → Label)))
          (fun table => table i) ((1 : ENNReal)/2^256) (by
            intro label
            rw [uniform_coordinate_mass, bytes_card]
            norm_num) guesses
        have length : (guesses.length : ENNReal) ≤ q := by exact_mod_cast bound _
        calc
          _ ≤ (guesses.length : ENNReal)*((1 : ENNReal)/2^256) := h
          _ ≤ (q : ENNReal)*((1 : ENNReal)/2^256) := by gcongr
          _ = _ := by rw [← mul_div_assoc, mul_one]
      have h := measure_exists_finset_le (uniformOn (Set.univ : Set (I → Label)))
        (fun i => {table | table i ∈ guesses}) (fun _ => (q : ENNReal)/2^256)
        Finset.univ (fun i _ => mass i)
      change uniformOn (Set.univ : Set (I → Label))
        {table | ∃ i, table i ∈ guesses} ≤ (Fintype.card I : ENNReal)*q/2^256
      simpa only [Set.mem_preimage, Set.mem_setOf_eq, guesses, Finset.mem_univ, true_and,
        Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_div_assoc] using h
    _ = _ := by simp

/-- Query traces may depend on every selected label. This bound never
conditions on the absence of earlier hits. It requires an actual baseline
whose dependence is limited to the selected labels and independent data. -/
theorem selected_trace_difference_bound {I J A : Type} [Fintype I] [Fintype J]
    (bits : J → Bool) (parseNode parseLabel : ByteArray → Option Label)
    (baseline : (J → Label) → Hash) (changed : ((I → Label) × (J → Pair)) → Hash)
    (program : (J → Label) → Program A) (q : Nat)
    (bound : ∀ selected, IsTotalQueryBound (program selected) q)
    (offTargets : ∀ sample input,
      (∀ i, parseNode input ≠ some (sample.1 i)) →
      (∀ j, parseLabel input ≠ some ((sample.2 j).get (!(bits j)))) →
      baseline (fun j => (sample.2 j).get (bits j)) input = changed sample input) :
    uniformOn (Set.univ : Set ((I → Label) × (J → Pair)))
      {sample | let selected := fun j => (sample.2 j).get (bits j)
        ROM.run (baseline selected) (program selected) ≠ ROM.run (changed sample) (program selected)} ≤
      (Fintype.card I : ENNReal)*q/2^256 + (Fintype.card J : ENNReal)*q*2/2^256 := by
  classical
  let nodes selected := traceTargets parseNode (baseline selected) (program selected)
  let labels selected := traceTargets parseLabel (baseline selected) (program selected)
  let nodeHit : Set ((I → Label) × (J → Pair)) :=
    {sample | ∃ i, sample.1 i ∈ nodes (fun j => (sample.2 j).get (bits j))}
  let labelHit : Set ((I → Label) × (J → Pair)) :=
    {sample | ∃ j, (sample.2 j).get (!(bits j)) ∈ labels (fun j => (sample.2 j).get (bits j))}
  have subset : {sample : (I → Label) × (J → Pair) |
      let selected := fun j => (sample.2 j).get (bits j)
      ROM.run (baseline selected) (program selected) ≠ ROM.run (changed sample) (program selected)} ⊆
      nodeHit ∪ labelHit := by
    intro sample different
    by_contra absent
    apply different
    apply run_eq_of_trace_agreement
    intro input member
    apply offTargets sample input
    · intro i he
      exact absent (Or.inl ⟨i,List.mem_filterMap.mpr ⟨input,member,he⟩⟩)
    · intro j he
      exact absent (Or.inr ⟨j,List.mem_filterMap.mpr ⟨input,member,he⟩⟩)
  have nodeBound : uniformOn (Set.univ : Set ((I → Label) × (J → Pair))) nodeHit ≤
      (Fintype.card I : ENNReal)*q/2^256 :=
    uniform_hidden_selected_list_hit bits nodes q
      (fun selected => traceTargets_length_le _ _ _ q (bound selected))
  have labelBound : uniformOn (Set.univ : Set ((I → Label) × (J → Pair))) labelHit ≤
      (Fintype.card J : ENNReal)*q*2/2^256 := by
    have event_eq : labelHit = (Set.univ : Set (I → Label)) ×ˢ
        {table | ∃ j, (table j).get (!(bits j)) ∈ labels (fun j => (table j).get (bits j))} := by
      ext sample
      simp only [labelHit, Set.mem_setOf_eq, Set.mem_prod, Set.mem_univ, true_and]
    rw [event_eq]
    rw [uniform_product, Measure.prod_prod, measure_univ, one_mul]
    exact uniform_selected_table_list_hit bits labels q
      (fun selected => traceTargets_length_le _ _ _ q (bound selected))
  exact (measure_mono subset).trans ((measure_union_le _ _).trans (add_le_add nodeBound labelBound))

/-- Agreement may be established only on collision-free samples. The failure
probability is kept explicitly; no conditioning or renormalization is used. -/
theorem selected_trace_difference_on_good_bound {I J A : Type} [Fintype I] [Fintype J]
    (bits : J → Bool) (parseNode parseLabel : ByteArray → Option Label)
    (baseline : (J → Label) → Hash) (changed : ((I → Label) × (J → Pair)) → Hash)
    (program : (J → Label) → Program A) (q : Nat)
    (bound : ∀ selected, IsTotalQueryBound (program selected) q)
    (good : Set ((I → Label) × (J → Pair)))
    (offTargets : ∀ sample ∈ good, ∀ input,
      (∀ i, parseNode input ≠ some (sample.1 i)) →
      (∀ j, parseLabel input ≠ some ((sample.2 j).get (!(bits j)))) →
      baseline (fun j => (sample.2 j).get (bits j)) input = changed sample input) :
    uniformOn (Set.univ : Set ((I → Label) × (J → Pair)))
      {sample | let selected := fun j => (sample.2 j).get (bits j)
        ROM.run (baseline selected) (program selected) ≠ ROM.run (changed sample) (program selected)} ≤
      ((Fintype.card I : ENNReal)*q/2^256 + (Fintype.card J : ENNReal)*q*2/2^256) +
        uniformOn (Set.univ : Set ((I → Label) × (J → Pair))) goodᶜ := by
  classical
  let clipped sample := if sample ∈ good then changed sample
    else baseline (fun j => (sample.2 j).get (bits j))
  have clippedBound := selected_trace_difference_bound bits parseNode parseLabel baseline clipped
    program q bound (by
      intro sample input nodesMissing labelsMissing
      by_cases member : sample ∈ good
      · simpa only [clipped, if_pos member] using offTargets sample member input nodesMissing labelsMissing
      · simp only [clipped, if_neg member])
  have comparison := event_bound_of_agree_on_good
    (uniformOn (Set.univ : Set ((I → Label) × (J → Pair))))
    {sample | let selected := fun j => (sample.2 j).get (bits j)
      ROM.run (baseline selected) (program selected) ≠ ROM.run (changed sample) (program selected)}
    {sample | let selected := fun j => (sample.2 j).get (bits j)
      ROM.run (baseline selected) (program selected) ≠ ROM.run (clipped sample) (program selected)}
    good (by intro sample member; simp only [Set.mem_setOf_eq, clipped, if_pos member])
  exact comparison.trans (add_le_add clippedBound le_rfl)

end WotsLamport.Submission
