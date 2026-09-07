import G1Release.Submission.FiniteProbability

namespace G1Release.Submission.HintProductLaw

/-! Regroup independent oracle and label coordinates. These equalities concern
countable product measures, so they retain the entire active-label oracle. -/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

variable {ι κ : Type*}

theorem infinitePi_sum_symm {X : ι ⊕ κ → Type*}
    [∀ i, MeasurableSpace (X i)] (μ : (i : ι ⊕ κ) → Measure (X i))
    [∀ i, IsProbabilityMeasure (μ i)] :
    MeasurePreserving (MeasurableEquiv.sumPiEquivProdPi X).symm
      ((Measure.infinitePi fun i => μ (.inl i)).prod
        (Measure.infinitePi fun i => μ (.inr i))) (Measure.infinitePi μ) := by
  refine ⟨(MeasurableEquiv.sumPiEquivProdPi X).symm.measurable, ?_⟩
  apply Measure.eq_infinitePi
  intro s t ht
  classical
  rw [Measure.map_apply (MeasurableEquiv.sumPiEquivProdPi X).symm.measurable
    (MeasurableSet.pi s.countable_toSet (fun i _ => ht i))]
  have hpre : (MeasurableEquiv.sumPiEquivProdPi X).symm ⁻¹' (s : Set (ι ⊕ κ)).pi t =
      ((s.toLeft : Set ι).pi (fun i => t (.inl i))) ×ˢ
      ((s.toRight : Set κ).pi (fun i => t (.inr i))) := by
    ext state
    simp only [Set.mem_preimage, Set.mem_pi, Finset.mem_coe, Set.mem_prod,
      Finset.mem_toLeft, Finset.mem_toRight]
    constructor
    · intro h
      exact ⟨fun i hi => h (.inl i) hi, fun i hi => h (.inr i) hi⟩
    · rintro ⟨hl, hr⟩ (i | i) hi
      · exact hl i hi
      · exact hr i hi
  rw [hpre, Measure.prod_prod,
    Measure.infinitePi_pi _ (fun i _ => ht (.inl i)),
    Measure.infinitePi_pi _ (fun i _ => ht (.inr i)),
    Finset.prod_sum_eq_prod_toLeft_mul_prod_toRight]

theorem infinitePi_sum {X : ι ⊕ κ → Type*}
    [∀ i, MeasurableSpace (X i)] (μ : (i : ι ⊕ κ) → Measure (X i))
    [∀ i, IsProbabilityMeasure (μ i)] :
    MeasurePreserving (MeasurableEquiv.sumPiEquivProdPi X)
      (Measure.infinitePi μ)
      ((Measure.infinitePi fun i => μ (.inl i)).prod
        (Measure.infinitePi fun i => μ (.inr i))) :=
  (infinitePi_sum_symm μ).symm (MeasurableEquiv.sumPiEquivProdPi X).symm

end G1Release.Submission.HintProductLaw
