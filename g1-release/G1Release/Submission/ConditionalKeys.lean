import G1Release.Submission.LamportLaw

namespace G1Release.Submission.ConditionalKeys
open SecretRelease MeasureTheory ProbabilityTheory LamportLaw

/-- A bound conditional on the disclosed labels and any independent public
context lifts to the protected uniform distinct-pair distribution. -/
theorem bound {ι X : Type*} [Fintype ι] [MeasurableSpace X]
    [MeasurableSpace (ι → Pair)] [DiscreteMeasurableSpace (ι → Pair)]
    (bits : ι → Bool) (context : Measure X) [IsProbabilityMeasure context]
    (event : Set ((ι → Pair) × X)) (he : MeasurableSet event) (error : ENNReal)
    (hconditional : ∀ active x,
      uniformOn (Set.univ : Set (ι → Rank))
        {ranks | ((keysEquiv bits).symm (active,ranks),x) ∈ event} ≤ error) :
    ((uniformOn (Set.univ : Set (ι → Pair))).prod context) event ≤ error := by
  let activeLaw : Measure (ι → Label) := uniformOn Set.univ
  let rankLaw : Measure (ι → Rank) := uniformOn Set.univ
  have hk : MeasurePreserving (keysEquiv bits).symm
      (activeLaw.prod rankLaw) (uniformOn (Set.univ : Set (ι → Pair))) := by
    rw [show activeLaw.prod rankLaw = uniformOn Set.univ from prod_uniform_univ]
    exact FiniteProbability.uniform_equiv (keysEquiv bits).symm
  have hmap := hk.prod (MeasurePreserving.id context)
  let pulled : Set (((ι → Label) × (ι → Rank)) × X) :=
    (fun s => ((keysEquiv bits).symm s.1,s.2)) ⁻¹' event
  have hp : MeasurableSet pulled := hmap.measurable he
  have heq : ((activeLaw.prod rankLaw).prod context) pulled =
      ((uniformOn (Set.univ : Set (ι → Pair))).prod context) event :=
    hmap.measure_preimage he.nullMeasurableSet
  rw [← heq, Measure.prod_apply_symm hp]
  calc
    (∫⁻ x, (activeLaw.prod rankLaw) ((fun ar => (ar,x)) ⁻¹' pulled) ∂context) ≤
        ∫⁻ _ : X, error ∂context := by
      apply lintegral_mono
      intro x
      change (activeLaw.prod rankLaw) ((fun ar => (ar,x)) ⁻¹' pulled) ≤ error
      rw [Measure.prod_apply (μ := activeLaw) (ν := rankLaw) (measurable_prodMk_right hp)]
      calc
        (∫⁻ active, rankLaw (Prod.mk active ⁻¹' ((fun ar => (ar,x)) ⁻¹' pulled)) ∂activeLaw) ≤
            ∫⁻ _ : ι → Label, error ∂activeLaw := by
          apply lintegral_mono
          intro active
          exact hconditional active x
        _ = error := by simp [activeLaw]
    _ = error := by simp

end G1Release.Submission.ConditionalKeys
