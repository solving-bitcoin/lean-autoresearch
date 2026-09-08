import Blake3Prize.Submission.RomMixedKeys

namespace Blake3Prize.Submission.RomMixedConditional
open SecretRelease MeasureTheory ProbabilityTheory RomMixedKeys RomLamportLaw

theorem bound {X : Type*} [MeasurableSpace X]
    (external : Fin e → Bool) (internal : Fin k → Bool)
    (context : Measure X) [IsProbabilityMeasure context]
    (event : Set (Keys e k × X)) (he : MeasurableSet event) (error : ENNReal)
    (hconditional : ∀ active x,
      uniformOn (Set.univ : Set (Ranks e k))
        {ranks | ((split external internal).symm (active,ranks),x) ∈ event} ≤ error) :
    ((uniformOn (Set.univ : Set (Keys e k))).prod context) event ≤ error := by
  let activeLaw : Measure (Active e k) := uniformOn Set.univ
  let rankLaw : Measure (Ranks e k) := uniformOn Set.univ
  have hk : MeasurePreserving (split external internal).symm
      (activeLaw.prod rankLaw) (uniformOn (Set.univ : Set (Keys e k))) := by
    rw [show activeLaw.prod rankLaw = uniformOn Set.univ from prod_uniform_univ]
    exact RomFiniteProbability.uniform_equiv (split external internal).symm
  have hmap := hk.prod (MeasurePreserving.id context)
  let pulled : Set ((Active e k × Ranks e k) × X) :=
    (fun s => ((split external internal).symm s.1,s.2)) ⁻¹' event
  have hp : MeasurableSet pulled := hmap.measurable he
  have heq : ((activeLaw.prod rankLaw).prod context) pulled =
      ((uniformOn (Set.univ : Set (Keys e k))).prod context) event :=
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
            ∫⁻ _ : Active e k, error ∂activeLaw := by
          apply lintegral_mono
          intro active
          exact hconditional active x
        _ = error := by simp [activeLaw]
    _ = error := by simp

end Blake3Prize.Submission.RomMixedConditional
