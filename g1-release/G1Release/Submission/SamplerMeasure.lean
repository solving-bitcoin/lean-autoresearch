import G1Release.Submission.CoinLaw
import G1Release.Submission.EventBounds

namespace G1Release.Submission.SamplerMeasure
open SecretRelease G1Release.Protected Randomized MeasureTheory ProbabilityTheory

noncomputable def samplerLaw (n : Nat)
    (sampler : SecretRelease.Bytes n → (hidden : Hidden) → Randomness hidden) (hidden : Hidden) :
    Measure (Randomness hidden) :=
  (uniformOn (Set.univ : Set (SecretRelease.Bytes n))).map (fun coins => sampler coins hidden)

theorem sampler_preserving (n : Nat)
    (sampler : SecretRelease.Bytes n → (hidden : Hidden) → Randomness hidden) (hidden : Hidden) :
    MeasurePreserving (fun coins => sampler coins hidden)
      (uniformOn (Set.univ : Set (SecretRelease.Bytes n))) (samplerLaw n sampler hidden) :=
  ⟨Measurable.of_discrete,rfl⟩

instance (n : Nat) (sampler : SecretRelease.Bytes n → (hidden : Hidden) → Randomness hidden)
    (hidden : Hidden) : IsProbabilityMeasure (samplerLaw n sampler hidden) :=
  Measure.isProbabilityMeasure_map Measurable.of_discrete.aemeasurable

instance (hidden : Hidden) : IsProbabilityMeasure (idealLaw hidden) := by
  unfold idealLaw
  infer_instance

theorem samplingError_nonneg : 0 ≤ samplingError := by
  unfold samplingError
  positivity

theorem sampleLaw_close (hidden : Hidden) :
    EventBounds.Le (samplerLaw coinBytes sample hidden) (idealLaw hidden) (ENNReal.ofReal samplingError) ∧
      EventBounds.Le (idealLaw hidden) (samplerLaw coinBytes sample hidden) (ENNReal.ofReal samplingError) := by
  constructor
  · apply EventBounds.of_toReal _ _ samplingError samplingError_nonneg
    intro event hm
    rw [samplerLaw, Measure.map_apply Measurable.of_discrete hm]
    exact (sample_event_probability_bounds hidden event).1
  · apply EventBounds.of_toReal _ _ samplingError samplingError_nonneg
    intro event hm
    rw [samplerLaw, Measure.map_apply Measurable.of_discrete hm]
    exact (sample_event_probability_bounds hidden event).2

end G1Release.Submission.SamplerMeasure
