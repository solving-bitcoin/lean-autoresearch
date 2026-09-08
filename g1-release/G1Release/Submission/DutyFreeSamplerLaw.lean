import G1Release.Submission.DutyFreeSampler
import G1Release.Submission.CosetSamplerMeasure
import G1Release.Submission.LamportLaw

/-! The private coin tape splits exactly into the existing coset sampler
and independent uniform bridge keys. Keeping the unused legacy row coins
in the proof space allows reuse of the already checked sampling bound. -/
namespace G1Release.Submission.DutyFreeSamplerLaw
open SecretRelease G1Release.Protected MeasureTheory ProbabilityTheory
open DutyFreeSampler

abbrev FullRandomness (hidden : Private) := CosetSampler.Randomness hidden × DutyFreeProgram.HotKeys

def fullSample (coins : Bytes coinBytes) (hidden : Private) : FullRandomness hidden :=
  let parts := split CosetSampler.coinBytes 65536 coins
  (CosetSampler.sample parts.1 hidden,hotEquiv parts.2)

theorem sample_projection (coins : Bytes coinBytes) (hidden : Private) :
    sample coins hidden = ((fullSample coins hidden).1.1,(fullSample coins hidden).2) := by
  simp only [sample, fullSample, CosetFastSampler.sample_eq, hotStorage, Vector.get_ofFn]

noncomputable def law (hidden : Private) : Measure (FullRandomness hidden) :=
  (CosetSamplerMeasure.samplerLaw CosetSampler.coinBytes CosetSampler.sample hidden).prod
    (uniformOn Set.univ)

noncomputable def idealLaw (hidden : Private) : Measure (FullRandomness hidden) :=
  (CosetSampler.idealLaw hidden).prod (uniformOn Set.univ)

theorem preserving (hidden : Private) :
    MeasurePreserving (fun coins => fullSample coins hidden) (uniformOn Set.univ) (law hidden) := by
  have hs : MeasurePreserving (splitEquiv CosetSampler.coinBytes 65536)
      (uniformOn Set.univ)
      ((uniformOn (Set.univ : Set (Bytes CosetSampler.coinBytes))).prod
        (uniformOn (Set.univ : Set (Bytes 65536)))) := by
    rw [LamportLaw.prod_uniform_univ]
    exact FiniteProbability.uniform_equiv (splitEquiv CosetSampler.coinBytes 65536)
  have hm := (CosetSamplerMeasure.sampler_preserving CosetSampler.coinBytes CosetSampler.sample hidden).prod
    (FiniteProbability.uniform_equiv hotEquiv)
  exact hm.comp hs

theorem law_close (hidden : Private) :
    EventBounds.Le (law hidden) (idealLaw hidden) (ENNReal.ofReal CosetSampler.samplingError) ∧
      EventBounds.Le (idealLaw hidden) (law hidden) (ENNReal.ofReal CosetSampler.samplingError) := by
  constructor
  · exact EventBounds.prod_right (CosetSamplerMeasure.sampleLaw_close hidden).1 (uniformOn Set.univ)
  · exact EventBounds.prod_right (CosetSamplerMeasure.sampleLaw_close hidden).2 (uniformOn Set.univ)

end G1Release.Submission.DutyFreeSamplerLaw
