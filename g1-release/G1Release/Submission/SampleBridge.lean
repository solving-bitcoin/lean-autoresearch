import G1Release.Submission.ReleaseReduction
import G1Release.Submission.SamplerMeasure

set_option maxRecDepth 4096
set_option maxHeartbeats 300000

namespace G1Release.Submission.SampleBridge
open SecretRelease G1Release.Protected Randomized GameLaw SamplerMeasure
open MeasureTheory ProbabilityTheory

local instance : MeasurableSpace Keys := ⊤
local instance : MeasurableSpace challenge.inputs.Keys := ⊤
local instance : MeasurableSpace challenge.outputs.Keys := ⊤

variable (n : Nat) (sampler : SecretRelease.Bytes n → (hidden : Hidden) → Randomness hidden)

def state (hidden : Hidden) (ω : ROM.Sample (scheme n sampler)) : RealState hidden :=
  (ω.1, sampler ω.2.2.1 hidden, ω.2.2.2)

theorem preserving (hidden : Hidden) :
    MeasurePreserving (state n sampler hidden) (ROM.law (scheme n sampler))
      (realLaw hidden (samplerLaw n sampler hidden)) := by
  have hs := (sampler_preserving n sampler hidden).prod
    (MeasurePreserving.id (OracleLaw.law (List (Fin 256))))
  have hd : MeasurePreserving
      (Prod.snd : challenge.outputs.Keys × SecretRelease.Bytes n × ROM.Oracle → _)
      ((uniformOn (Set.univ : Set challenge.outputs.Keys)).prod
        ((uniformOn (Set.univ : Set (SecretRelease.Bytes n))).prod (OracleLaw.law (List (Fin 256)))))
      ((uniformOn (Set.univ : Set (SecretRelease.Bytes n))).prod (OracleLaw.law (List (Fin 256)))) :=
    measurePreserving_snd
  exact (MeasurePreserving.id (uniformOn (Set.univ : Set challenge.inputs.Keys))).prod (hs.comp hd)

theorem outcome_eq (hidden : Hidden) (input : Input) (adversary : View challenge → Program α)
    (ω : ROM.Sample (scheme n sampler)) :
    ROM.run (ROM.hash ω.2.2.2) (adversary (ROM.view (scheme n sampler) hidden input ω)) =
      realOutcome hidden input adversary (state n sampler hidden ω) := rfl

theorem winEvent_eq (hidden : Hidden) (input : Input)
    (adversary : View challenge → Program challenge.Claim) :
    ROM.winEvent (scheme n sampler) hidden input adversary =
      state n sampler hidden ⁻¹' realWin hidden input adversary := rfl

theorem distinguishEvent_eq (hidden : Hidden) (input : Input)
    (adversary : View challenge → Program Bool) :
    ROM.distinguishEvent (scheme n sampler) hidden input adversary =
      state n sampler hidden ⁻¹' realDistinguish hidden input adversary := rfl

theorem win_measurable (hidden : Hidden) (input : Input)
    (adversary : View challenge → Program challenge.Claim) :
    MeasurableSet (ROM.winEvent (scheme n sampler) hidden input adversary) := by
  rw [winEvent_eq]
  exact (preserving n sampler hidden).measurable (realWin_measurable hidden input adversary)

theorem distinguish_measurable (hidden : Hidden) (input : Input)
    (adversary : View challenge → Program Bool) :
    MeasurableSet (ROM.distinguishEvent (scheme n sampler) hidden input adversary) := by
  rw [distinguishEvent_eq]
  exact (preserving n sampler hidden).measurable (realDistinguish_measurable hidden input adversary)

theorem win_probability_eq (hidden : Hidden) (input : Input)
    (adversary : View challenge → Program challenge.Claim) :
    ROM.law (scheme n sampler) (ROM.winEvent (scheme n sampler) hidden input adversary) =
      realLaw hidden (samplerLaw n sampler hidden) (realWin hidden input adversary) := by
  rw [winEvent_eq]
  exact (preserving n sampler hidden).measure_preimage (realWin_measurable hidden input adversary).nullMeasurableSet

theorem distinguish_probability_eq (hidden : Hidden) (input : Input)
    (adversary : View challenge → Program Bool) :
    ROM.law (scheme n sampler) (ROM.distinguishEvent (scheme n sampler) hidden input adversary) =
      realLaw hidden (samplerLaw n sampler hidden) (realDistinguish hidden input adversary) := by
  rw [distinguishEvent_eq]
  exact (preserving n sampler hidden).measure_preimage
    (realDistinguish_measurable hidden input adversary).nullMeasurableSet

end G1Release.Submission.SampleBridge
