import G1Release.Submission.ReferenceFacts
import G1Release.Submission.DutyFreeSampleBridge
import G1Release.Submission.DutyFreeFunctionReduction
import G1Release.Submission.DutyFreeNumericBounds

/-! The direct-field nibble construction uses the unchanged shared contract:
correctness, exact serialization, opposite-label security, and equal-output
function privacy in the bounded-query ROM. No new assumption is introduced. -/
namespace G1Release.Submission.DutyFreeCertified
open SecretRelease G1Release.Protected
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

local instance : MeasurableSpace DutyFreeSlots.Keys := ⊤
local instance : MeasurableSpace challenge.inputs.Keys := ⊤
local instance : MeasurableSpace challenge.outputs.Keys := ⊤

theorem releaseSecure : ROM.ReleaseSecure DutyFreeSampler.scheme := by
  intro hidden input q _ adversary ha
  letI : MeasureTheory.IsProbabilityMeasure (DutyFreeSampleBridge.samplerLaw hidden) :=
    CosetSamplerMeasure.instIsProbabilityMeasureRandomnessSamplerLaw
      CosetSampler.coinBytes CosetSampler.sample hidden
  refine ⟨DutyFreeSampleBridge.win_measurable hidden input adversary, ?_⟩
  exact (DutyFreeSampleBridge.win_probability_eq hidden input adversary).trans_le
    ((DutyFreeReleaseReduction.realWin_probability_le hidden input
      (DutyFreeSampleBridge.samplerLaw hidden) adversary q ha).trans (CosetNumericBounds.release_le q))

private theorem function_bound (source target : Private) (input : Input)
    (hequal : GLVOffsetFamily.mapAt source input = GLVOffsetFamily.mapAt target input)
    (href : reference source input = reference target input)
    (adversary : View challenge → Program Bool) (q : Nat) (ha : ROM.Bounded adversary q) :
    ROM.law DutyFreeSampler.scheme (ROM.distinguishEvent DutyFreeSampler.scheme source input adversary) ≤
      ROM.law DutyFreeSampler.scheme (ROM.distinguishEvent DutyFreeSampler.scheme target input adversary) +
        (challenge.rom.error q : ENNReal) := by
  rw [DutyFreeSampleBridge.distinguish_probability_eq, DutyFreeSampleBridge.distinguish_probability_eq]
  exact (DutyFreeFunctionReduction.probability_le source target input hequal href adversary q ha).trans
    (add_le_add le_rfl (DutyFreeNumericBounds.function_le q))

theorem functionPrivate : ROM.FunctionPrivate DutyFreeSampler.scheme := by
  intro leakage hleak source target input hequal q _ adversary ha
  have hl : (fun p a => encodeOutput (reference p a)) = leakage := Option.some.inj hleak
  have he : encodeOutput (reference source input) = encodeOutput (reference target input) :=
    (congrFun (congrFun hl source) input).trans
      (hequal.trans (congrFun (congrFun hl target) input).symm)
  exact ⟨DutyFreeSampleBridge.distinguish_measurable source input adversary,
    function_bound source target input ((same_leakage_iff source target input).mp he)
      (encodeOutput_injective he) adversary q ha⟩

def certificate : SecretRelease.Certificate DutyFreeSampler.scheme 1776384 where
  correct := DutyFreeSampler.correct
  decode_encode := DutyFreeArtifact.decode_encode
  encode_decode := fun _ _ h => DutyFreeArtifact.encode_decode h
  artifactBound := DutyFreeSampler.artifactBound
  releaseSecure := releaseSecure
  withholdingSecure := True.intro
  functionPrivate := functionPrivate

def entry : SecretRelease.Candidate challenge where
  scheme := DutyFreeSampler.scheme
  maxBytes := 1776384
  certificate := some certificate

end G1Release.Submission.DutyFreeCertified
