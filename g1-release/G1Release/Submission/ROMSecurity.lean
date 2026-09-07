import G1Release.Submission.ReferenceFacts
import G1Release.Submission.SampleBridge
import G1Release.Submission.FunctionReduction
import G1Release.Submission.NumericBounds

set_option maxRecDepth 4096
set_option maxHeartbeats 300000

namespace G1Release.Submission.ROMSecurity
open SecretRelease G1Release.Protected Randomized SamplerMeasure
open MeasureTheory

local instance : MeasurableSpace GameLaw.Keys := ⊤
local instance : MeasurableSpace challenge.inputs.Keys := ⊤
local instance : MeasurableSpace challenge.outputs.Keys := ⊤

private theorem release_bound (n : Nat)
    (sampler : SecretRelease.Bytes n → (hidden : Hidden) → Randomness hidden)
    (hidden : Hidden) (input : Input) (q : Nat)
    (adversary : View challenge → Program challenge.Claim) (ha : ROM.Bounded adversary q) :
    ROM.law (scheme n sampler) (ROM.winEvent (scheme n sampler) hidden input adversary) ≤
      (challenge.rom.error q : ENNReal) :=
  (SampleBridge.win_probability_eq n sampler hidden input adversary).le.trans
    ((ReleaseReduction.realWin_probability_le hidden input (samplerLaw n sampler hidden)
      adversary q ha).trans (NumericBounds.release_le q))

/-- The release reduction holds for every independent byte-tape sampler. -/
theorem releaseSecure (n : Nat)
    (sampler : SecretRelease.Bytes n → (hidden : Hidden) → Randomness hidden) :
    ROM.ReleaseSecure (scheme n sampler) :=
  fun hidden input q _ adversary ha =>
    ⟨SampleBridge.win_measurable n sampler hidden input adversary,
      release_bound n sampler hidden input q adversary ha⟩

private theorem function_bound (source target : Hidden) (input : Input)
    (hequal : OffsetFamily.mapAt source input = OffsetFamily.mapAt target input)
    (href : reference source input = reference target input)
    (adversary : View challenge → Program Bool) (q : Nat) (ha : ROM.Bounded adversary q) :
    ROM.law executableScheme (ROM.distinguishEvent executableScheme source input adversary) ≤
      ROM.law executableScheme (ROM.distinguishEvent executableScheme target input adversary) +
        (challenge.rom.error q : ENNReal) := by
  have hs := SampleBridge.distinguish_probability_eq coinBytes sample source input adversary
  have ht := SampleBridge.distinguish_probability_eq coinBytes sample target input adversary
  have hm := FunctionReduction.probability_le source target input hequal href adversary q ha
  exact hs.le.trans (hm.trans (add_le_add ht.symm.le (NumericBounds.function_le q)))

/-- Equal authorized plaintext outputs give the required privacy inequality,
including the explicit finite-tape sampling error. -/
theorem functionPrivate : ROM.FunctionPrivate executableScheme := by
  intro leakage hleak source target input hequal q _ adversary ha
  have hl : (fun p a => encodeOutput (reference p a)) = leakage := Option.some.inj hleak
  have he : encodeOutput (reference source input) = encodeOutput (reference target input) := by
    exact (congrFun (congrFun hl source) input).trans
      (hequal.trans (congrFun (congrFun hl target) input).symm)
  exact ⟨SampleBridge.distinguish_measurable coinBytes sample source input adversary,
    function_bound source target input ((same_leakage_iff source target input).mp he)
      (encodeOutput_injective he) adversary q ha⟩

def certificate : SecretRelease.Certificate executableScheme Scheme.claimedBytes where
  correct := executable_correct
  decode_encode := Scheme.decode_encode
  encode_decode := fun _ _ h => Scheme.encode_decode h
  artifactBound := artifactBound coinBytes sample
  releaseSecure := releaseSecure coinBytes sample
  withholdingSecure := True.intro
  functionPrivate := functionPrivate

end G1Release.Submission.ROMSecurity
