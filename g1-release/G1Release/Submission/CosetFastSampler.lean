import G1Release.Submission.CosetSampler
import G1Release.Submission.FixedBase

/-! Executable refinements of the finite-tape sampler. Reading 64-byte
blocks with machine words and sharing one fixed-base multiplication table
changes neither the sampled values nor their proved distribution. -/
namespace G1Release.Submission.CosetFastSampler
open SecretRelease G1Release.Protected G1Release.Math CosetSampler

def coordinates (coins : SecretRelease.Bytes coinBytes) : RawValues := fun c =>
  ModuloSampling.sample (2^512) (rawModulus c) (rawModulus_pos c)
    (FlatBlock.toFin coins ((coordinateSlot c).val*64) (by
      have hs := (coordinateSlot c).isLt
      dsimp only [coinBytes]
      omega))

theorem coordinates_eq (coins : SecretRelease.Bytes coinBytes) :
    coordinates coins = sampleCoordinates coins := by
  funext c
  exact congrArg (ModuloSampling.sample (2^512) (rawModulus c) (rawModulus_pos c))
    (FlatBlock.toFin_eq (count := coordinateCount) coins (coordinateSlot c))

def coreFromSamples (hidden : Private) (samples : CosetRandomness.Samples) :
    CosetRandomness.Randomness hidden :=
  let table := FixedBase.table Randomized.standardGenerator
  { offsets := GLVSampling.offsetsFromTail hidden
      ⟨List.ofFn (fun i => FixedBase.multiply table (samples.1 i).val),List.length_ofFn⟩
    states := fun i => (CosetFieldSampling.unitFromSamples (samples.2 i).1,
      CosetRandomness.masksFromSamples (samples.2 i).2) }

theorem coreFromSamples_eq (hidden : Private) (samples : CosetRandomness.Samples) :
    coreFromSamples hidden samples = CosetRandomness.randomnessFromSamples hidden samples := by
  have h (i : Fin 90) : FixedBase.multiply (FixedBase.table Randomized.standardGenerator)
      (samples.1 i).val = (samples.1 i).val • Randomized.standardGenerator :=
    FixedBase.multiply_eq Randomized.standardGenerator (samples.1 i)
  simp only [coreFromSamples, CosetRandomness.randomnessFromSamples, h]

def sample (coins : SecretRelease.Bytes coinBytes) (hidden : Private) : Randomness hidden :=
  let values := samplesFromRaw (coordinates coins)
  (coreFromSamples hidden values.1, values.2)

theorem sample_eq (coins : SecretRelease.Bytes coinBytes) (hidden : Private) :
    sample coins hidden = CosetSampler.sample coins hidden := by
  unfold sample
  rw [coordinates_eq]
  dsimp only
  rw [coreFromSamples_eq]
  rfl

def scheme : SecretRelease.Scheme challenge := CosetScheme.scheme coinBytes sample

theorem scheme_eq : scheme = CosetSampler.scheme := by
  have h : sample = CosetSampler.sample := by funext coins hidden; exact sample_eq coins hidden
  unfold scheme CosetSampler.scheme
  rw [h]

end G1Release.Submission.CosetFastSampler
