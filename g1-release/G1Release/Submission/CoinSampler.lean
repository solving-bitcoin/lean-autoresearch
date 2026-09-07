import G1Release.Submission.RandomCoordinates
import G1Release.Submission.ModuloSampling

/-! Total executable sampler. Private coins are consumed directly; expanding
a short seed is deliberately not an unproved extra cryptographic step. The
modulo-sampling approximation remains an explicit probability obligation. -/
namespace G1Release.Submission.Randomized
open GarblingPrize.Protected G1Release.Protected SecretRelease

def coordinateCount : Nat := 449672
def coinBytes : Nat := coordinateCount * 64

theorem coordinateIndex_lt (c : OracleCoordinate) : coordinateIndex c < coordinateCount := by
  cases c with
  | offset i => simp [coordinateIndex, coordinateCount]; omega
  | randomizer i => simp [coordinateIndex, coordinateCount]; omega
  | chain i j => simp [coordinateIndex, coordinateCount]; omega
  | table i kind j =>
    have hk : kind.index < 11 := by cases kind <;> decide
    simp only [coordinateIndex, coordinateCount]
    omega

def coordinateSlot (c : OracleCoordinate) : Fin coordinateCount :=
  ⟨coordinateIndex c, coordinateIndex_lt c⟩

theorem coordinateSlot_injective : Function.Injective coordinateSlot := by
  intro a b h
  exact coordinateIndex_injective (congrArg Fin.val h)

def sampleCoordinates (coins : SecretRelease.Bytes coinBytes) : RawValues := fun c =>
  let block := FiniteProbability.blockEquiv coordinateCount 64 coins (coordinateSlot c)
  ModuloSampling.sample (2^512) (rawModulus c) (rawModulus_pos c)
    (FiniteProbability.bytesFinEquiv 64 block)

def unitFromFin (value : Fin (baseFieldModulus - 1)) : Wordˣ :=
  Units.mk0 ((value.val + 1 : Nat) : Word) (by
    intro hzero
    have hdvd : baseFieldModulus ∣ value.val + 1 :=
      (ZMod.natCast_eq_zero_iff _ _).mp hzero
    have hle := Nat.le_of_dvd (by omega : 0 < value.val + 1) hdvd
    omega)

/-- The executable forward map uses scalar multiplication, never the
noncomputable discrete-log inverse appearing in the distributional proof. -/
def freeFromValues (raw : RawValues) : FreeRandomness where
  offsets := offsetTailEquiv (fun i => (raw (.offset i)).val • standardGenerator)
  scales := fun i => unitFromFin (raw (.randomizer i))
  chains := fun i j => ((raw (.chain i j)).val : Word)
  tableMasks := fun i kind j => ((raw (.table i kind j)).val : Word)

theorem freeFromValues_eq (raw : RawValues) : freeFromValues raw = freeFromRaw raw := by
  rfl

def sample (coins : SecretRelease.Bytes coinBytes) (hidden : Hidden) : Randomness hidden :=
  randomnessFromFree hidden (freeFromValues (sampleCoordinates coins))

theorem sample_eq (coins : SecretRelease.Bytes coinBytes) (hidden : Hidden) :
    sample coins hidden = rawRandomnessEquiv hidden (sampleCoordinates coins) := by
  rw [sample, freeFromValues_eq]
  rfl

def executableScheme : SecretRelease.Scheme challenge := scheme coinBytes sample

theorem executable_correct : Correct executableScheme := correct coinBytes sample

theorem executable_artifactBound : ArtifactBound executableScheme Scheme.claimedBytes :=
  artifactBound coinBytes sample

end G1Release.Submission.Randomized
