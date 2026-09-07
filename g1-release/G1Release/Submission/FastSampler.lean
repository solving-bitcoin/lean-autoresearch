import G1Release.Submission.FastGarble
import G1Release.Submission.FixedBase
import G1Release.Submission.FlatBlock

set_option exponentiation.threshold 1024
set_option maxRecDepth 4096
set_option maxHeartbeats 300000

namespace G1Release.Submission.FastSampler
open SecretRelease G1Release.Protected Randomized
open scoped BigOperators

theorem ofFn_get {α : Type} {n : Nat} (f : Fin n → α) : (Vector.ofFn f).get = f := by
  funext i
  simp only [Vector.get_ofFn]

/-- Store both the free entries and the completed mask vector as data.
The compiler cannot eta-expand a vector into a per-lookup sampler. -/
def maskValues (constant : Word) (free : Fin 253 → Word) : Vector Word 254 :=
  let values := Vector.ofFn free
  let final := constant - ∑ i, values.get i
  Vector.ofFn (Fin.lastCases final values.get)

theorem maskValues_get (constant : Word) (free : Fin 253 → Word) :
    (maskValues constant free).get = (tableMaskFromFree constant free).1 := by
  simp only [maskValues, ofFn_get, tableMaskFromFree]

def kindVector {α : Type} (f : ProjectiveMap.TableKind → α) : Vector α 11 :=
  Vector.ofFn fun i => f (ProjectiveMap.tableKindAt i)

theorem kindVector_get {α : Type} (f : ProjectiveMap.TableKind → α) (kind : ProjectiveMap.TableKind) :
    (kindVector f).get kind.finIndex = f kind := by
  simp only [kindVector, Vector.get_ofFn, ProjectiveMap.tableKindAt_finIndex]

def fromFree (hidden : Hidden) (free : FreeRandomness) : Randomness hidden :=
  let offsets := offsetsFromTail hidden free.offsets
  let scales := free.scales
  let chains := fun i => chainsFromFree (free.chains i)
  let masks := Vector.ofFn fun i : Fin 161 => kindVector fun kind =>
    maskValues ((mapHidden hidden offsets scales chains i).params kind).constant
      (free.tableMasks i kind)
  { offsets, scales, chains
    tableMasks := fun i kind => ((masks.get i).get kind.finIndex).get
    tableMasks_sum := by
      intro i kind
      dsimp only [masks]
      rw [Vector.get_ofFn, kindVector_get, maskValues_get]
      exact (tableMaskFromFree ((mapHidden hidden offsets scales chains i).params kind).constant
        (free.tableMasks i kind)).2 }

theorem fromFree_eq (hidden : Hidden) (free : FreeRandomness) :
    fromFree hidden free = randomnessFromFree hidden free := by
  simp only [fromFree, Vector.get_ofFn, kindVector_get, maskValues_get, randomnessFromFree]

def coordinates (coins : SecretRelease.Bytes coinBytes) : RawValues := fun c =>
  ModuloSampling.sample (2^512) (rawModulus c) (rawModulus_pos c)
    (FlatBlock.toFin coins ((coordinateSlot c).val*64) (by
      have hs := (coordinateSlot c).isLt
      dsimp only [coinBytes]
      omega))

theorem coordinates_eq (coins : SecretRelease.Bytes coinBytes) : coordinates coins = sampleCoordinates coins := by
  funext c
  exact congrArg (ModuloSampling.sample (2^512) (rawModulus c) (rawModulus_pos c))
    (FlatBlock.toFin_eq (count := coordinateCount) coins (coordinateSlot c))

/-- Reuse one fixed-base table for all 160 random point coordinates. -/
def freeValues (base : GarblingPrize.Protected.BN254.G1) (raw : RawValues) : FreeRandomness :=
  let tables := FixedBase.table base
  { offsets := offsetTailEquiv (fun i => FixedBase.multiply tables (raw (.offset i)).val)
    scales := fun i => unitFromFin (raw (.randomizer i))
    chains := fun i j => ((raw (.chain i j)).val : Word)
    tableMasks := fun i kind j => ((raw (.table i kind j)).val : Word) }

theorem freeValues_eq (raw : RawValues) :
    freeValues standardGenerator raw = freeFromValues raw := by
  have h (i : Fin 160) :
      FixedBase.multiply (FixedBase.table standardGenerator) (raw (.offset i)).val =
        (raw (.offset i)).val • standardGenerator :=
    FixedBase.multiply_eq standardGenerator (raw (.offset i))
  simp only [freeValues, freeFromValues, h]

def sample (coins : SecretRelease.Bytes coinBytes) (hidden : Hidden) : Randomness hidden :=
  fromFree hidden (freeValues standardGenerator (coordinates coins))

theorem sample_eq (coins : SecretRelease.Bytes coinBytes) (hidden : Hidden) :
    sample coins hidden = Randomized.sample coins hidden := by
  unfold sample
  rw [freeValues_eq, coordinates_eq]
  exact fromFree_eq _ _

end G1Release.Submission.FastSampler
