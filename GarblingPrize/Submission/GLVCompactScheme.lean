import GarblingPrize.Submission.GLVFamilyArtifact
import GarblingPrize.Submission.GLVOffsetFamily
import GarblingPrize.Submission.GLVProjectiveMapPrivacy
import GarblingPrize.Submission.GLVProjectiveMapRuntime
import GarblingPrize.Submission.RuntimeG1GLV

namespace GarblingPrize.Submission.GLVCompactScheme

/-!
# Norm-seven GLV garbling and exact size

The exported construction uses **16,145,129 bytes**, down from the
28,564,459-byte balanced ternary baseline: **12,419,330 bytes saved (43.48%)**.

## Scalar representation

The checked BN254 endomorphism is `phi(x,y) = (beta*x,y)`, with `beta^3 = 1`.
The generator certificate and prime group cardinality prove that `phi`
acts as multiplication by the scalar eigenvalue `lambda` on every G1 point.
Thus the Eisenstein unit `omega` can be evaluated as `phi`.

In the Eisenstein integers, `omega^2 + omega + 1 = 0`, and the radix
`alpha = 3 + omega` has norm `3^2 - 3 + 1 = 7`. The existing reduction and
termination proofs represent every protected scalar with exactly 91 digits
in `{0, ±1, ±omega, ±omega^2}`. Horner evaluation multiplies a point by the
radix using `3*P + phi(P)`.

## Maps and privacy

Each map produces a randomized projective representative of `offset_i + d_i*A`.
Choose 90 independent uniform G1 offsets and solve the first offset so that
their radix-weighted sum is `Q`. Recomposing the 91 map outputs then gives
`Q + r*A` for all protected inputs, including infinity outputs.

The GLV polynomial substitution and eleven-table factorization already have
checked semantics and a privacy change of variables. This submission connects
that construction to the current protected `InternalOracle` contract:

- Each free scalar, nonzero randomizer, chain mask, and table mask uses a
  distinct typed oracle address.
- The standard generator bijects scalar samples with G1. Solving the first
  offset and each final table mask bijects free samples with the constraint
  fibers, proving the exact joint randomness law.
- The existing offset, projective-randomizer, chain-mask, and unused-label-pad
  transformations preserve the artifact bytes and active labels. Pushing the
  derived law through this transformation proves equality of complete public
  view distributions whenever the hidden functions agree at the selected input.

## Exact size and execution

There are 11 affine tables per map. Each table has 254 rows; a pair of rows
contains four 254-bit ciphertexts and occupies exactly 127 bytes. Therefore:

```text
91 maps * 11 tables * 127 row pairs * 127 bytes = 16,145,129 bytes
(161 - 91) maps * 177,419 bytes/map = 12,419,330 bytes saved
```

The codec proves both round trips and rejects truncation and trailing bytes.
Array materialization and the parallel encoder have equality proofs tying
native execution to the same logical artifact. `Solution.validClaimed`
exports the protected `ValidCandidate` theorem for this exact byte bound.
-/

open GarblingPrize.Protected
open GarblingPrize.Submission.EisensteinRadix

abbrev Profile := BN254.bn254
abbrev Hidden := HiddenInput Profile
abbrev Input := AffineInput Profile
abbrev Word := BN254.Fq
abbrev Point := RuntimeG1.Point
abbrev Artifact := GLVFamilyArtifact.Artifact 91

local instance concreteGroup : AddCommGroup BN254.G1 :=
  BN254.bn254.addCommGroup
local instance profileGroup : AddCommGroup Profile.G1 :=
  concreteGroup

def runtimeOfGroup : BN254.G1 → Point
  | .zero => RuntimeG1.infinity
  | @WeierstrassCurve.Affine.Point.some _ _ _ x y h =>
      RuntimeG1.ofAffine ⟨x, y⟩ (by
        have hequation :=
          (BN254.curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero
            BN254.discriminant_ne_zero).mpr h
        rw [WeierstrassCurve.Affine.equation_iff] at hequation
        simpa [HomogeneousRCBG1GroupLaw.AffineOnCurve, BN254.curve] using
          hequation.symm)

@[simp] theorem toPoint_runtimeOfGroup (point : BN254.G1) :
    RuntimeG1.toPoint (runtimeOfGroup point) = point := by
  cases point <;> rfl

def inputAffine (input : Input) : HomogeneousRCBG1GroupLaw.Affine :=
  ⟨(input.x.val : Word), (input.y.val : Word)⟩

theorem inputAffine_onCurve (input : Input) :
    HomogeneousRCBG1GroupLaw.AffineOnCurve (inputAffine input) := by
  change (input.x.val : Word) ^ 3 + 3 = (input.y.val : Word) ^ 2
  exact input.onCurve.symm

def inputRuntime (input : Input) : Point :=
  RuntimeG1.ofAffine (inputAffine input) (inputAffine_onCurve input)

def inputG1 (input : Input) : BN254.G1 :=
  BN254.ofAffine input.x input.y input.onCurve

@[simp] theorem toPoint_inputRuntime (input : Input) :
    RuntimeG1.toPoint (inputRuntime input) = inputG1 input := by
  rfl

theorem inputPoint_eq (input : Input) : input.point = inputG1 input := rfl

def digitSelector : Digit → Bool
  | .zero => false
  | _ => true

def digitSign : Digit → HomogeneousRCB.Sign
  | .negOne | .negOmega | .negOmegaSq => .negative
  | _ => .positive

def digitScale : Digit → Word
  | .zero | .one | .negOne => 1
  | .omega | .negOmega => G1Endomorphism.beta
  | .omegaSq | .negOmegaSq => G1Endomorphism.beta ^ 2

theorem digitScale_cube (digit : Digit) : digitScale digit ^ 3 = 1 := by
  cases digit <;> simp [digitScale]
  all_goals
    calc
      G1Endomorphism.beta ^ 6 =
          (G1Endomorphism.beta ^ 3) ^ 2 := by ring
      _ = 1 := by rw [G1Endomorphism.beta_pow_three]; norm_num

def digitAffine (digit : Digit) (input : Input) :
    HomogeneousRCBG1GroupLaw.Affine :=
  ⟨digitScale digit * (input.x.val : Word), (input.y.val : Word)⟩

theorem digitAffine_onCurve (digit : Digit) (input : Input) :
    HomogeneousRCBG1GroupLaw.AffineOnCurve (digitAffine digit input) := by
  change (digitScale digit * (input.x.val : Word)) ^ 3 + 3 =
    (input.y.val : Word) ^ 2
  rw [mul_pow, digitScale_cube, one_mul]
  exact inputAffine_onCurve input

def digitBaseRuntime (digit : Digit) (input : Input) : Point :=
  RuntimeG1.ofAffine (digitAffine digit input) (digitAffine_onCurve digit input)

def digitBasePoint (digit : Digit) (point : BN254.G1) : BN254.G1 :=
  match digit with
  | .zero | .one | .negOne => point
  | .omega | .negOmega => G1Endomorphism.phi point
  | .omegaSq | .negOmegaSq =>
      G1Endomorphism.phi (G1Endomorphism.phi point)

theorem toPoint_digitBaseRuntime (digit : Digit) (input : Input) :
    RuntimeG1.toPoint (digitBaseRuntime digit input) =
      digitBasePoint digit (inputG1 input) := by
  cases digit <;>
    simp [digitBaseRuntime, digitBasePoint, digitAffine, digitScale,
      RuntimeG1.toPoint, RuntimeG1.ofAffine, inputG1, BN254.ofAffine,
      G1Endomorphism.phi] <;> ring

def digitRuntime (digit : Digit) (input : Input) : Point :=
  match digit with
  | .negOne | .negOmega | .negOmegaSq =>
      RuntimeG1.ofAffine (HomogeneousRCBG1GroupLaw.negAffine
        (digitAffine digit input))
        (HomogeneousRCBG1GroupLaw.negAffine_onCurve (digitAffine digit input)
          (digitAffine_onCurve digit input))
  | .zero => RuntimeG1.infinity
  | _ => digitBaseRuntime digit input

theorem selectedInput_eq_digitRuntime (digit : Digit) (input : Input) :
    HomogeneousRCB.selectedInput (digitSelector digit) (digitSign digit)
        (RuntimeG1.encode (digitBaseRuntime digit input)) =
      RuntimeG1.encode (digitRuntime digit input) := by
  cases digit with
  | zero =>
      simpa [digitSelector, digitSign, digitRuntime, digitBaseRuntime,
        RuntimeG1.encode, RuntimeG1.ofAffine, RuntimeG1.infinity] using
        HomogeneousRCBG1GroupLaw.selectedInput_positive_eq_encode false
          (digitAffine .zero input)
  | negOne =>
      simpa [digitSelector, digitSign, digitRuntime, inputRuntime,
        digitBaseRuntime, RuntimeG1.encode, RuntimeG1.ofAffine] using
        HomogeneousRCBG1GroupLaw.selectedInput_negative_eq_encode true
          (digitAffine .negOne input)
  | negOmega =>
      simpa [digitSelector, digitSign, digitRuntime, digitBaseRuntime,
        RuntimeG1.encode, RuntimeG1.ofAffine] using
        HomogeneousRCBG1GroupLaw.selectedInput_negative_eq_encode true
          (digitAffine .negOmega input)
  | negOmegaSq =>
      simpa [digitSelector, digitSign, digitRuntime, digitBaseRuntime,
        RuntimeG1.encode, RuntimeG1.ofAffine] using
        HomogeneousRCBG1GroupLaw.selectedInput_negative_eq_encode true
          (digitAffine .negOmegaSq input)
  | one =>
      simpa [digitSelector, digitSign, digitRuntime, RuntimeG1.encode,
        digitBaseRuntime, RuntimeG1.ofAffine] using
        HomogeneousRCBG1GroupLaw.selectedInput_positive_eq_encode true
          (digitAffine .one input)
  | omega =>
      simpa [digitSelector, digitSign, digitRuntime, RuntimeG1.encode,
        digitBaseRuntime, RuntimeG1.ofAffine] using
        HomogeneousRCBG1GroupLaw.selectedInput_positive_eq_encode true
          (digitAffine .omega input)
  | omegaSq =>
      simpa [digitSelector, digitSign, digitRuntime, RuntimeG1.encode,
        digitBaseRuntime, RuntimeG1.ofAffine] using
        HomogeneousRCBG1GroupLaw.selectedInput_positive_eq_encode true
          (digitAffine .omegaSq input)

def curveC : Word := ProjectiveMap.curveC

def rawMap (offset : BN254.G1) (digit : Digit) (input : Input) :
    HomogeneousRCB.Point Word :=
  HomogeneousRCB.formula curveC
    (RuntimeG1.encode (runtimeOfGroup offset))
    (HomogeneousRCB.selectedInput (digitSelector digit) (digitSign digit)
      (RuntimeG1.encode (digitBaseRuntime digit input)))

def rawBaseCoefficients (offset : BN254.G1) (digit : Digit) :
    ProjectiveMap.Coefficients Word :=
  ProjectiveMap.coefficients curveC
    (RuntimeG1.encode (runtimeOfGroup offset))
    (digitSelector digit) (digitSign digit)

def rawCoefficients (offset : BN254.G1) (digit : Digit) :
    ProjectiveMap.Coefficients Word :=
  GLVProjectiveMap.substituteX (digitScale digit)
    (rawBaseCoefficients offset digit)

def randomizedCoefficients (offset : BN254.G1) (digit : Digit)
    (randomizer : Wordˣ) : ProjectiveMap.Coefficients Word :=
  (rawCoefficients offset digit).scale (randomizer : Word)

theorem polynomial_randomizedCoefficients (offset : BN254.G1)
    (digit : Digit) (randomizer : Wordˣ) (input : Input) :
    ProjectiveMap.polynomial
        (randomizedCoefficients offset digit randomizer)
        (input.x.val : Word) (input.y.val : Word) =
      ProjectiveMap.Coordinates.ofHomogeneous
        (HomogeneousRCB.randomize (randomizer : Word)
          (rawMap offset digit input)) := by
  rw [randomizedCoefficients, ProjectiveMap.polynomial_scale,
    rawCoefficients, GLVProjectiveMap.polynomial_substituteX]
  rw [show ProjectiveMap.polynomial (rawBaseCoefficients offset digit)
      (digitScale digit * (input.x.val : Word)) (input.y.val : Word) =
        ProjectiveMap.Coordinates.ofHomogeneous (rawMap offset digit input) by
    exact ProjectiveMap.polynomial_coefficients curveC
      (RuntimeG1.encode (runtimeOfGroup offset))
      (digitSelector digit) (digitSign digit)
      (digitScale digit * (input.x.val : Word)) (input.y.val : Word)]
  rfl

def getFixed (values : List α) (length_eq : values.length = count)
    (index : Fin count) : α :=
  values.get ⟨index.val, by rw [length_eq]; exact index.isLt⟩

theorem map_getFixed_finRange (values : List α)
    (length_eq : values.length = count) :
    (List.finRange count).map (getFixed values length_eq) = values := by
  subst count
  have canonical :
      (List.finRange values.length).map (getFixed values rfl) = values := by
    rw [show getFixed values rfl = values.get by
      funext index
      unfold getFixed
      congr]
    exact List.map_get_finRange values
  exact canonical

def offsetAt {hidden : Hidden} (offsets : GLVOffsetFamily.Fiber hidden)
    (index : Fin 91) : BN254.G1 :=
  getFixed offsets.values offsets.length_eq index

def digitAt (hidden : Hidden) (index : Fin 91) : Digit :=
  getFixed (GLVOffsetFamily.digits hidden)
    (GLVOffsetFamily.digits_length hidden) index

def mapHidden (hidden : Hidden) (offsets : GLVOffsetFamily.Fiber hidden)
    (randomizers : Fin 91 → Wordˣ)
    (chainMasks : Fin 91 → GLVProjectiveMap.ChainMasks)
    (index : Fin 91) : GLVProjectiveMap.Hidden where
  coefficients := randomizedCoefficients (offsetAt offsets index)
    (digitAt hidden index) (randomizers index)
  chainMasks := chainMasks index

/-- Array-backed executable family of map secrets.  `offsetAt` indexes a list,
and `digitAt` both rebuilds and indexes the 91-digit decomposition.  Calling
those accessors independently for every map is quadratic in the map count.
Materializing the two already-fixed-width lists once preserves the exact
proof-level map while making each lookup constant time. -/
def materializedMapHiddenFamily (hidden : Hidden)
    (offsets : GLVOffsetFamily.Fiber hidden)
    (randomizers : Fin 91 → Wordˣ)
    (chainMasks : Fin 91 → GLVProjectiveMap.ChainMasks) :
    Fin 91 → GLVProjectiveMap.Hidden :=
  let offsetValues : List BN254.G1 := offsets.values
  let packedOffsets : Vector BN254.G1 91 :=
    ⟨offsetValues.toArray, by
      exact offsetValues.size_toArray.trans offsets.length_eq⟩
  let digits := GLVOffsetFamily.digits hidden
  let packedDigits : Vector Digit 91 :=
    ⟨digits.toArray, by
      exact digits.size_toArray.trans (GLVOffsetFamily.digits_length hidden)⟩
  fun index =>
    { coefficients := randomizedCoefficients packedOffsets[index.val]
        packedDigits[index.val] (randomizers index)
      chainMasks := chainMasks index }

@[simp] theorem materializedMapHiddenFamily_apply (hidden : Hidden)
    (offsets : GLVOffsetFamily.Fiber hidden)
    (randomizers : Fin 91 → Wordˣ)
    (chainMasks : Fin 91 → GLVProjectiveMap.ChainMasks)
    (index : Fin 91) :
    materializedMapHiddenFamily hidden offsets randomizers chainMasks index =
      mapHidden hidden offsets randomizers chainMasks index := by
  unfold materializedMapHiddenFamily mapHidden offsetAt digitAt getFixed
  apply GLVProjectiveMap.Hidden.ext
  · dsimp only
    congr 1
  · rfl

structure Randomness (hidden : Hidden) where
  offsets : GLVOffsetFamily.Fiber hidden
  randomizers : Fin 91 → Wordˣ
  chainMasks : Fin 91 → GLVProjectiveMap.ChainMasks
  tableMasks : Fin 91 → GLVProjectiveMap.TableKind →
    Fin IdealAffineTable.tableWidth → Word
  tableMasks_sum : ∀ index kind, ∑ i, tableMasks index kind i =
    ((mapHidden hidden offsets randomizers chainMasks index).params kind).constant

theorem Randomness.ext {hidden : Hidden} (left right : Randomness hidden)
    (hoffsets : left.offsets = right.offsets)
    (hrandomizers : left.randomizers = right.randomizers)
    (hchainMasks : left.chainMasks = right.chainMasks)
    (htableMasks : left.tableMasks = right.tableMasks) : left = right := by
  cases left
  cases right
  cases hoffsets
  cases hrandomizers
  cases hchainMasks
  cases htableMasks
  rfl

def zeroChainMasks : GLVProjectiveMap.ChainMasks where
  xLinear := 0
  xCross := 0
  xOuter := 0
  yCubic := 0
  yQuadratic := 0
  zCross := 0
  zCubic := 0
  zLinear := 0

def canonicalRandomness (hidden : Hidden) : Randomness hidden :=
  let offsets := GLVOffsetFamily.canonical hidden
  let randomizers : Fin 91 → Wordˣ := fun _ => 1
  let chainMasks : Fin 91 → GLVProjectiveMap.ChainMasks :=
    fun _ => zeroChainMasks
  { offsets, randomizers, chainMasks
    tableMasks := fun index kind =>
      (IdealAffineTable.canonicalMasks
        ((mapHidden hidden offsets randomizers chainMasks index).params kind).constant).1
    tableMasks_sum := fun index kind =>
      (IdealAffineTable.canonicalMasks
        ((mapHidden hidden offsets randomizers chainMasks index).params kind).constant).2 }

instance (hidden : Hidden) : Nonempty (Randomness hidden) :=
  ⟨canonicalRandomness hidden⟩

/-- Computable form of multiplication by the norm-seven radix `3 + omega`. -/
def offsetAlpha (point : BN254.G1) : BN254.G1 :=
  3 • point + G1Endomorphism.phi point

theorem offsetAlpha_eq (point : BN254.G1) :
    offsetAlpha point = EisensteinFullWidth.alphaPoint point :=
  (EisensteinFullWidth.alphaPoint_eq_three_add_phi point).symm

/-- Horner recomposition used to solve the leading offset from 90 free offsets. -/
def offsetRecompose : List BN254.G1 → BN254.G1
  | [] => 0
  | head :: tail => head + offsetAlpha (offsetRecompose tail)

theorem offsetRecompose_eq (points : List BN254.G1) :
    offsetRecompose points = EisensteinFullWidth.recompose points := by
  induction points with
  | nil => rfl
  | cons head tail ih =>
      simp only [offsetRecompose, EisensteinFullWidth.recompose_cons, ih,
        offsetAlpha_eq]

/-! ## Protected-oracle instantiation

`Randomness` remains a private proof helper. The accepted `Scheme` below only
receives `InternalOracle`, and this deterministic layout derives every free
coordinate from a distinct typed oracle address. -/

private theorem scalarFieldModulus_fits :
    scalarFieldModulus ≤ 2 ^ 3072 := by
  calc
    scalarFieldModulus ≤ 2 ^ 256 := by norm_num [scalarFieldModulus]
    _ ≤ 2 ^ 3072 := pow_le_pow_right' (by decide) (by decide)

private theorem baseFieldModulus_fits :
    baseFieldModulus ≤ 2 ^ 3072 := by
  calc
    baseFieldModulus ≤ 2 ^ 256 := by norm_num [baseFieldModulus]
    _ ≤ 2 ^ 3072 := pow_le_pow_right' (by decide) (by decide)

private theorem baseFieldUnits_positive : 0 < baseFieldModulus - 1 := by
  norm_num [baseFieldModulus]

private theorem baseFieldUnits_fits :
    baseFieldModulus - 1 ≤ 2 ^ 3072 := by
  calc
    baseFieldModulus - 1 ≤ 2 ^ 256 := by norm_num [baseFieldModulus]
    _ ≤ 2 ^ 3072 := pow_le_pow_right' (by decide) (by decide)

/-- Every free oracle coordinate consumed by the GLV construction.  The
derived leading offset and final table-mask entries are deliberately absent. -/
inductive OracleCoordinate where
  | offset (index : Fin 90)
  | randomizer (index : Fin 91)
  | chain (index : Fin 91) (slot : Fin 8)
  | table (index : Fin 91) (kind : GLVProjectiveMap.TableKind)
      (slot : Fin 253)
  deriving DecidableEq, Fintype

/-- A deterministic, injective purpose assignment internal to this
submission.  It identifies coordinates within one GLV artifact only. -/
def oraclePurpose : OracleCoordinate → Purpose
  | .offset index => index.val
  | .randomizer index => 90 + index.val
  | .chain index slot => 181 + 8 * index.val + slot.val
  | .table index kind slot =>
      909 + (11 * index.val + kind.index) * 253 + slot.val

private theorem tableKind_index_injective :
    Function.Injective GLVProjectiveMap.TableKind.index := by
  intro left right hequal
  cases left <;> cases right <;>
    simp only [GLVProjectiveMap.TableKind.index] at hequal ⊢ <;> omega

theorem oraclePurpose_injective : Function.Injective oraclePurpose := by
  intro left right hequal
  cases left with
  | offset leftIndex =>
      cases right with
      | offset rightIndex =>
          change leftIndex.val = rightIndex.val at hequal
          congr; exact Fin.ext hequal
      | randomizer rightIndex =>
          change leftIndex.val = 90 + rightIndex.val at hequal
          omega
      | chain rightIndex rightSlot =>
          change leftIndex.val = 181 + 8 * rightIndex.val + rightSlot.val at hequal
          omega
      | table rightIndex rightKind rightSlot =>
          change leftIndex.val = 909 +
            (11 * rightIndex.val + rightKind.index) * 253 + rightSlot.val at hequal
          omega
  | randomizer leftIndex =>
      cases right with
      | offset rightIndex =>
          change 90 + leftIndex.val = rightIndex.val at hequal
          omega
      | randomizer rightIndex =>
          change 90 + leftIndex.val = 90 + rightIndex.val at hequal
          congr; apply Fin.ext; omega
      | chain rightIndex rightSlot =>
          change 90 + leftIndex.val =
            181 + 8 * rightIndex.val + rightSlot.val at hequal
          omega
      | table rightIndex rightKind rightSlot =>
          change 90 + leftIndex.val = 909 +
            (11 * rightIndex.val + rightKind.index) * 253 + rightSlot.val at hequal
          omega
  | chain leftIndex leftSlot =>
      cases right with
      | offset rightIndex =>
          change 181 + 8 * leftIndex.val + leftSlot.val = rightIndex.val at hequal
          omega
      | randomizer rightIndex =>
          change 181 + 8 * leftIndex.val + leftSlot.val =
            90 + rightIndex.val at hequal
          omega
      | chain rightIndex rightSlot =>
          change 181 + 8 * leftIndex.val + leftSlot.val =
            181 + 8 * rightIndex.val + rightSlot.val at hequal
          have hindex : leftIndex.val = rightIndex.val := by omega
          have hslot : leftSlot.val = rightSlot.val := by omega
          congr <;> apply Fin.ext <;> assumption
      | table rightIndex rightKind rightSlot =>
          change 181 + 8 * leftIndex.val + leftSlot.val = 909 +
            (11 * rightIndex.val + rightKind.index) * 253 + rightSlot.val at hequal
          omega
  | table leftIndex leftKind leftSlot =>
      cases right with
      | offset rightIndex =>
          change 909 + (11 * leftIndex.val + leftKind.index) * 253 +
            leftSlot.val = rightIndex.val at hequal
          omega
      | randomizer rightIndex =>
          change 909 + (11 * leftIndex.val + leftKind.index) * 253 +
            leftSlot.val = 90 + rightIndex.val at hequal
          omega
      | chain rightIndex rightSlot =>
          change 909 + (11 * leftIndex.val + leftKind.index) * 253 +
            leftSlot.val = 181 + 8 * rightIndex.val + rightSlot.val at hequal
          omega
      | table rightIndex rightKind rightSlot =>
          change 909 + (11 * leftIndex.val + leftKind.index) * 253 +
            leftSlot.val = 909 +
              (11 * rightIndex.val + rightKind.index) * 253 +
                rightSlot.val at hequal
          have howner : 11 * leftIndex.val + leftKind.index =
              11 * rightIndex.val + rightKind.index := by omega
          have hslot : leftSlot.val = rightSlot.val := by omega
          have hindex : leftIndex.val = rightIndex.val := by
            have hleft : leftKind.index < 11 := by cases leftKind <;> decide
            have hright : rightKind.index < 11 := by cases rightKind <;> decide
            omega
          have hkindIndex : leftKind.index = rightKind.index := by omega
          have hkind : leftKind = rightKind :=
            tableKind_index_injective hkindIndex
          congr
          · exact Fin.ext hindex
          · exact Fin.ext hslot

def offsetPurpose (index : Fin 90) : Purpose :=
  oraclePurpose (.offset index)

def randomizerPurpose (index : Fin 91) : Purpose :=
  oraclePurpose (.randomizer index)

def chainPurpose (index : Fin 91) (slot : Fin 8) : Purpose :=
  oraclePurpose (.chain index slot)

def tableMaskPurpose (index : Fin 91) (kind : GLVProjectiveMap.TableKind)
    (slot : Fin 253) : Purpose :=
  oraclePurpose (.table index kind slot)

def scalarSample (oracle : InternalOracle) (purpose : Purpose) :
    Fin scalarFieldModulus :=
  oracle.sample scalarFieldModulus (by norm_num [scalarFieldModulus])
    scalarFieldModulus_fits purpose

def wordSample (oracle : InternalOracle) (purpose : Purpose) : Word :=
  (oracle.sample baseFieldModulus (by norm_num [baseFieldModulus])
    baseFieldModulus_fits purpose).val

def unitSampleValue (oracle : InternalOracle) (purpose : Purpose) : Nat :=
  (oracle.sample (baseFieldModulus - 1) baseFieldUnits_positive
    baseFieldUnits_fits purpose).val + 1

private theorem unitSampleValue_positive (oracle : InternalOracle)
    (purpose : Purpose) : 0 < unitSampleValue oracle purpose := by
  unfold unitSampleValue
  omega

private theorem unitSampleValue_lt (oracle : InternalOracle)
    (purpose : Purpose) : unitSampleValue oracle purpose < baseFieldModulus := by
  have h := (oracle.sample (baseFieldModulus - 1) baseFieldUnits_positive
    baseFieldUnits_fits purpose).isLt
  unfold unitSampleValue
  omega

private theorem unitSampleValue_ne_zero (oracle : InternalOracle)
    (purpose : Purpose) :
    ((unitSampleValue oracle purpose : Nat) : Word) ≠ 0 := by
  intro hzero
  have hdvd : baseFieldModulus ∣ unitSampleValue oracle purpose :=
    (ZMod.natCast_eq_zero_iff _ _).mp hzero
  have hle : baseFieldModulus ≤ unitSampleValue oracle purpose :=
    Nat.le_of_dvd (unitSampleValue_positive oracle purpose) hdvd
  exact (Nat.not_le_of_gt (unitSampleValue_lt oracle purpose)) hle

def randomizerSample (oracle : InternalOracle) (purpose : Purpose) : Wordˣ :=
  Units.mk0 (unitSampleValue oracle purpose : Word)
    (unitSampleValue_ne_zero oracle purpose)

def standardGenerator : BN254.G1 :=
  BN254.ofAffine
    ⟨1, by norm_num [baseFieldModulus]⟩
    ⟨2, by norm_num [baseFieldModulus]⟩
    (by norm_num [BN254.OnCurve])

def sampledOffsetTail (oracle : InternalOracle) : List BN254.G1 :=
  (List.finRange 90).map fun index =>
    (scalarSample oracle (offsetPurpose index)).val • standardGenerator

@[simp] theorem sampledOffsetTail_length (oracle : InternalOracle) :
    (sampledOffsetTail oracle).length = 90 := by
  simp [sampledOffsetTail]

def offsetsFromOracle (hidden : Hidden) (oracle : InternalOracle) :
    GLVOffsetFamily.Fiber hidden :=
  let tail := sampledOffsetTail oracle
  { values :=
      (GLVOffsetFamily.qPoint hidden -
        offsetAlpha (offsetRecompose tail)) :: tail
    length_eq := by
      exact (congrArg Nat.succ (sampledOffsetTail_length oracle)).trans rfl
    total_eq := by
      change (GLVOffsetFamily.qPoint hidden -
        offsetAlpha (offsetRecompose tail)) +
          EisensteinFullWidth.alphaPoint
            (EisensteinFullWidth.recompose tail) = GLVOffsetFamily.qPoint hidden
      rw [offsetRecompose_eq, offsetAlpha_eq]
      abel }


def chainMasksFromOracle (oracle : InternalOracle) (index : Fin 91) :
    GLVProjectiveMap.ChainMasks where
  xLinear := wordSample oracle (chainPurpose index 0)
  xCross := wordSample oracle (chainPurpose index 1)
  xOuter := wordSample oracle (chainPurpose index 2)
  yCubic := wordSample oracle (chainPurpose index 3)
  yQuadratic := wordSample oracle (chainPurpose index 4)
  zCross := wordSample oracle (chainPurpose index 5)
  zCubic := wordSample oracle (chainPurpose index 6)
  zLinear := wordSample oracle (chainPurpose index 7)

def tableMaskFree (oracle : InternalOracle) (index : Fin 91)
    (kind : GLVProjectiveMap.TableKind) (slot : Fin 253) : Word :=
  wordSample oracle (tableMaskPurpose index kind slot)

def tableMaskFiber (constant : Word) (oracle : InternalOracle)
    (index : Fin 91) (kind : GLVProjectiveMap.TableKind) :
    IdealAffineTable.MaskFiber constant :=
  let free : Fin 253 → Word := tableMaskFree oracle index kind
  let final := constant - ∑ slot, free slot
  ⟨Fin.lastCases final free, by
    change ∑ i : Fin (253 + 1), Fin.lastCases final free i = constant
    rw [Fin.sum_univ_castSucc]
    rw [Fin.lastCases_last]
    simp [final]⟩

/-- Extension by one final value with constant-time executable indexing.
`Fin.lastCases` is the convenient proof-level eliminator, but its generated
code reaches an arbitrary index by reverse induction. -/
def indexedLastCases {n : Nat} {α : Type}
    (last : α) (init : Fin n → α) (index : Fin (n + 1)) : α :=
  if h : index.val < n then init ⟨index.val, h⟩ else last

theorem indexedLastCases_eq_lastCases {n : Nat} {α : Type}
    (last : α) (init : Fin n → α) :
    indexedLastCases last init = Fin.lastCases last init := by
  funext index
  refine Fin.lastCases ?_ (fun slot => ?_) index
  · simp [indexedLastCases]
  · simp [indexedLastCases]

/-- Strict executable representative of `tableMaskFiber`.  The ideal
definition above stays transparent for the distribution proof; this version
materializes the 253 independent coordinates once so repeated row openings do
not repeat oracle calls or the checksum fold. -/
def materializedTableMaskFiber (constant : Word) (oracle : InternalOracle)
    (index : Fin 91) (kind : GLVProjectiveMap.TableKind) :
    IdealAffineTable.MaskFiber constant :=
  let packedFree : Vector Word 253 :=
    Vector.ofFn (tableMaskFree oracle index kind)
  let free : Fin 253 → Word := fun slot => packedFree[slot.val]
  let final := constant - ∑ slot, free slot
  ⟨indexedLastCases final free, by
    change ∑ i : Fin (253 + 1), indexedLastCases final free i = constant
    rw [indexedLastCases_eq_lastCases, Fin.sum_univ_castSucc,
      Fin.lastCases_last]
    simp [final]⟩

theorem materializedTableMaskFiber_eq (constant : Word)
    (oracle : InternalOracle) (index : Fin 91)
    (kind : GLVProjectiveMap.TableKind) :
    materializedTableMaskFiber constant oracle index kind =
      tableMaskFiber constant oracle index kind := by
  apply Subtype.ext
  funext slot
  unfold materializedTableMaskFiber tableMaskFiber
  simp [IdealAffineTable.tableWidth, indexedLastCases_eq_lastCases]

def randomnessFromOracle (hidden : Hidden) (oracle : InternalOracle) :
    Randomness hidden :=
  let offsets := offsetsFromOracle hidden oracle
  let randomizers : Fin 91 → Wordˣ := fun index =>
    randomizerSample oracle (randomizerPurpose index)
  let chainMasks : Fin 91 → GLVProjectiveMap.ChainMasks :=
    chainMasksFromOracle oracle
  { offsets, randomizers, chainMasks
    tableMasks := fun index kind =>
      (tableMaskFiber
        ((mapHidden hidden offsets randomizers chainMasks index).params kind).constant
        oracle index kind).1
    tableMasks_sum := fun index kind =>
      (tableMaskFiber
        ((mapHidden hidden offsets randomizers chainMasks index).params kind).constant
        oracle index kind).2 }

def xWire (index : Fin IdealAffineTable.tableWidth) : BitIndex :=
  ⟨index.val, by
    change index.val < 2 * coordinateWidth
    have := index.isLt
    norm_num [IdealAffineTable.tableWidth, coordinateWidth] at this ⊢
    omega⟩

def yWire (index : Fin IdealAffineTable.tableWidth) : BitIndex :=
  ⟨coordinateWidth + index.val, by
    change coordinateWidth + index.val < 2 * coordinateWidth
    have := index.isLt
    norm_num [IdealAffineTable.tableWidth, coordinateWidth] at this ⊢
    omega⟩

def xPairs (pairs : LabelPairs) :
    Fin IdealAffineTable.tableWidth → Bool → Label :=
  fun index bit => pairs (xWire index) bit

def yPairs (pairs : LabelPairs) :
    Fin IdealAffineTable.tableWidth → Bool → Label :=
  fun index bit => pairs (yWire index) bit

def garble (hidden : Hidden) (randomness : Randomness hidden)
    (pairs : LabelPairs) : Artifact where
  maps := fun index =>
    GLVProjectiveMap.garble index.val (xPairs pairs) (yPairs pairs)
      (mapHidden hidden randomness.offsets randomness.randomizers
        randomness.chainMasks index)
      (fun kind => ⟨randomness.tableMasks index kind,
        randomness.tableMasks_sum index kind⟩)

@[simp] theorem garble_map (hidden : Hidden) (randomness : Randomness hidden)
    (pairs : LabelPairs) (index : Fin 91) :
    (garble hidden randomness pairs).maps index =
      GLVProjectiveMap.garble index.val (xPairs pairs) (yPairs pairs)
        (mapHidden hidden randomness.offsets randomness.randomizers
          randomness.chainMasks index)
        (fun kind => ⟨randomness.tableMasks index kind,
          randomness.tableMasks_sum index kind⟩) := rfl

/-- Force all 127 packed pairs of a table while its inputs are shared values.
The public table type remains the challenge's function-backed representation. -/
def materializeTable (table : IdealAffineTable.Table) :
    IdealAffineTable.Table :=
  let packed : Vector IdealAffineTable.PackedPair
      IdealAffineTable.pairCount := Vector.ofFn table.pairs
  { pairs := fun pair => packed[pair.val] }

@[simp] theorem materializeTable_eq (table : IdealAffineTable.Table) :
    materializeTable table = table := by
  apply IdealAffineTable.Table.ext
  funext pair
  simp [materializeTable]

/-- Build one complete table eagerly.  Keeping mask materialization and pair
materialization in the same strict scope prevents either function-backed layer
from reconstructing the oracle-derived vector. -/
def garbleTableWithOracle (index : Fin 91)
    (kind : GLVProjectiveMap.TableKind)
    (xPairs yPairs : Fin IdealAffineTable.tableWidth → Bool → Label)
    (hidden : GLVProjectiveMap.Hidden) (oracle : InternalOracle) :
    IdealAffineTable.Table :=
  let params := hidden.params kind
  let masks := materializedTableMaskFiber params.constant oracle index kind
  materializeTable (IdealAffineTable.garble
    (GLVProjectiveMap.purpose index.val kind)
    (GLVProjectiveMap.pairsFor xPairs yPairs kind) params masks)

theorem garbleTableWithOracle_eq (index : Fin 91)
    (kind : GLVProjectiveMap.TableKind)
    (xPairs yPairs : Fin IdealAffineTable.tableWidth → Bool → Label)
    (hidden : GLVProjectiveMap.Hidden) (oracle : InternalOracle) :
    garbleTableWithOracle index kind xPairs yPairs hidden oracle =
      IdealAffineTable.garble (GLVProjectiveMap.purpose index.val kind)
        (GLVProjectiveMap.pairsFor xPairs yPairs kind) (hidden.params kind)
        (tableMaskFiber (hidden.params kind).constant oracle index kind) := by
  unfold garbleTableWithOracle
  rw [materializeTable_eq, materializedTableMaskFiber_eq]

/-- Expose tables on demand.  Each selected table is internally materialized,
but maps do not retain all eleven expanded table objects at once. -/
def garbleMapWithOracle (index : Fin 91)
    (xPairs yPairs : Fin IdealAffineTable.tableWidth → Bool → Label)
    (hidden : GLVProjectiveMap.Hidden) (oracle : InternalOracle) :
    GLVProjectiveMap.Artifact :=
  { tables := fun kind =>
      garbleTableWithOracle index kind xPairs yPairs hidden oracle }

@[simp] theorem garbleMapWithOracle_table (index : Fin 91)
    (xPairs yPairs : Fin IdealAffineTable.tableWidth → Bool → Label)
    (hidden : GLVProjectiveMap.Hidden) (oracle : InternalOracle)
    (kind : GLVProjectiveMap.TableKind) :
    (garbleMapWithOracle index xPairs yPairs hidden oracle).tables kind =
      garbleTableWithOracle index kind xPairs yPairs hidden oracle := by
  rfl

theorem garbleMapWithOracle_eq (index : Fin 91)
    (xPairs yPairs : Fin IdealAffineTable.tableWidth → Bool → Label)
    (hidden : GLVProjectiveMap.Hidden) (oracle : InternalOracle) :
    garbleMapWithOracle index xPairs yPairs hidden oracle =
      GLVProjectiveMap.garble index.val xPairs yPairs hidden
        (fun kind => tableMaskFiber
          (hidden.params kind).constant oracle index kind) := by
  apply GLVProjectiveMap.Artifact.ext
  funext kind
  rw [garbleMapWithOracle_table, garbleTableWithOracle_eq]
  rfl

def garbleWithOracle (hidden : Hidden) (oracle : InternalOracle)
    (pairs : LabelPairs) : Artifact :=
  let randomness := randomnessFromOracle hidden oracle
  let mapStates := materializedMapHiddenFamily hidden randomness.offsets
    randomness.randomizers randomness.chainMasks
  { maps := fun index =>
    garbleMapWithOracle index (xPairs pairs) (yPairs pairs)
      (mapStates index) oracle }

@[simp] theorem garbleWithOracle_map (hidden : Hidden)
    (oracle : InternalOracle) (pairs : LabelPairs) (index : Fin 91) :
    (garbleWithOracle hidden oracle pairs).maps index =
      garbleMapWithOracle index (xPairs pairs) (yPairs pairs)
        (mapHidden hidden (randomnessFromOracle hidden oracle).offsets
          (randomnessFromOracle hidden oracle).randomizers
          (randomnessFromOracle hidden oracle).chainMasks index) oracle := by
  simp [garbleWithOracle]

theorem garbleWithOracle_eq (hidden : Hidden) (oracle : InternalOracle)
    (pairs : LabelPairs) :
    garbleWithOracle hidden oracle pairs =
      garble hidden (randomnessFromOracle hidden oracle) pairs := by
  apply GLVFamilyArtifact.Artifact.ext
  funext index
  rw [garbleWithOracle_map, garbleMapWithOracle_eq, garble_map]
  apply congrArg (GLVProjectiveMap.garble index.val (xPairs pairs) (yPairs pairs)
    (mapHidden hidden (randomnessFromOracle hidden oracle).offsets
      (randomnessFromOracle hidden oracle).randomizers
      (randomnessFromOracle hidden oracle).chainMasks index))
  funext kind
  apply Subtype.ext
  rfl

def xBits (input : Input) : Fin IdealAffineTable.tableWidth → Bool :=
  fun index => input.x.val.testBit index.val

def yBits (input : Input) : Fin IdealAffineTable.tableWidth → Bool :=
  fun index => input.y.val.testBit index.val

def xLabels (labels : ActiveLabels) :
    Fin IdealAffineTable.tableWidth → Label :=
  fun index => labels (xWire index)

def yLabels (labels : ActiveLabels) :
    Fin IdealAffineTable.tableWidth → Label :=
  fun index => labels (yWire index)

private theorem baseFieldModulus_lt_two_pow_tableWidth :
    baseFieldModulus < 2 ^ IdealAffineTable.tableWidth := by
  norm_num [baseFieldModulus, IdealAffineTable.tableWidth]

theorem decodeBits_xBits (input : Input) :
  IdealAffineTable.decodeBits (xBits input) = (input.x.val : Word) := by
  apply IdealAffineTable.decodeBits_testBit
  exact input.x.isLt.trans baseFieldModulus_lt_two_pow_tableWidth

theorem decodeBits_yBits (input : Input) :
  IdealAffineTable.decodeBits (yBits input) = (input.y.val : Word) := by
  apply IdealAffineTable.decodeBits_testBit
  exact input.y.isLt.trans baseFieldModulus_lt_two_pow_tableWidth

theorem active_xLabels (pairs : LabelPairs) (input : Input) :
    xLabels (activeLabels pairs input) =
      fun index => xPairs pairs index (xBits input index) := by
  funext index purpose
  have hindex : index.val < coordinateWidth := by
    have := index.isLt
    norm_num [IdealAffineTable.tableWidth, coordinateWidth] at this ⊢
    omega
  simp [xLabels, activeLabels, xPairs, xWire, xBits, inputBit, hindex]

theorem active_yLabels (pairs : LabelPairs) (input : Input) :
    yLabels (activeLabels pairs input) =
      fun index => yPairs pairs index (yBits input index) := by
  funext index purpose
  simp [yLabels, activeLabels, yPairs, yWire, yBits, inputBit]

def evaluateMap (index : Fin 91) (artifact : GLVProjectiveMap.Artifact)
    (input : Input) (labels : ActiveLabels) : Except EvalError Point :=
  GLVProjectiveMapRuntime.evaluate index.val artifact
    (input.x.val : Word) (input.y.val : Word)
    (xBits input) (yBits input) (xLabels labels) (yLabels labels)

def evaluateMaps (artifact : Artifact) (input : Input)
    (labels : ActiveLabels) : List (Fin 91) → Except EvalError (List Point)
  | [] => .ok []
  | index :: tail => do
      let point ← evaluateMap index (artifact.maps index) input labels
      let points ← evaluateMaps artifact input labels tail
      pure (point :: points)

def evaluate (artifact : Artifact) (input : Input)
    (labels : ActiveLabels) : Except EvalError Profile.Output := do
  let points ← evaluateMaps artifact input labels (List.finRange 91)
  let result ← RuntimeG1.recomposeAlpha points
  pure (show Profile.Output from RuntimeG1.toOutput result)

theorem rawMap_eq_addFormula (offset : BN254.G1) (digit : Digit)
    (input : Input) :
    rawMap offset digit input =
      HomogeneousRCBG1GroupLaw.addFormula
        (RuntimeG1.encode (runtimeOfGroup offset))
        (RuntimeG1.encode (digitRuntime digit input)) := by
  unfold rawMap HomogeneousRCBG1GroupLaw.addFormula curveC ProjectiveMap.curveC
  rw [selectedInput_eq_digitRuntime]

theorem rawMap_valid (offset : BN254.G1) (digit : Digit) (input : Input) :
    BN254.curve.toJacobian.Nonsingular
      (HomogeneousRCBG1GroupLaw.toJacobian (rawMap offset digit input)) := by
  rw [rawMap_eq_addFormula]
  exact HomogeneousRCBG1GroupLaw.toJacobian_formula_valid
    (runtimeOfGroup offset).1 (digitRuntime digit input).1
    (runtimeOfGroup offset).2 (digitRuntime digit input).2

theorem toPoint_digitRuntime (digit : Digit) (input : Input) :
    RuntimeG1.toPoint (digitRuntime digit input) =
      EisensteinFullWidth.digitTerm digit (inputG1 input) := by
  rw [EisensteinFullWidth.digitTerm_eq_unitPoint]
  cases digit with
  | zero => rfl
  | one => exact toPoint_digitBaseRuntime .one input
  | omega => exact toPoint_digitBaseRuntime .omega input
  | omegaSq => exact toPoint_digitBaseRuntime .omegaSq input
  | negOne =>
      rw [show digitRuntime .negOne input =
          RuntimeG1.ofAffine
            (HomogeneousRCBG1GroupLaw.negAffine (digitAffine .negOne input))
            (HomogeneousRCBG1GroupLaw.negAffine_onCurve
              (digitAffine .negOne input) (digitAffine_onCurve .negOne input))
        by rfl,
        RuntimeG1.toPoint_negAffine]
      change -RuntimeG1.toPoint (digitBaseRuntime .negOne input) =
        -inputG1 input
      exact congrArg Neg.neg (toPoint_digitBaseRuntime .negOne input)
  | negOmega =>
      rw [show digitRuntime .negOmega input =
          RuntimeG1.ofAffine
            (HomogeneousRCBG1GroupLaw.negAffine (digitAffine .negOmega input))
            (HomogeneousRCBG1GroupLaw.negAffine_onCurve
              (digitAffine .negOmega input) (digitAffine_onCurve .negOmega input))
        by rfl,
        RuntimeG1.toPoint_negAffine]
      change -RuntimeG1.toPoint (digitBaseRuntime .negOmega input) =
        -G1Endomorphism.phi (inputG1 input)
      exact congrArg Neg.neg (toPoint_digitBaseRuntime .negOmega input)
  | negOmegaSq =>
      rw [show digitRuntime .negOmegaSq input =
          RuntimeG1.ofAffine
            (HomogeneousRCBG1GroupLaw.negAffine
              (digitAffine .negOmegaSq input))
            (HomogeneousRCBG1GroupLaw.negAffine_onCurve
              (digitAffine .negOmegaSq input)
              (digitAffine_onCurve .negOmegaSq input)) by rfl,
        RuntimeG1.toPoint_negAffine]
      change -RuntimeG1.toPoint (digitBaseRuntime .negOmegaSq input) =
        -G1Endomorphism.phi (G1Endomorphism.phi (inputG1 input))
      exact congrArg Neg.neg (toPoint_digitBaseRuntime .negOmegaSq input)

theorem decode_rawMap (offset : BN254.G1) (digit : Digit) (input : Input) :
    FormulaSemantics.Law.decode (rawMap offset digit input) =
      offset + EisensteinFullWidth.digitTerm digit (inputG1 input) := by
  rw [rawMap_eq_addFormula]
  unfold RuntimeG1.encode
  rw [FormulaSemantics.Law.decode_formula
    (runtimeOfGroup offset).1 (digitRuntime digit input).1
    (runtimeOfGroup offset).2 (digitRuntime digit input).2]
  rw [← RuntimeG1.toPoint_eq_pointOfInput (runtimeOfGroup offset),
    ← RuntimeG1.toPoint_eq_pointOfInput (digitRuntime digit input),
    toPoint_runtimeOfGroup, toPoint_digitRuntime]

theorem mapOutput_eq (offset : BN254.G1) (digit : Digit) (input : Input) :
    EisensteinFullWidth.mapOutput offset digit (-inputG1 input) =
      offset + EisensteinFullWidth.digitTerm digit (inputG1 input) := by
  unfold EisensteinFullWidth.mapOutput
  rw [EisensteinFullWidth.digitTerm_neg]
  abel

def localHidden (offset : BN254.G1) (digit : Digit) (randomizer : Wordˣ)
    (chainMasks : GLVProjectiveMap.ChainMasks) : GLVProjectiveMap.Hidden where
  coefficients := randomizedCoefficients offset digit randomizer
  chainMasks := chainMasks

theorem evaluateMap_projectiveGarble (offset : BN254.G1) (digit : Digit)
    (randomizer : Wordˣ) (chainMasks : GLVProjectiveMap.ChainMasks)
    (tableMasks : (kind : GLVProjectiveMap.TableKind) →
      IdealAffineTable.MaskFiber
        ((localHidden offset digit randomizer chainMasks).params kind).constant)
    (pairs : LabelPairs) (input : Input) (index : Fin 91) :
    ∃ result : Point,
      evaluateMap index
          (GLVProjectiveMap.garble index.val (xPairs pairs) (yPairs pairs)
            (localHidden offset digit randomizer chainMasks) tableMasks)
          input
          (activeLabels pairs input) = Except.ok result ∧
        RuntimeG1.toPoint result =
          EisensteinFullWidth.mapOutput offset digit (-inputG1 input) := by
  have hlabelsX := active_xLabels pairs input
  have hlabelsY := active_yLabels pairs input
  have hprojective := polynomial_randomizedCoefficients
    offset digit randomizer input
  have hvalid := rawMap_valid offset digit input
  obtain ⟨result, hnormalize, hresult⟩ :=
    RuntimeG1.normalize_randomize_of_valid
      (rawMap offset digit input) hvalid randomizer
  refine ⟨result, ?_, ?_⟩
  · unfold evaluateMap
    rw [hlabelsX, hlabelsY, ← decodeBits_xBits, ← decodeBits_yBits]
    calc
      GLVProjectiveMapRuntime.evaluate index.val
          (GLVProjectiveMap.garble index.val (xPairs pairs) (yPairs pairs)
            (localHidden offset digit randomizer chainMasks) tableMasks)
          (IdealAffineTable.decodeBits (xBits input))
          (IdealAffineTable.decodeBits (yBits input))
          (xBits input) (yBits input)
          (fun i => xPairs pairs i (xBits input i))
          (fun i => yPairs pairs i (yBits input i)) =
          GLVProjectiveMapRuntime.normalizeCoordinates
            (ProjectiveMap.polynomial
              (localHidden offset digit randomizer chainMasks).coefficients
              (IdealAffineTable.decodeBits (xBits input))
              (IdealAffineTable.decodeBits (yBits input))) :=
            GLVProjectiveMapRuntime.evaluate_garble index.val
              (xPairs pairs) (yPairs pairs)
              (localHidden offset digit randomizer chainMasks) tableMasks
              (xBits input) (yBits input)
              (by
                rw [decodeBits_xBits, decodeBits_yBits]
                change ((input.y.val : Word) ^ 2 =
                  (input.x.val : Word) ^ 3 + 3)
                exact input.onCurve)
      _ = Except.ok result := by
        rw [decodeBits_xBits, decodeBits_yBits]
        unfold GLVProjectiveMapRuntime.normalizeCoordinates
        rw [show (localHidden offset digit randomizer chainMasks).coefficients =
            randomizedCoefficients offset digit randomizer by rfl,
          hprojective]
        exact hnormalize
  · rw [hresult, decode_rawMap, mapOutput_eq]

theorem evaluateMap_garble (hidden : Hidden) (randomness : Randomness hidden)
    (pairs : LabelPairs) (input : Input) (index : Fin 91) :
    ∃ result : Point,
      evaluateMap index ((garble hidden randomness pairs).maps index) input
          (activeLabels pairs input) = Except.ok result ∧
        RuntimeG1.toPoint result =
          EisensteinFullWidth.mapOutput (offsetAt randomness.offsets index)
            (digitAt hidden index) (-inputG1 input) := by
  rw [garble_map]
  exact evaluateMap_projectiveGarble
    (offsetAt randomness.offsets index) (digitAt hidden index)
    (randomness.randomizers index) (randomness.chainMasks index)
    (fun kind => ⟨randomness.tableMasks index kind,
      randomness.tableMasks_sum index kind⟩) pairs input index

theorem evaluateMaps_garble (hidden : Hidden) (randomness : Randomness hidden)
    (pairs : LabelPairs) (input : Input) (indices : List (Fin 91)) :
    ∃ results : List Point,
      evaluateMaps (garble hidden randomness pairs) input
          (activeLabels pairs input) indices = .ok results ∧
        results.map RuntimeG1.toPoint =
          indices.map fun index =>
            EisensteinFullWidth.mapOutput (offsetAt randomness.offsets index)
              (digitAt hidden index) (-inputG1 input) := by
  induction indices with
  | nil => exact ⟨[], rfl, rfl⟩
  | cons index indices ih =>
      obtain ⟨point, hpoint, hpointValue⟩ :=
        evaluateMap_garble hidden randomness pairs input index
      obtain ⟨points, hpoints, hpointsValue⟩ := ih
      refine ⟨point :: points, ?_, ?_⟩
      · unfold evaluateMaps
        rw [hpoint, hpoints]
        rfl
      · simp only [List.map_cons]
        rw [hpointValue, hpointsValue]

private theorem map_finRange_offsetAt (hidden : Hidden)
    (offsets : GLVOffsetFamily.Fiber hidden) :
    (List.finRange 91).map (offsetAt offsets) = offsets.values := by
  exact map_getFixed_finRange offsets.values offsets.length_eq

private theorem map_finRange_digitAt (hidden : Hidden) :
    (List.finRange 91).map (digitAt hidden) =
      GLVOffsetFamily.digits hidden := by
  exact map_getFixed_finRange (GLVOffsetFamily.digits hidden)
    (GLVOffsetFamily.digits_length hidden)

private theorem zipWith_map_same {Index Left Right Result : Type*}
    (combine : Left → Right → Result) (left : Index → Left)
    (right : Index → Right) (indices : List Index) :
    List.zipWith combine (indices.map left) (indices.map right) =
      indices.map fun index => combine (left index) (right index) := by
  induction indices with
  | nil => rfl
  | cons index indices ih =>
      simp only [List.map_cons, List.zipWith_cons_cons]
      rw [ih]

theorem fullMapOutputs (hidden : Hidden)
    (offsets : GLVOffsetFamily.Fiber hidden) (input : Input) :
    (List.finRange 91).map (fun index =>
        EisensteinFullWidth.mapOutput (offsetAt offsets index)
          (digitAt hidden index) (-inputG1 input)) =
      EisensteinFullWidth.mapOutputs offsets.values
        (GLVOffsetFamily.digits hidden) (-inputG1 input) := by
  unfold EisensteinFullWidth.mapOutputs
  rw [← zipWith_map_same
    (fun offset digit => EisensteinFullWidth.mapOutput offset digit
      (-inputG1 input)) (offsetAt offsets) (digitAt hidden)]
  rw [map_finRange_offsetAt, map_finRange_digitAt]

theorem pointwise_of_finRange_map_eq {Value : Type*}
    (left right : Fin count → Value)
    (equality : (List.finRange count).map left =
      (List.finRange count).map right) (index : Fin count) :
    left index = right index := by
  have atIndex := congrArg (fun values => values[index.val]?) equality
  simpa using atIndex

theorem artifactCorrect (hidden : Hidden) (randomness : Randomness hidden)
    (pairs : LabelPairs) (input : Input) :
    ∃ output : Profile.Output,
      evaluate (garble hidden randomness pairs) input
          (activeLabels pairs input) = .ok output ∧
        Profile.outputEquiv output = reference Profile hidden input := by
  obtain ⟨points, hpoints, hpointsValue⟩ :=
    evaluateMaps_garble hidden randomness pairs input (List.finRange 91)
  obtain ⟨result, hresult, hresultValue⟩ :=
    RuntimeG1.recomposeAlpha_correct points
  refine ⟨show Profile.Output from RuntimeG1.toOutput result, ?_, ?_⟩
  · unfold evaluate
    rw [hpoints]
    change (do
      let result ← RuntimeG1.recomposeAlpha points
      pure (RuntimeG1.toOutput result)) = _
    rw [hresult]
    rfl
  · change BN254.CanonicalOutput.toPoint (RuntimeG1.toOutput result) = _
    rw [RuntimeG1.output_toPoint, hresultValue, hpointsValue,
      fullMapOutputs]
    change EisensteinFullWidth.outputList randomness.offsets.values
      (GLVOffsetFamily.digits hidden) (-inputG1 input) =
        GLVOffsetFamily.qPoint hidden + hidden.r.val • inputG1 input
    have hsemantic := EisensteinFullWidth.output_scalar
      randomness.offsets.values hidden.r (-inputG1 input)
      randomness.offsets.length_eq
    unfold GLVOffsetFamily.digits
    rw [hsemantic, randomness.offsets.total_eq]
    rw [EisensteinFullWidth.point_nsmul_neg]
    abel

def encodeArtifact : Artifact → ByteArray := GLVFamilyArtifact.encode

/-- Native execution may build the independent map encodings concurrently.
The logical scheme and all privacy proofs continue to see the canonical
sequential encoder. -/
def encodeArtifactParallel : Artifact → ByteArray :=
  GLVFamilyArtifact.encodeParallel

@[csimp] theorem encodeArtifact_eq_parallel :
    encodeArtifact = encodeArtifactParallel := by
  funext artifact
  simp [encodeArtifact, encodeArtifactParallel]

def decodeArtifact (bytes : ByteArray) : Except DecodeError Artifact :=
  match GLVFamilyArtifact.decode 91 bytes with
  | .ok artifact => .ok artifact
  | .error .trailingBytes => .error .trailingBytes
  | .error _ => .error .malformedArtifact

def scheme : Scheme Profile :=
  Scheme.ofFunctions Artifact garbleWithOracle evaluate encodeArtifact
    decodeArtifact

theorem codec : CodecLaws scheme := by
  apply Scheme.codecLaws_ofFunctions
  · intro artifact
    unfold decodeArtifact encodeArtifact
    rw [GLVFamilyArtifact.decode_encode]
  · intro bytes artifact hdecode
    unfold decodeArtifact at hdecode
    cases hfamily : GLVFamilyArtifact.decode 91 bytes with
    | error error =>
        cases error <;> simp [hfamily] at hdecode
    | ok decoded =>
        have hdecoded : decoded = artifact := by simpa [hfamily] using hdecode
        subst decoded
        exact GLVFamilyArtifact.encode_decode hfamily

theorem correct : Correct scheme := by
  apply Scheme.correct_ofFunctions Artifact garbleWithOracle evaluate
    encodeArtifact decodeArtifact codec
  intro hidden oracle pairs input
  rw [garbleWithOracle_eq]
  exact artifactCorrect hidden (randomnessFromOracle hidden oracle) pairs input

def claimedBytes : Nat := 16145129

set_option maxRecDepth 4096 in
theorem artifactBound (hidden : Hidden) (randomness : Randomness hidden)
    (pairs : LabelPairs) :
    (GLVFamilyArtifact.encode (garble hidden randomness pairs)).size ≤
      claimedBytes := by
  rw [GLVFamilyArtifact.encode_size, GLVFamilyArtifact.ninetyOne_byteCount]
  rfl

set_option maxRecDepth 4096 in
theorem artifactBoundOracle (hidden : Hidden) (oracle : InternalOracle)
    (pairs : LabelPairs) :
    (scheme.garbleBytes hidden oracle pairs).size ≤ claimedBytes := by
  change (GLVFamilyArtifact.encode
    (garbleWithOracle hidden oracle pairs)).size ≤ _
  rw [garbleWithOracle_eq]
  exact artifactBound hidden (randomnessFromOracle hidden oracle) pairs


end GarblingPrize.Submission.GLVCompactScheme
