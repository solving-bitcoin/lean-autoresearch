import GarblingPrize.Submission.FamilyArtifact
import GarblingPrize.Submission.G1Cardinality
import GarblingPrize.Submission.OffsetFamily
import GarblingPrize.Submission.ProjectiveMapPrivacy
import GarblingPrize.Submission.ProjectiveMapRuntime

namespace GarblingPrize.Submission.CompactScheme

open GarblingPrize.Protected
open GarblingPrize.Submission.BalancedTernary

abbrev Profile := BN254.bn254
abbrev Hidden := HiddenInput Profile
abbrev Input := AffineInput Profile
abbrev Word := BN254.Fq
abbrev Point := RuntimeG1.Point
abbrev Artifact := FamilyArtifact.Artifact 161

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
  | .negative => true
  | .zero => false
  | .positive => true

def digitSign : Digit → HomogeneousRCB.Sign
  | .negative => .negative
  | .zero => .positive
  | .positive => .positive

def digitRuntime (digit : Digit) (input : Input) : Point :=
  match digit with
  | .negative =>
      RuntimeG1.ofAffine (HomogeneousRCBG1GroupLaw.negAffine (inputAffine input))
        (HomogeneousRCBG1GroupLaw.negAffine_onCurve (inputAffine input)
          (inputAffine_onCurve input))
  | .zero => RuntimeG1.infinity
  | .positive => inputRuntime input

theorem selectedInput_eq_digitRuntime (digit : Digit) (input : Input) :
    HomogeneousRCB.selectedInput (digitSelector digit) (digitSign digit)
        (RuntimeG1.encode (inputRuntime input)) =
      RuntimeG1.encode (digitRuntime digit input) := by
  cases digit with
  | negative =>
      simpa [digitSelector, digitSign, digitRuntime, inputRuntime,
        RuntimeG1.encode, RuntimeG1.ofAffine] using
        HomogeneousRCBG1GroupLaw.selectedInput_negative_eq_encode true
          (inputAffine input)
  | zero =>
      simpa [digitSelector, digitSign, digitRuntime, RuntimeG1.encode,
        inputRuntime, RuntimeG1.ofAffine, RuntimeG1.infinity] using
        HomogeneousRCBG1GroupLaw.selectedInput_positive_eq_encode false
          (inputAffine input)
  | positive =>
      simpa [digitSelector, digitSign, digitRuntime, RuntimeG1.encode,
        inputRuntime, RuntimeG1.ofAffine] using
        HomogeneousRCBG1GroupLaw.selectedInput_positive_eq_encode true
          (inputAffine input)

def curveC : Word := ProjectiveMap.curveC

def rawMap (offset : BN254.G1) (digit : Digit) (input : Input) :
    HomogeneousRCB.Point Word :=
  HomogeneousRCB.formula curveC
    (RuntimeG1.encode (runtimeOfGroup offset))
    (HomogeneousRCB.selectedInput (digitSelector digit) (digitSign digit)
      (RuntimeG1.encode (inputRuntime input)))

def rawCoefficients (offset : BN254.G1) (digit : Digit) :
    ProjectiveMap.Coefficients Word :=
  ProjectiveMap.coefficients curveC
    (RuntimeG1.encode (runtimeOfGroup offset))
    (digitSelector digit) (digitSign digit)

def randomizedCoefficients (offset : BN254.G1) (digit : Digit)
    (randomizer : Wordˣ) : ProjectiveMap.Coefficients Word :=
  (rawCoefficients offset digit).scale (randomizer : Word)

theorem randomizedCoefficients_xX (offset : BN254.G1) (digit : Digit)
    (randomizer : Wordˣ) :
    (randomizedCoefficients offset digit randomizer).xX =
      -(2 * ProjectiveMap.curveC *
        (randomizedCoefficients offset digit randomizer).zYY) := by
  apply ProjectiveMap.scale_xX
  exact ProjectiveMap.coefficients_xX curveC
    (RuntimeG1.encode (runtimeOfGroup offset))
    (digitSelector digit) (digitSign digit)

theorem randomizedCoefficients_zXX (offset : BN254.G1) (digit : Digit)
    (randomizer : Wordˣ) :
    (randomizedCoefficients offset digit randomizer).zXX =
      3 * (randomizedCoefficients offset digit randomizer).xYY := by
  apply ProjectiveMap.scale_zXX
  exact ProjectiveMap.coefficients_zXX curveC
    (RuntimeG1.encode (runtimeOfGroup offset))
    (digitSelector digit) (digitSign digit)

theorem polynomial_randomizedCoefficients (offset : BN254.G1)
    (digit : Digit) (randomizer : Wordˣ) (input : Input) :
    ProjectiveMap.polynomial
        (randomizedCoefficients offset digit randomizer)
        (input.x.val : Word) (input.y.val : Word) =
      ProjectiveMap.Coordinates.ofHomogeneous
        (HomogeneousRCB.randomize (randomizer : Word)
          (rawMap offset digit input)) := by
  rw [randomizedCoefficients, ProjectiveMap.polynomial_scale]
  rw [show ProjectiveMap.polynomial (rawCoefficients offset digit)
      (input.x.val : Word) (input.y.val : Word) =
        ProjectiveMap.Coordinates.ofHomogeneous (rawMap offset digit input) by
    exact ProjectiveMap.polynomial_coefficients curveC
      (RuntimeG1.encode (runtimeOfGroup offset))
      (digitSelector digit) (digitSign digit)
      (input.x.val : Word) (input.y.val : Word)]
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

def offsetAt {hidden : Hidden} (offsets : OffsetFamily.Fiber hidden)
    (index : Fin 161) : BN254.G1 :=
  getFixed offsets.values offsets.length_eq index

def digitAt (hidden : Hidden) (index : Fin 161) : Digit :=
  getFixed (OffsetFamily.digits hidden).values
    (OffsetFamily.digits hidden).length_eq index

def mapHidden (hidden : Hidden) (offsets : OffsetFamily.Fiber hidden)
    (randomizers : Fin 161 → Wordˣ)
    (chainMasks : Fin 161 → ProjectiveMap.ChainMasks Word)
    (index : Fin 161) : ProjectiveMap.Hidden where
  coefficients := randomizedCoefficients (offsetAt offsets index)
    (digitAt hidden index) (randomizers index)
  chainMasks := chainMasks index

/-- Array-backed executable family of map secrets.  `offsetAt` indexes a list,
and `digitAt` both rebuilds and indexes the 161-trit decomposition.  Calling
those accessors independently for every map is quadratic in the map count.
Materializing the two already-fixed-width lists once preserves the exact
proof-level map while making each lookup constant time. -/
def materializedMapHiddenFamily (hidden : Hidden)
    (offsets : OffsetFamily.Fiber hidden)
    (randomizers : Fin 161 → Wordˣ)
    (chainMasks : Fin 161 → ProjectiveMap.ChainMasks Word) :
    Fin 161 → ProjectiveMap.Hidden :=
  let offsetValues : List BN254.G1 := offsets.values
  let packedOffsets : Vector BN254.G1 161 :=
    ⟨offsetValues.toArray, by
      exact offsetValues.size_toArray.trans offsets.length_eq⟩
  let digits := OffsetFamily.digits hidden
  let packedDigits : Vector Digit 161 :=
    ⟨digits.values.toArray, by
      exact digits.values.size_toArray.trans digits.length_eq⟩
  fun index =>
    { coefficients := randomizedCoefficients packedOffsets[index.val]
        packedDigits[index.val] (randomizers index)
      chainMasks := chainMasks index }

@[simp] theorem materializedMapHiddenFamily_apply (hidden : Hidden)
    (offsets : OffsetFamily.Fiber hidden)
    (randomizers : Fin 161 → Wordˣ)
    (chainMasks : Fin 161 → ProjectiveMap.ChainMasks Word)
    (index : Fin 161) :
    materializedMapHiddenFamily hidden offsets randomizers chainMasks index =
      mapHidden hidden offsets randomizers chainMasks index := by
  unfold materializedMapHiddenFamily mapHidden offsetAt digitAt getFixed
  apply ProjectiveMap.Hidden.ext
  · dsimp only
    congr 1
  · rfl

structure Randomness (hidden : Hidden) where
  offsets : OffsetFamily.Fiber hidden
  randomizers : Fin 161 → Wordˣ
  chainMasks : Fin 161 → ProjectiveMap.ChainMasks Word
  tableMasks : Fin 161 → ProjectiveMap.TableKind →
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

def zeroChainMasks : ProjectiveMap.ChainMasks Word where
  shared := 0
  xCross := 0
  xOuter := 0
  yCubic := 0
  yQuadratic := 0
  zSquare := 0
  zCross := 0
  zLinear := 0

def canonicalRandomness (hidden : Hidden) : Randomness hidden :=
  let offsets := OffsetFamily.canonical hidden
  let randomizers : Fin 161 → Wordˣ := fun _ => 1
  let chainMasks : Fin 161 → ProjectiveMap.ChainMasks Word :=
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

/-- Every free oracle coordinate consumed by the Compact construction.  The
derived leading offset and final table-mask entries are deliberately absent. -/
inductive OracleCoordinate where
  | offset (index : Fin 160)
  | randomizer (index : Fin 161)
  | chain (index : Fin 161) (slot : Fin 8)
  | table (index : Fin 161) (kind : ProjectiveMap.TableKind)
      (slot : Fin 253)
  deriving DecidableEq, Fintype

/-- A deterministic, injective purpose assignment internal to this
submission.  It identifies coordinates within one Compact artifact only. -/
def oraclePurpose : OracleCoordinate → Purpose
  | .offset index => index.val
  | .randomizer index => 160 + index.val
  | .chain index slot => 321 + 8 * index.val + slot.val
  | .table index kind slot =>
      1609 + (11 * index.val + kind.index) * 253 + slot.val

private theorem tableKind_index_injective :
    Function.Injective ProjectiveMap.TableKind.index := by
  intro left right hequal
  cases left <;> cases right <;>
    simp only [ProjectiveMap.TableKind.index] at hequal ⊢ <;> omega

theorem oraclePurpose_injective : Function.Injective oraclePurpose := by
  intro left right hequal
  cases left with
  | offset leftIndex =>
      cases right with
      | offset rightIndex =>
          change leftIndex.val = rightIndex.val at hequal
          congr; exact Fin.ext hequal
      | randomizer rightIndex =>
          change leftIndex.val = 160 + rightIndex.val at hequal
          omega
      | chain rightIndex rightSlot =>
          change leftIndex.val = 321 + 8 * rightIndex.val + rightSlot.val at hequal
          omega
      | table rightIndex rightKind rightSlot =>
          change leftIndex.val = 1609 +
            (11 * rightIndex.val + rightKind.index) * 253 + rightSlot.val at hequal
          omega
  | randomizer leftIndex =>
      cases right with
      | offset rightIndex =>
          change 160 + leftIndex.val = rightIndex.val at hequal
          omega
      | randomizer rightIndex =>
          change 160 + leftIndex.val = 160 + rightIndex.val at hequal
          congr; apply Fin.ext; omega
      | chain rightIndex rightSlot =>
          change 160 + leftIndex.val =
            321 + 8 * rightIndex.val + rightSlot.val at hequal
          omega
      | table rightIndex rightKind rightSlot =>
          change 160 + leftIndex.val = 1609 +
            (11 * rightIndex.val + rightKind.index) * 253 + rightSlot.val at hequal
          omega
  | chain leftIndex leftSlot =>
      cases right with
      | offset rightIndex =>
          change 321 + 8 * leftIndex.val + leftSlot.val = rightIndex.val at hequal
          omega
      | randomizer rightIndex =>
          change 321 + 8 * leftIndex.val + leftSlot.val =
            160 + rightIndex.val at hequal
          omega
      | chain rightIndex rightSlot =>
          change 321 + 8 * leftIndex.val + leftSlot.val =
            321 + 8 * rightIndex.val + rightSlot.val at hequal
          have hindex : leftIndex.val = rightIndex.val := by omega
          have hslot : leftSlot.val = rightSlot.val := by omega
          congr <;> apply Fin.ext <;> assumption
      | table rightIndex rightKind rightSlot =>
          change 321 + 8 * leftIndex.val + leftSlot.val = 1609 +
            (11 * rightIndex.val + rightKind.index) * 253 + rightSlot.val at hequal
          omega
  | table leftIndex leftKind leftSlot =>
      cases right with
      | offset rightIndex =>
          change 1609 + (11 * leftIndex.val + leftKind.index) * 253 +
            leftSlot.val = rightIndex.val at hequal
          omega
      | randomizer rightIndex =>
          change 1609 + (11 * leftIndex.val + leftKind.index) * 253 +
            leftSlot.val = 160 + rightIndex.val at hequal
          omega
      | chain rightIndex rightSlot =>
          change 1609 + (11 * leftIndex.val + leftKind.index) * 253 +
            leftSlot.val = 321 + 8 * rightIndex.val + rightSlot.val at hequal
          omega
      | table rightIndex rightKind rightSlot =>
          change 1609 + (11 * leftIndex.val + leftKind.index) * 253 +
            leftSlot.val = 1609 +
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

def offsetPurpose (index : Fin 160) : Purpose :=
  oraclePurpose (.offset index)

def randomizerPurpose (index : Fin 161) : Purpose :=
  oraclePurpose (.randomizer index)

def chainPurpose (index : Fin 161) (slot : Fin 8) : Purpose :=
  oraclePurpose (.chain index slot)

def tableMaskPurpose (index : Fin 161) (kind : ProjectiveMap.TableKind)
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
  (List.finRange 160).map fun index =>
    (scalarSample oracle (offsetPurpose index)).val • standardGenerator

@[simp] theorem sampledOffsetTail_length (oracle : InternalOracle) :
    (sampledOffsetTail oracle).length = 160 := by
  simp [sampledOffsetTail]

def offsetsFromOracle (hidden : Hidden) (oracle : InternalOracle) :
    OffsetFamily.Fiber hidden :=
  let tail := sampledOffsetTail oracle
  { values :=
      (OffsetFamily.qPoint hidden -
        3 • TernaryFullWidth.recompose tail) :: tail
    length_eq := by
      exact (congrArg Nat.succ (sampledOffsetTail_length oracle)).trans rfl
    total_eq := by
      change (OffsetFamily.qPoint hidden -
          3 • TernaryFullWidth.recompose tail) +
        3 • TernaryFullWidth.recompose tail = OffsetFamily.qPoint hidden
      abel }

def chainMasksFromOracle (oracle : InternalOracle) (index : Fin 161) :
    ProjectiveMap.ChainMasks Word where
  shared := wordSample oracle (chainPurpose index 0)
  xCross := wordSample oracle (chainPurpose index 1)
  xOuter := wordSample oracle (chainPurpose index 2)
  yCubic := wordSample oracle (chainPurpose index 3)
  yQuadratic := wordSample oracle (chainPurpose index 4)
  zSquare := wordSample oracle (chainPurpose index 5)
  zCross := wordSample oracle (chainPurpose index 6)
  zLinear := wordSample oracle (chainPurpose index 7)

def tableMaskFree (oracle : InternalOracle) (index : Fin 161)
    (kind : ProjectiveMap.TableKind) (slot : Fin 253) : Word :=
  wordSample oracle (tableMaskPurpose index kind slot)

def tableMaskFiber (constant : Word) (oracle : InternalOracle)
    (index : Fin 161) (kind : ProjectiveMap.TableKind) :
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
    (index : Fin 161) (kind : ProjectiveMap.TableKind) :
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
    (oracle : InternalOracle) (index : Fin 161)
    (kind : ProjectiveMap.TableKind) :
    materializedTableMaskFiber constant oracle index kind =
      tableMaskFiber constant oracle index kind := by
  apply Subtype.ext
  funext slot
  unfold materializedTableMaskFiber tableMaskFiber
  simp [IdealAffineTable.tableWidth, indexedLastCases_eq_lastCases]

def randomnessFromOracle (hidden : Hidden) (oracle : InternalOracle) :
    Randomness hidden :=
  let offsets := offsetsFromOracle hidden oracle
  let randomizers : Fin 161 → Wordˣ := fun index =>
    randomizerSample oracle (randomizerPurpose index)
  let chainMasks : Fin 161 → ProjectiveMap.ChainMasks Word :=
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
    ProjectiveMap.garble index.val (xPairs pairs) (yPairs pairs)
      (mapHidden hidden randomness.offsets randomness.randomizers
        randomness.chainMasks index)
      (fun kind => ⟨randomness.tableMasks index kind,
        randomness.tableMasks_sum index kind⟩)

@[simp] theorem garble_map (hidden : Hidden) (randomness : Randomness hidden)
    (pairs : LabelPairs) (index : Fin 161) :
    (garble hidden randomness pairs).maps index =
      ProjectiveMap.garble index.val (xPairs pairs) (yPairs pairs)
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
def garbleTableWithOracle (index : Fin 161)
    (kind : ProjectiveMap.TableKind)
    (xPairs yPairs : Fin IdealAffineTable.tableWidth → Bool → Label)
    (hidden : ProjectiveMap.Hidden) (oracle : InternalOracle) :
    IdealAffineTable.Table :=
  let params := hidden.params kind
  let masks := materializedTableMaskFiber params.constant oracle index kind
  materializeTable (IdealAffineTable.garble
    (ProjectiveMap.purpose index.val kind)
    (ProjectiveMap.pairsFor xPairs yPairs kind) params masks)

theorem garbleTableWithOracle_eq (index : Fin 161)
    (kind : ProjectiveMap.TableKind)
    (xPairs yPairs : Fin IdealAffineTable.tableWidth → Bool → Label)
    (hidden : ProjectiveMap.Hidden) (oracle : InternalOracle) :
    garbleTableWithOracle index kind xPairs yPairs hidden oracle =
      IdealAffineTable.garble (ProjectiveMap.purpose index.val kind)
        (ProjectiveMap.pairsFor xPairs yPairs kind) (hidden.params kind)
        (tableMaskFiber (hidden.params kind).constant oracle index kind) := by
  unfold garbleTableWithOracle
  rw [materializeTable_eq, materializedTableMaskFiber_eq]

/-- Expose tables on demand.  Each selected table is internally materialized,
but maps do not retain all eleven expanded table objects at once. -/
def garbleMapWithOracle (index : Fin 161)
    (xPairs yPairs : Fin IdealAffineTable.tableWidth → Bool → Label)
    (hidden : ProjectiveMap.Hidden) (oracle : InternalOracle) :
    ProjectiveMap.Artifact :=
  { tables := fun kind =>
      garbleTableWithOracle index kind xPairs yPairs hidden oracle }

@[simp] theorem garbleMapWithOracle_table (index : Fin 161)
    (xPairs yPairs : Fin IdealAffineTable.tableWidth → Bool → Label)
    (hidden : ProjectiveMap.Hidden) (oracle : InternalOracle)
    (kind : ProjectiveMap.TableKind) :
    (garbleMapWithOracle index xPairs yPairs hidden oracle).tables kind =
      garbleTableWithOracle index kind xPairs yPairs hidden oracle := by
  rfl

theorem garbleMapWithOracle_eq (index : Fin 161)
    (xPairs yPairs : Fin IdealAffineTable.tableWidth → Bool → Label)
    (hidden : ProjectiveMap.Hidden) (oracle : InternalOracle) :
    garbleMapWithOracle index xPairs yPairs hidden oracle =
      ProjectiveMap.garble index.val xPairs yPairs hidden
        (fun kind => tableMaskFiber
          (hidden.params kind).constant oracle index kind) := by
  apply ProjectiveMap.Artifact.ext
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
    (oracle : InternalOracle) (pairs : LabelPairs) (index : Fin 161) :
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
  apply FamilyArtifact.Artifact.ext
  funext index
  rw [garbleWithOracle_map, garbleMapWithOracle_eq, garble_map]
  apply congrArg (ProjectiveMap.garble index.val (xPairs pairs) (yPairs pairs)
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

def evaluateMap (index : Fin 161) (artifact : ProjectiveMap.Artifact)
    (input : Input) (labels : ActiveLabels) : Except EvalError Point :=
  ProjectiveMapRuntime.evaluate index.val artifact
    (input.x.val : Word) (input.y.val : Word)
    (xBits input) (yBits input) (xLabels labels) (yLabels labels)

def evaluateMaps (artifact : Artifact) (input : Input)
    (labels : ActiveLabels) : List (Fin 161) → Except EvalError (List Point)
  | [] => .ok []
  | index :: tail => do
      let point ← evaluateMap index (artifact.maps index) input labels
      let points ← evaluateMaps artifact input labels tail
      pure (point :: points)

def evaluate (artifact : Artifact) (input : Input)
    (labels : ActiveLabels) : Except EvalError Profile.Output := do
  let points ← evaluateMaps artifact input labels (List.finRange 161)
  let result ← RuntimeG1.recompose points
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
      digit.value • inputG1 input := by
  cases digit with
  | negative =>
      calc
        RuntimeG1.toPoint (digitRuntime .negative input) =
            -RuntimeG1.toPoint (inputRuntime input) := by
          exact RuntimeG1.toPoint_negAffine (inputAffine input)
            (inputAffine_onCurve input)
        _ = -inputG1 input := congrArg Neg.neg (toPoint_inputRuntime input)
  | zero => rfl
  | positive =>
      simp [digitRuntime, Digit.value, toPoint_inputRuntime]

theorem decode_rawMap (offset : BN254.G1) (digit : Digit) (input : Input) :
    FormulaSemantics.Law.decode (rawMap offset digit input) =
      offset + digit.value • inputG1 input := by
  rw [rawMap_eq_addFormula]
  unfold RuntimeG1.encode
  rw [FormulaSemantics.Law.decode_formula
    (runtimeOfGroup offset).1 (digitRuntime digit input).1
    (runtimeOfGroup offset).2 (digitRuntime digit input).2]
  rw [← RuntimeG1.toPoint_eq_pointOfInput (runtimeOfGroup offset),
    ← RuntimeG1.toPoint_eq_pointOfInput (digitRuntime digit input),
    toPoint_runtimeOfGroup, toPoint_digitRuntime]

theorem mapOutput_eq (offset : BN254.G1) (digit : Digit) (input : Input) :
    TernaryFullWidth.mapOutput offset digit (-inputG1 input) =
      offset + digit.value • inputG1 input := by
  cases digit <;> simp [TernaryFullWidth.mapOutput, Digit.value] <;> abel

def localHidden (offset : BN254.G1) (digit : Digit) (randomizer : Wordˣ)
    (chainMasks : ProjectiveMap.ChainMasks Word) : ProjectiveMap.Hidden where
  coefficients := randomizedCoefficients offset digit randomizer
  chainMasks := chainMasks

theorem evaluateMap_projectiveGarble (offset : BN254.G1) (digit : Digit)
    (randomizer : Wordˣ) (chainMasks : ProjectiveMap.ChainMasks Word)
    (tableMasks : (kind : ProjectiveMap.TableKind) →
      IdealAffineTable.MaskFiber
        ((localHidden offset digit randomizer chainMasks).params kind).constant)
    (pairs : LabelPairs) (input : Input) (index : Fin 161) :
    ∃ result : Point,
      evaluateMap index
          (ProjectiveMap.garble index.val (xPairs pairs) (yPairs pairs)
            (localHidden offset digit randomizer chainMasks) tableMasks)
          input
          (activeLabels pairs input) = Except.ok result ∧
        RuntimeG1.toPoint result =
          TernaryFullWidth.mapOutput offset digit (-inputG1 input) := by
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
      ProjectiveMapRuntime.evaluate index.val
          (ProjectiveMap.garble index.val (xPairs pairs) (yPairs pairs)
            (localHidden offset digit randomizer chainMasks) tableMasks)
          (IdealAffineTable.decodeBits (xBits input))
          (IdealAffineTable.decodeBits (yBits input))
          (xBits input) (yBits input)
          (fun i => xPairs pairs i (xBits input i))
          (fun i => yPairs pairs i (yBits input i)) =
          ProjectiveMapRuntime.normalizeCoordinates
            (ProjectiveMap.polynomial
              (localHidden offset digit randomizer chainMasks).coefficients
              (IdealAffineTable.decodeBits (xBits input))
              (IdealAffineTable.decodeBits (yBits input))) :=
            ProjectiveMapRuntime.evaluate_garble index.val
              (xPairs pairs) (yPairs pairs)
              (localHidden offset digit randomizer chainMasks) tableMasks
              (xBits input) (yBits input)
              (by
                rw [decodeBits_xBits, decodeBits_yBits]
                change ((input.y.val : Word) ^ 2 =
                  (input.x.val : Word) ^ 3 + 3)
                exact input.onCurve)
              (randomizedCoefficients_xX offset digit randomizer)
              (randomizedCoefficients_zXX offset digit randomizer)
      _ = Except.ok result := by
        rw [decodeBits_xBits, decodeBits_yBits]
        unfold ProjectiveMapRuntime.normalizeCoordinates
        rw [show (localHidden offset digit randomizer chainMasks).coefficients =
            randomizedCoefficients offset digit randomizer by rfl,
          hprojective]
        exact hnormalize
  · rw [hresult, decode_rawMap, mapOutput_eq]

theorem evaluateMap_garble (hidden : Hidden) (randomness : Randomness hidden)
    (pairs : LabelPairs) (input : Input) (index : Fin 161) :
    ∃ result : Point,
      evaluateMap index ((garble hidden randomness pairs).maps index) input
          (activeLabels pairs input) = Except.ok result ∧
        RuntimeG1.toPoint result =
          TernaryFullWidth.mapOutput (offsetAt randomness.offsets index)
            (digitAt hidden index) (-inputG1 input) := by
  rw [garble_map]
  exact evaluateMap_projectiveGarble
    (offsetAt randomness.offsets index) (digitAt hidden index)
    (randomness.randomizers index) (randomness.chainMasks index)
    (fun kind => ⟨randomness.tableMasks index kind,
      randomness.tableMasks_sum index kind⟩) pairs input index

theorem evaluateMaps_garble (hidden : Hidden) (randomness : Randomness hidden)
    (pairs : LabelPairs) (input : Input) (indices : List (Fin 161)) :
    ∃ results : List Point,
      evaluateMaps (garble hidden randomness pairs) input
          (activeLabels pairs input) indices = .ok results ∧
        results.map RuntimeG1.toPoint =
          indices.map fun index =>
            TernaryFullWidth.mapOutput (offsetAt randomness.offsets index)
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
    (offsets : OffsetFamily.Fiber hidden) :
    (List.finRange 161).map (offsetAt offsets) = offsets.values := by
  exact map_getFixed_finRange offsets.values offsets.length_eq

private theorem map_finRange_digitAt (hidden : Hidden) :
    (List.finRange 161).map (digitAt hidden) =
      (OffsetFamily.digits hidden).values := by
  exact map_getFixed_finRange (OffsetFamily.digits hidden).values
    (OffsetFamily.digits hidden).length_eq

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
    (offsets : OffsetFamily.Fiber hidden) (input : Input) :
    (List.finRange 161).map (fun index =>
        TernaryFullWidth.mapOutput (offsetAt offsets index)
          (digitAt hidden index) (-inputG1 input)) =
      TernaryFullWidth.mapOutputs offsets.values
        (OffsetFamily.digits hidden).values (-inputG1 input) := by
  unfold TernaryFullWidth.mapOutputs
  rw [← zipWith_map_same
    (fun offset digit => TernaryFullWidth.mapOutput offset digit
      (-inputG1 input)) (offsetAt offsets) (digitAt hidden)]
  rw [map_finRange_offsetAt, map_finRange_digitAt]
  rfl

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
    evaluateMaps_garble hidden randomness pairs input (List.finRange 161)
  obtain ⟨result, hresult, hresultValue⟩ := RuntimeG1.recompose_correct points
  refine ⟨show Profile.Output from RuntimeG1.toOutput result, ?_, ?_⟩
  · unfold evaluate
    rw [hpoints]
    change (do
      let result ← RuntimeG1.recompose points
      pure (RuntimeG1.toOutput result)) = _
    rw [hresult]
    rfl
  · change BN254.CanonicalOutput.toPoint (RuntimeG1.toOutput result) = _
    rw [RuntimeG1.output_toPoint, hresultValue, hpointsValue,
      fullMapOutputs]
    have hsemantic := TernaryFullWidth.output_encodeScalar
      randomness.offsets.values hidden.r (-inputG1 input)
      randomness.offsets.length_eq
    unfold TernaryFullWidth.output at hsemantic
    change TernaryFullWidth.outputList randomness.offsets.values
      (BalancedTernary.encodeScalar hidden.r).values (-inputG1 input) = _
    rw [hsemantic, randomness.offsets.total_eq]
    change Profile.outputEquiv hidden.Q - hidden.r.val • (-input.point) =
      Profile.outputEquiv hidden.Q + hidden.r.val • input.point
    simp

def encodeArtifact : Artifact → ByteArray := FamilyArtifact.encode

/-- Native execution may build the independent map encodings concurrently.
The logical scheme and all privacy proofs continue to see the canonical
sequential encoder. -/
def encodeArtifactParallel : Artifact → ByteArray :=
  FamilyArtifact.encodeParallel

@[csimp] theorem encodeArtifact_eq_parallel :
    encodeArtifact = encodeArtifactParallel := by
  funext artifact
  simp [encodeArtifact, encodeArtifactParallel]

def decodeArtifact (bytes : ByteArray) : Except DecodeError Artifact :=
  match FamilyArtifact.decode 161 bytes with
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
    rw [FamilyArtifact.decode_encode]
  · intro bytes artifact hdecode
    unfold decodeArtifact at hdecode
    cases hfamily : FamilyArtifact.decode 161 bytes with
    | error error =>
        cases error <;> simp [hfamily] at hdecode
    | ok decoded =>
        have hdecoded : decoded = artifact := by simpa [hfamily] using hdecode
        subst decoded
        exact FamilyArtifact.encode_decode hfamily

theorem correct : Correct scheme := by
  apply Scheme.correct_ofFunctions Artifact garbleWithOracle evaluate
    encodeArtifact decodeArtifact codec
  intro hidden oracle pairs input
  rw [garbleWithOracle_eq]
  exact artifactCorrect hidden (randomnessFromOracle hidden oracle) pairs input

def claimedBytes : Nat := 28564459

set_option maxRecDepth 4096 in
theorem artifactBound (hidden : Hidden) (randomness : Randomness hidden)
    (pairs : LabelPairs) :
    (FamilyArtifact.encode (garble hidden randomness pairs)).size ≤
      claimedBytes := by
  rw [FamilyArtifact.encode_size, FamilyArtifact.threadedMask_byteCount]
  rfl

set_option maxRecDepth 4096 in
theorem artifactBoundOracle (hidden : Hidden) (oracle : InternalOracle)
    (pairs : LabelPairs) :
    (scheme.garbleBytes hidden oracle pairs).size ≤ claimedBytes := by
  change (FamilyArtifact.encode
    (garbleWithOracle hidden oracle pairs)).size ≤ _
  rw [garbleWithOracle_eq]
  exact artifactBound hidden (randomnessFromOracle hidden oracle) pairs


end GarblingPrize.Submission.CompactScheme
