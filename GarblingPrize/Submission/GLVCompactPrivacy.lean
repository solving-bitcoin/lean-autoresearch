import GarblingPrize.Submission.GLVCompactOracleLaw
import GarblingPrize.Submission.IdealAffineTablePrivacy

namespace GarblingPrize.Submission.GLVCompactPrivacy

open GarblingPrize.Protected
open GarblingPrize.Submission.EisensteinRadix
open GarblingPrize.Submission.GLVCompactScheme
open GarblingPrize.Submission.GLVCompactOracleLaw
open MeasureTheory ProbabilityTheory

local instance concreteGroup : AddCommGroup BN254.G1 :=
  BN254.bn254.addCommGroup
local instance profileGroup : AddCommGroup Profile.G1 :=
  concreteGroup

private def pointCode : BN254.G1 → Option (BN254.Fq × BN254.Fq)
  | .zero => none
  | .some x y _ => some (x, y)

private theorem pointCode_injective : Function.Injective pointCode := by
  intro left right hequal
  cases left <;> cases right <;> simpa [pointCode] using hequal

instance : Finite BN254.G1 :=
  Finite.of_injective pointCode pointCode_injective

private def chainMasksCode (masks : GLVProjectiveMap.ChainMasks) :
    Fin 8 → Word
  | ⟨0, _⟩ => masks.xLinear
  | ⟨1, _⟩ => masks.xCross
  | ⟨2, _⟩ => masks.xOuter
  | ⟨3, _⟩ => masks.yCubic
  | ⟨4, _⟩ => masks.yQuadratic
  | ⟨5, _⟩ => masks.zCross
  | ⟨6, _⟩ => masks.zCubic
  | ⟨_, _⟩ => masks.zLinear

private theorem chainMasksCode_injective :
    Function.Injective chainMasksCode := by
  intro left right hequal
  apply GLVProjectiveMap.ChainMasks.ext
  · exact congrFun hequal ⟨0, by decide⟩
  · exact congrFun hequal ⟨1, by decide⟩
  · exact congrFun hequal ⟨2, by decide⟩
  · exact congrFun hequal ⟨3, by decide⟩
  · exact congrFun hequal ⟨4, by decide⟩
  · exact congrFun hequal ⟨5, by decide⟩
  · exact congrFun hequal ⟨6, by decide⟩
  · exact congrFun hequal ⟨7, by decide⟩

instance : Finite (GLVProjectiveMap.ChainMasks) :=
  Finite.of_injective chainMasksCode chainMasksCode_injective

private def offsetCode (hidden : Hidden)
    (offsets : GLVOffsetFamily.Fiber hidden) : Fin 91 → BN254.G1 :=
  fun index => getFixed offsets.values offsets.length_eq index

private theorem offsetCode_injective (hidden : Hidden) :
    Function.Injective (offsetCode hidden) := by
  intro left right hequal
  apply GLVOffsetFamily.Fiber.ext
  rw [← map_getFixed_finRange left.values left.length_eq,
    ← map_getFixed_finRange right.values right.length_eq]
  exact congrArg (fun values => (List.finRange 91).map values) hequal

instance (hidden : Hidden) : Finite (GLVOffsetFamily.Fiber hidden) :=
  Finite.of_injective (offsetCode hidden) (offsetCode_injective hidden)

def targetOffsets (input : Input) (source target : Hidden)
    (hequal : reference Profile source input = reference Profile target input)
    (offsets : GLVOffsetFamily.Fiber source) : GLVOffsetFamily.Fiber target :=
  GLVOffsetFamily.equiv input source target hequal offsets

theorem mapOutput_preserved (input : Input) (source target : Hidden)
    (hequal : reference Profile source input = reference Profile target input)
    (offsets : GLVOffsetFamily.Fiber source) (index : Fin 91) :
    EisensteinFullWidth.mapOutput (offsetAt (targetOffsets input source target
        hequal offsets) index) (digitAt target index) (-inputG1 input) =
      EisensteinFullWidth.mapOutput (offsetAt offsets index)
        (digitAt source index) (-inputG1 input) := by
  have family := GLVOffsetFamily.selectedOutputs_preserved input source target
    hequal offsets
  have indexed :
      (List.finRange 91).map (fun index =>
          EisensteinFullWidth.mapOutput
            (offsetAt (targetOffsets input source target hequal offsets) index)
            (digitAt target index) (-inputG1 input)) =
        (List.finRange 91).map (fun index =>
          EisensteinFullWidth.mapOutput (offsetAt offsets index)
            (digitAt source index) (-inputG1 input)) := by
    rw [fullMapOutputs, fullMapOutputs]
    change EisensteinFullWidth.mapOutputs
        (targetOffsets input source target hequal offsets).values
        (GLVOffsetFamily.digits target) (-inputG1 input) =
      EisensteinFullWidth.mapOutputs offsets.values
        (GLVOffsetFamily.digits source) (-inputG1 input)
    exact family
  exact pointwise_of_finRange_map_eq _ _ indexed index

theorem rawMap_wellFormed (offset : BN254.G1) (digit : Digit)
    (input : Input) :
    RepresentativeAlignment.WellFormed (rawMap offset digit input) := by
  rw [rawMap_eq_addFormula]
  exact FormulaSemantics.Law.formula_wellFormed
    (runtimeOfGroup offset).1 (digitRuntime digit input).1
    (runtimeOfGroup offset).2 (digitRuntime digit input).2

theorem rawMap_decode_eq (input : Input) (source target : Hidden)
    (hequal : reference Profile source input = reference Profile target input)
    (offsets : GLVOffsetFamily.Fiber source) (index : Fin 91) :
    FormulaSemantics.Law.decode
        (rawMap (offsetAt offsets index) (digitAt source index) input) =
      FormulaSemantics.Law.decode
        (rawMap (offsetAt (targetOffsets input source target hequal offsets)
          index) (digitAt target index) input) := by
  rw [decode_rawMap, decode_rawMap]
  rw [← mapOutput_eq, ← mapOutput_eq]
  exact (mapOutput_preserved input source target hequal offsets index).symm

theorem rawMap_normalize_eq (input : Input) (source target : Hidden)
    (hequal : reference Profile source input = reference Profile target input)
    (offsets : GLVOffsetFamily.Fiber source) (index : Fin 91) :
    RepresentativeAlignment.normalize
        (rawMap (offsetAt offsets index) (digitAt source index) input) =
      RepresentativeAlignment.normalize
        (rawMap (offsetAt (targetOffsets input source target hequal offsets)
          index) (digitAt target index) input) := by
  apply FormulaSemantics.Law.normalize_eq_of_decode_eq
    (rawMap_valid _ _ _) (rawMap_valid _ _ _)
  exact rawMap_decode_eq input source target hequal offsets index

def targetRandomizer (input : Input) (source target : Hidden)
    (hequal : reference Profile source input = reference Profile target input)
    (offsets : GLVOffsetFamily.Fiber source) (index : Fin 91)
    (randomizer : Wordˣ) : Wordˣ :=
  RepresentativeAlignment.randomizerEquiv
    (rawMap (offsetAt offsets index) (digitAt source index) input)
    (rawMap (offsetAt (targetOffsets input source target hequal offsets) index)
      (digitAt target index) input)
    (rawMap_wellFormed _ _ _) (rawMap_wellFormed _ _ _)
    (rawMap_normalize_eq input source target hequal offsets index) randomizer

theorem randomizedPolynomial_preserved (input : Input)
    (source target : Hidden)
    (hequal : reference Profile source input = reference Profile target input)
    (offsets : GLVOffsetFamily.Fiber source) (index : Fin 91)
    (randomizer : Wordˣ) :
    ProjectiveMap.polynomial
        (randomizedCoefficients
          (offsetAt (targetOffsets input source target hequal offsets) index)
          (digitAt target index)
          (targetRandomizer input source target hequal offsets index randomizer))
        (input.x.val : Word) (input.y.val : Word) =
      ProjectiveMap.polynomial
        (randomizedCoefficients (offsetAt offsets index)
          (digitAt source index) randomizer)
        (input.x.val : Word) (input.y.val : Word) := by
  rw [polynomial_randomizedCoefficients,
    polynomial_randomizedCoefficients]
  apply congrArg ProjectiveMap.Coordinates.ofHomogeneous
  exact RepresentativeAlignment.randomize_randomizerEquiv
    (rawMap (offsetAt offsets index) (digitAt source index) input)
    (rawMap (offsetAt (targetOffsets input source target hequal offsets) index)
      (digitAt target index) input)
    (rawMap_wellFormed _ _ _) (rawMap_wellFormed _ _ _)
    (rawMap_normalize_eq input source target hequal offsets index) randomizer

/-- A finite BN254 G1 input cannot have `x = 0`: its curve equation would
make the certified quadratic non-residue `3` a square. -/
theorem inputX_ne_zero (input : Input) : (input.x.val : Word) ≠ 0 := by
  intro hx
  apply HomogeneousRCBG1GroupLaw.three_not_square (input.y.val : Word)
  have hcurve : (input.y.val : Word) ^ 2 =
      (input.x.val : Word) ^ 3 + 3 :=
    (inputAffine_onCurve input).symm
  simpa [hx] using hcurve

def targetChainMasks (input : Input) (source target : Hidden)
    (hequal : reference Profile source input = reference Profile target input)
    (offsets : GLVOffsetFamily.Fiber source) (randomizers : Fin 91 → Wordˣ)
    (chainMasks : Fin 91 → GLVProjectiveMap.ChainMasks)
    (index : Fin 91) : GLVProjectiveMap.ChainMasks :=
  GLVProjectiveMapPrivacy.chainMaskEquiv
    (randomizedCoefficients (offsetAt offsets index)
      (digitAt source index) (randomizers index))
    (randomizedCoefficients
      (offsetAt (targetOffsets input source target hequal offsets) index)
      (digitAt target index)
      (targetRandomizer input source target hequal offsets index
        (randomizers index)))
    (input.x.val : Word) (input.y.val : Word) (inputX_ne_zero input)
    (chainMasks index)

def bitsFor (kind : GLVProjectiveMap.TableKind) (input : Input) :
    Fin IdealAffineTable.tableWidth → Bool :=
  match kind with
  | .xLinear | .xCross | .yCubic | .yQuadratic | .yLinear |
      .zCross | .zCubic =>
      xBits input
  | .xOuter | .xCorrection | .zLinear | .zOuter =>
      yBits input

theorem decodeBits_bitsFor (kind : GLVProjectiveMap.TableKind) (input : Input) :
    IdealAffineTable.decodeBits (bitsFor kind input) =
      GLVProjectiveMapPrivacy.tableInput kind
        (input.x.val : Word) (input.y.val : Word) := by
  cases kind <;>
    simp [bitsFor, GLVProjectiveMapPrivacy.tableInput, decodeBits_xBits,
      decodeBits_yBits]

theorem tableOutput_preserved (input : Input) (source target : Hidden)
    (hequal : reference Profile source input = reference Profile target input)
    (offsets : GLVOffsetFamily.Fiber source) (randomizers : Fin 91 → Wordˣ)
    (chainMasks : Fin 91 → GLVProjectiveMap.ChainMasks)
    (index : Fin 91) (kind : GLVProjectiveMap.TableKind) :
    let sourceMap := mapHidden source offsets randomizers chainMasks index
    let targetMap := mapHidden target
      (targetOffsets input source target hequal offsets)
      (fun index => targetRandomizer input source target hequal offsets index
        (randomizers index))
      (targetChainMasks input source target hequal offsets randomizers chainMasks)
      index
    (sourceMap.params kind).coefficient *
          IdealAffineTable.decodeBits (bitsFor kind input) +
        (sourceMap.params kind).constant =
      (targetMap.params kind).coefficient *
          IdealAffineTable.decodeBits (bitsFor kind input) +
        (targetMap.params kind).constant := by
  dsimp only
  rw [decodeBits_bitsFor]
  symm
  apply GLVProjectiveMapPrivacy.params_output_chainMaskEquiv
  · exact (randomizedPolynomial_preserved input source target hequal offsets
      index (randomizers index)).symm
  · exact input.onCurve

def targetTableMasks (input : Input) (source target : Hidden)
    (hequal : reference Profile source input = reference Profile target input)
    (offsets : GLVOffsetFamily.Fiber source) (randomizers : Fin 91 → Wordˣ)
    (chainMasks : Fin 91 → GLVProjectiveMap.ChainMasks)
    (tableMasks : Fin 91 → GLVProjectiveMap.TableKind →
      Fin IdealAffineTable.tableWidth → Word)
    (tableMasks_sum : ∀ index kind, ∑ i, tableMasks index kind i =
      ((mapHidden source offsets randomizers chainMasks index).params kind).constant)
    (index : Fin 91) (kind : GLVProjectiveMap.TableKind) :=
  IdealAffineTablePrivacy.maskEquiv
    ((mapHidden source offsets randomizers chainMasks index).params kind)
    ((mapHidden target
      (targetOffsets input source target hequal offsets)
      (fun index => targetRandomizer input source target hequal offsets index
        (randomizers index))
      (targetChainMasks input source target hequal offsets randomizers chainMasks)
      index).params kind)
    (bitsFor kind input)
    (tableOutput_preserved input source target hequal offsets randomizers
      chainMasks index kind)
    (⟨tableMasks index kind, tableMasks_sum index kind⟩ :
      IdealAffineTable.MaskFiber
        ((mapHidden source offsets randomizers chainMasks index).params kind).constant)

def targetRandomness (input : Input) (source target : Hidden)
    (hequal : reference Profile source input = reference Profile target input)
    (randomness : Randomness source) : Randomness target where
  offsets := targetOffsets input source target hequal randomness.offsets
  randomizers := fun index =>
    targetRandomizer input source target hequal randomness.offsets index
      (randomness.randomizers index)
  chainMasks := targetChainMasks input source target hequal randomness.offsets
    randomness.randomizers randomness.chainMasks
  tableMasks := fun index kind =>
    (targetTableMasks input source target hequal randomness.offsets
      randomness.randomizers randomness.chainMasks randomness.tableMasks
      randomness.tableMasks_sum index kind).1
  tableMasks_sum := fun index kind =>
    (targetTableMasks input source target hequal randomness.offsets
      randomness.randomizers randomness.chainMasks randomness.tableMasks
      randomness.tableMasks_sum index kind).2

@[simp] theorem targetOffsets_swapped (input : Input) (source target : Hidden)
    (hequal : reference Profile source input = reference Profile target input)
    (offsets : GLVOffsetFamily.Fiber source) :
    targetOffsets input target source hequal.symm
        (targetOffsets input source target hequal offsets) = offsets := by
  exact (GLVOffsetFamily.equiv input source target hequal).left_inv offsets

theorem targetRandomizer_swapped (input : Input) (source target : Hidden)
    (hequal : reference Profile source input = reference Profile target input)
    (offsets : GLVOffsetFamily.Fiber source) (index : Fin 91)
    (randomizer : Wordˣ) :
    targetRandomizer input target source hequal.symm
        (targetOffsets input source target hequal offsets) index
        (targetRandomizer input source target hequal offsets index randomizer) =
      randomizer := by
  unfold targetRandomizer
  simp only [targetOffsets_swapped]
  let sourceRaw := rawMap (offsetAt offsets index) (digitAt source index) input
  let targetRaw := rawMap
    (offsetAt (targetOffsets input source target hequal offsets) index)
    (digitAt target index) input
  let sourceWell := rawMap_wellFormed (offsetAt offsets index)
    (digitAt source index) input
  let targetWell := rawMap_wellFormed
    (offsetAt (targetOffsets input source target hequal offsets) index)
    (digitAt target index) input
  let normalized := rawMap_normalize_eq input source target hequal offsets index
  change RepresentativeAlignment.randomizerEquiv targetRaw sourceRaw
      targetWell sourceWell normalized.symm
      (RepresentativeAlignment.randomizerEquiv sourceRaw targetRaw
        sourceWell targetWell normalized randomizer) = randomizer
  rw [← RepresentativeAlignment.randomizerEquiv_symm_apply_eq_swapped
    sourceRaw targetRaw sourceWell targetWell normalized]
  exact (RepresentativeAlignment.randomizerEquiv sourceRaw targetRaw
    sourceWell targetWell normalized).left_inv randomizer

theorem targetChainMasks_swapped (input : Input) (source target : Hidden)
    (hequal : reference Profile source input = reference Profile target input)
    (offsets : GLVOffsetFamily.Fiber source) (randomizers : Fin 91 → Wordˣ)
    (chainMasks : Fin 91 → GLVProjectiveMap.ChainMasks) :
    targetChainMasks input target source hequal.symm
        (targetOffsets input source target hequal offsets)
        (fun index => targetRandomizer input source target hequal offsets index
          (randomizers index))
        (targetChainMasks input source target hequal offsets randomizers
          chainMasks) = chainMasks := by
  funext index
  unfold targetChainMasks
  simp only [targetOffsets_swapped]
  rw [show targetRandomizer input target source hequal.symm
      (targetOffsets input source target hequal offsets) index
      (targetRandomizer input source target hequal offsets index
        (randomizers index)) = randomizers index by
    exact targetRandomizer_swapped input source target hequal offsets index
      (randomizers index)]
  exact GLVProjectiveMapPrivacy.translateMasks_source_target_source
    _ _ _ _ (inputX_ne_zero input) _

theorem targetRandomness_swapped (input : Input) (source target : Hidden)
    (hequal : reference Profile source input = reference Profile target input)
    (randomness : Randomness source) :
    targetRandomness input target source hequal.symm
        (targetRandomness input source target hequal randomness) = randomness := by
  let round := targetRandomness input target source hequal.symm
    (targetRandomness input source target hequal randomness)
  have hoffsets : round.offsets = randomness.offsets :=
    targetOffsets_swapped input source target hequal randomness.offsets
  have hrandomizers : round.randomizers = randomness.randomizers := by
    funext index
    exact targetRandomizer_swapped input source target hequal randomness.offsets
      index (randomness.randomizers index)
  have hchains : round.chainMasks = randomness.chainMasks :=
    targetChainMasks_swapped input source target hequal
      randomness.offsets randomness.randomizers randomness.chainMasks
  have htables : round.tableMasks = randomness.tableMasks := by
    funext index kind maskIndex
    let sourceParams :=
      (mapHidden source randomness.offsets randomness.randomizers
        randomness.chainMasks index).params kind
    let middle := targetRandomness input source target hequal randomness
    let middleParams :=
      (mapHidden target middle.offsets middle.randomizers middle.chainMasks
        index).params kind
    let roundParams :=
      (mapHidden source round.offsets round.randomizers round.chainMasks
        index).params kind
    have hroundParams : roundParams = sourceParams := by
      simp only [roundParams, sourceParams, hoffsets, hrandomizers, hchains]
    have hsourceMiddle :
        sourceParams.coefficient *
              IdealAffineTable.decodeBits (bitsFor kind input) +
            sourceParams.constant =
          middleParams.coefficient *
              IdealAffineTable.decodeBits (bitsFor kind input) +
            middleParams.constant := by
      exact tableOutput_preserved input source target hequal
        randomness.offsets randomness.randomizers randomness.chainMasks
        index kind
    have hmiddleRound :
        middleParams.coefficient *
              IdealAffineTable.decodeBits (bitsFor kind input) +
            middleParams.constant =
          roundParams.coefficient *
              IdealAffineTable.decodeBits (bitsFor kind input) +
            roundParams.constant := by
      rw [hroundParams]
      exact hsourceMiddle.symm
    change ((IdealAffineTablePrivacy.maskEquiv middleParams roundParams
        (bitsFor kind input) hmiddleRound)
      ((IdealAffineTablePrivacy.maskEquiv sourceParams middleParams
        (bitsFor kind input) hsourceMiddle)
        (⟨randomness.tableMasks index kind,
          randomness.tableMasks_sum index kind⟩ :
          IdealAffineTable.MaskFiber sourceParams.constant))).1 maskIndex =
      randomness.tableMasks index kind maskIndex
    dsimp only [IdealAffineTablePrivacy.maskEquiv]
    unfold IdealAffineTablePrivacy.transformMask
    change (randomness.tableMasks index kind maskIndex +
          IdealAffineTable.weight maskIndex *
            (sourceParams.coefficient - middleParams.coefficient) *
            IdealAffineTable.bitWord (bitsFor kind input maskIndex)) +
        IdealAffineTable.weight maskIndex *
          (middleParams.coefficient - roundParams.coefficient) *
          IdealAffineTable.bitWord (bitsFor kind input maskIndex) =
      randomness.tableMasks index kind maskIndex
    linear_combination
      -(IdealAffineTable.weight maskIndex *
        IdealAffineTable.bitWord (bitsFor kind input maskIndex)) *
      congrArg IdealAffineTable.Params.coefficient hroundParams
  exact Randomness.ext round randomness hoffsets hrandomizers hchains htables

def randomnessEquiv (input : Input) (source target : Hidden)
    (hequal : reference Profile source input = reference Profile target input) :
    Randomness source ≃ Randomness target where
  toFun := targetRandomness input source target hequal
  invFun := targetRandomness input target source hequal.symm
  left_inv := targetRandomness_swapped input source target hequal
  right_inv := targetRandomness_swapped input target source hequal.symm

theorem randomnessEquiv_measurePreserving (input : Input)
    (source target : Hidden)
    (hequal : reference Profile source input = reference Profile target input) :
    MeasureTheory.MeasurePreserving
      (randomnessEquiv input source target hequal)
      (randomnessLaw source) (randomnessLaw target) := by
  unfold randomnessLaw
  exact measurePreserving_uniformOfFiniteEquiv
    (randomnessEquiv input source target hequal)

def tableKindOfIndex (index : Fin 11) : GLVProjectiveMap.TableKind :=
  GLVProjectiveMap.tableKindAt index

theorem tableKindOfIndex_index (kind : GLVProjectiveMap.TableKind) :
    tableKindOfIndex kind.finIndex = kind := by
  exact GLVProjectiveMap.tableKindAt_finIndex kind

def tableOwner (purpose : Purpose) :
    Option (Fin 91 × GLVProjectiveMap.TableKind) :=
  if hbound : purpose < 11 * 91 then
    let index : Fin 91 := ⟨purpose / 11, by
      rw [Nat.div_lt_iff_lt_mul (by decide)]
      simpa [Nat.mul_comm] using hbound⟩
    let kindIndex : Fin 11 := ⟨purpose % 11, Nat.mod_lt _ (by omega)⟩
    some (index, tableKindOfIndex kindIndex)
  else
    none

theorem tableOwner_encoded (index : Fin 91) (kindIndex : Fin 11) :
    tableOwner (11 * index.val + kindIndex.val) =
      some (index, tableKindOfIndex kindIndex) := by
  have hbound : 11 * index.val + kindIndex.val < 11 * 91 := by
    have hi := index.isLt
    have hk := kindIndex.isLt
    omega
  unfold tableOwner
  rw [dif_pos hbound]
  have hdiv : (11 * index.val + kindIndex.val) / 11 = index.val := by
    rw [Nat.mul_add_div (by decide)]
    simp [Nat.div_eq_of_lt kindIndex.isLt]
  have hmod : (11 * index.val + kindIndex.val) % 11 = kindIndex.val := by
    rw [Nat.mul_add_mod]
    exact Nat.mod_eq_of_lt kindIndex.isLt
  have hindexFin :
      (⟨(11 * index.val + kindIndex.val) / 11, by
        rw [hdiv]
        exact index.isLt⟩ : Fin 91) = index := Fin.ext hdiv
  have hkindFin :
      (⟨(11 * index.val + kindIndex.val) % 11, by
        rw [hmod]
        exact kindIndex.isLt⟩ : Fin 11) = kindIndex := Fin.ext hmod
  dsimp only
  rw [hindexFin, hkindFin]

@[simp] theorem tableOwner_purpose (index : Fin 91)
    (kind : GLVProjectiveMap.TableKind) :
    tableOwner (GLVProjectiveMap.purpose index.val kind) = some (index, kind) := by
  unfold GLVProjectiveMap.purpose
  calc
    tableOwner (11 * index.val + kind.index) =
        some (index, tableKindOfIndex kind.finIndex) :=
      tableOwner_encoded index kind.finIndex
    _ = some (index, kind) := by rw [tableKindOfIndex_index]

def kindUsesX : GLVProjectiveMap.TableKind → Bool
  | .xLinear | .xCross | .yCubic | .yQuadratic | .yLinear |
      .zCross | .zCubic => true
  | .xOuter | .xCorrection | .zLinear | .zOuter => false

def tableWire (kind : GLVProjectiveMap.TableKind)
    (index : Fin IdealAffineTable.tableWidth) : BitIndex :=
  if kindUsesX kind then xWire index else yWire index

theorem inputBit_tableWire (kind : GLVProjectiveMap.TableKind) (input : Input)
    (index : Fin IdealAffineTable.tableWidth) :
    inputBit input (tableWire kind index) = bitsFor kind input index := by
  have hindex := index.isLt
  have hindex256 : index.val < coordinateWidth := by
    norm_num [IdealAffineTable.tableWidth, coordinateWidth] at hindex ⊢
    omega
  have hnot256 : ¬ 256 ≤ index.val := by
    norm_num [coordinateWidth] at hindex256
    omega
  cases kind <;>
    simp [tableWire, kindUsesX, bitsFor, inputBit, xWire, yWire, xBits,
      yBits, coordinateWidth, hnot256]

/-- The finite set of label-pad coordinates read while constructing one
artifact. The complete active-label oracle remains outside this projection. -/
abbrev ArtifactPads :=
  BitIndex → Bool → Fin (11 * 91) → IdealAffineTable.WordBytes

def artifactPads (pairs : LabelPairs) : ArtifactPads :=
  fun wire bit purpose => pairs wire bit purpose.val

def expandArtifactPads (pads : ArtifactPads) : LabelPairs :=
  fun wire bit purpose =>
    if hpurpose : purpose < 11 * 91 then
      pads wire bit ⟨purpose, hpurpose⟩
    else
      Bytes.zero labelByteCount

theorem artifactPads_measurable : Measurable artifactPads := by
  apply measurable_pi_lambda
  intro wire
  apply measurable_pi_lambda
  intro bit
  apply measurable_pi_lambda
  intro purpose
  unfold artifactPads
  fun_prop

@[simp] theorem expandArtifactPads_artifactPads (pairs : LabelPairs)
    (wire : BitIndex) (bit : Bool) (purpose : Purpose)
    (hpurpose : purpose < 11 * 91) :
    expandArtifactPads (artifactPads pairs) wire bit purpose =
      pairs wire bit purpose := by
  simp [expandArtifactPads, artifactPads, hpurpose]

theorem garble_expandArtifactPads_artifactPads (hidden : Hidden)
    (randomness : Randomness hidden) (pairs : LabelPairs) :
    garble hidden randomness (expandArtifactPads (artifactPads pairs)) =
      garble hidden randomness pairs := by
  apply GLVFamilyArtifact.Artifact.ext
  funext mapIndex
  apply GLVProjectiveMap.Artifact.ext
  funext kind
  apply IdealAffineTable.Table.ext
  funext pair
  have hpurpose : GLVProjectiveMap.purpose mapIndex.val kind < 11 * 91 := by
    have hmap := mapIndex.isLt
    have hkind : kind.index < 11 := by cases kind <;> decide
    unfold GLVProjectiveMap.purpose
    calc
      11 * mapIndex.val + kind.index < 11 * (mapIndex.val + 1) := by omega
      _ ≤ 11 * 91 := Nat.mul_le_mul_left 11 (by omega)
  unfold garble GLVProjectiveMap.garble IdealAffineTable.garble
  apply congrArg IdealAffineTable.packCiphertexts
  unfold IdealAffineTable.materializeCiphertexts
  apply congrArg Vector.ofFn
  funext slot
  unfold IdealAffineTable.ciphertextForSlot
  cases kind <;>
    simp [GLVProjectiveMap.pairsFor, xPairs, yPairs, hpurpose]

def tableIndex (kind : GLVProjectiveMap.TableKind) (wire : BitIndex) :
    Option (Fin IdealAffineTable.tableWidth) :=
  if kindUsesX kind then
    if hwire : wire.val < IdealAffineTable.tableWidth then
      some ⟨wire.val, hwire⟩
    else none
  else if _hwire : coordinateWidth ≤ wire.val then
    if htable : wire.val - coordinateWidth < IdealAffineTable.tableWidth then
      some ⟨wire.val - coordinateWidth, htable⟩
    else none
  else none

@[simp] theorem tableIndex_tableWire (kind : GLVProjectiveMap.TableKind)
    (index : Fin IdealAffineTable.tableWidth) :
    tableIndex kind (tableWire kind index) = some index := by
  have hindex : index.val < 254 := by
    simpa [IdealAffineTable.tableWidth] using index.isLt
  cases kind <;>
    simp [tableIndex, tableWire, kindUsesX, xWire, yWire, coordinateWidth,
      IdealAffineTable.tableWidth, hindex] <;> congr

def payloadAt (hidden : Hidden) (randomness : Randomness hidden)
    (wire : BitIndex) (bit : Bool) (purpose : Purpose) :
    IdealAffineTable.WordBytes :=
  match tableOwner purpose with
  | none => Bytes.zero 32
  | some (index, kind) =>
      match tableIndex kind wire with
      | none => Bytes.zero 32
      | some tableIndex =>
          IdealAffineTablePrivacy.payload
            ((mapHidden hidden randomness.offsets randomness.randomizers
              randomness.chainMasks index).params kind)
            (randomness.tableMasks index kind) tableIndex bit

@[simp] theorem payloadAt_tableWire (hidden : Hidden)
    (randomness : Randomness hidden) (mapIndex : Fin 91)
    (kind : GLVProjectiveMap.TableKind) (index : Fin IdealAffineTable.tableWidth)
    (bit : Bool) :
    payloadAt hidden randomness (tableWire kind index) bit
        (GLVProjectiveMap.purpose mapIndex.val kind) =
      IdealAffineTablePrivacy.payload
        ((mapHidden hidden randomness.offsets randomness.randomizers
          randomness.chainMasks mapIndex).params kind)
        (randomness.tableMasks mapIndex kind) index bit := by
  simp [payloadAt]

def transformPairs (input : Input) (source target : Hidden)
    (sourceRandomness : Randomness source)
    (targetRandomness : Randomness target) (pairs : LabelPairs) : LabelPairs :=
  fun wire bit purpose =>
    if bit = inputBit input wire then
      pairs wire bit purpose
    else
      IdealAffineTablePrivacy.translatePad
        (payloadAt source sourceRandomness wire bit purpose)
        (payloadAt target targetRandomness wire bit purpose)
        (pairs wire bit purpose)

def translatePadEquiv (oldPayload newPayload : IdealAffineTable.WordBytes) :
    IdealAffineTable.WordBytes ≃ IdealAffineTable.WordBytes where
  toFun := IdealAffineTablePrivacy.translatePad oldPayload newPayload
  invFun := IdealAffineTablePrivacy.translatePad newPayload oldPayload
  left_inv := IdealAffineTablePrivacy.translatePad_source_target_source
    oldPayload newPayload
  right_inv := IdealAffineTablePrivacy.translatePad_source_target_source
    newPayload oldPayload

noncomputable def translatePadMeasurableEquiv
    (oldPayload newPayload : IdealAffineTable.WordBytes) :
    IdealAffineTable.WordBytes ≃ᵐ IdealAffineTable.WordBytes where
  toEquiv := translatePadEquiv oldPayload newPayload
  measurable_toFun := Measurable.of_discrete
  measurable_invFun := Measurable.of_discrete

theorem translatePad_measurePreserving
    (oldPayload newPayload : IdealAffineTable.WordBytes) :
    MeasureTheory.MeasurePreserving
      (IdealAffineTablePrivacy.translatePad oldPayload newPayload)
      seedLabelLaw seedLabelLaw := by
  unfold seedLabelLaw
  exact measurePreserving_uniformOfFiniteEquiv
    (translatePadEquiv oldPayload newPayload)

theorem transformPairs_measurable (input : Input) (source target : Hidden)
    (sourceRandomness : Randomness source)
    (targetRandomness : Randomness target) :
    Measurable
      (transformPairs input source target sourceRandomness targetRandomness) := by
  apply measurable_pi_lambda
  intro wire
  apply measurable_pi_lambda
  intro bit
  apply measurable_pi_lambda
  intro purpose
  by_cases hselected : bit = inputBit input wire
  · simp only [transformPairs, hselected, if_true]
    fun_prop
  · simp only [transformPairs, hselected, if_false]
    exact Measurable.of_discrete.comp (by fun_prop)

theorem transformPairs_preservesLaw (input : Input) (source target : Hidden)
    (sourceRandomness : Randomness source)
    (targetRandomness : Randomness target) :
    Measure.map
        (transformPairs input source target sourceRandomness targetRandomness)
        labelPairsLaw = labelPairsLaw := by
  apply labelPairsLaw_map_coordinatewise
    (fun wire bit purpose pad =>
      if bit = inputBit input wire then pad
      else IdealAffineTablePrivacy.translatePad
        (payloadAt source sourceRandomness wire bit purpose)
        (payloadAt target targetRandomness wire bit purpose) pad)
  · intro wire bit purpose
    exact Measurable.of_discrete
  · intro wire bit purpose
    by_cases hselected : bit = inputBit input wire
    · simp only [hselected, if_true]
      exact Measure.map_id
    · simp only [hselected, if_false]
      exact translatePad_measurePreserving _ _ |>.map_eq

theorem transformPairs_joint_measurable (input : Input)
    (source target : Hidden)
    (hequal : reference Profile source input = reference Profile target input) :
    Measurable (fun state : Randomness source × LabelPairs =>
      transformPairs input source target state.1
        (targetRandomness input source target hequal state.1) state.2) := by
  apply measurable_pi_lambda
  intro wire
  apply measurable_pi_lambda
  intro bit
  apply measurable_pi_lambda
  intro purpose
  by_cases hselected : bit = inputBit input wire
  · simp only [transformPairs, hselected, if_true]
    fun_prop
  · simp only [transformPairs, hselected, if_false]
    have hsourceRandomness : Measurable (fun randomness : Randomness source =>
        payloadAt source randomness wire bit purpose) :=
      Measurable.of_discrete
    have hsource : Measurable (fun state : Randomness source × LabelPairs =>
        payloadAt source state.1 wire bit purpose) :=
      hsourceRandomness.comp measurable_fst
    have htargetRandomness : Measurable (fun randomness : Randomness source =>
        payloadAt target
          (targetRandomness input source target hequal randomness)
          wire bit purpose) :=
      Measurable.of_discrete
    have htarget : Measurable (fun state : Randomness source × LabelPairs =>
        payloadAt target
          (targetRandomness input source target hequal state.1)
          wire bit purpose) :=
      htargetRandomness.comp measurable_fst
    have hpad : Measurable (fun state : Randomness source × LabelPairs =>
        state.2 wire bit purpose) := by fun_prop
    have hop : Measurable
        (fun values : (IdealAffineTable.WordBytes ×
            IdealAffineTable.WordBytes) × IdealAffineTable.WordBytes =>
          IdealAffineTablePrivacy.translatePad values.1.1 values.1.2
            values.2) :=
      measurable_of_finite _
    have hvalues : Measurable
        (fun state : Randomness source × LabelPairs =>
          ((payloadAt source state.1 wire bit purpose,
            payloadAt target
              (targetRandomness input source target hequal state.1)
              wire bit purpose), state.2 wire bit purpose)) :=
      (hsource.prodMk htarget).prodMk hpad
    change Measurable
      ((fun values : (IdealAffineTable.WordBytes ×
          IdealAffineTable.WordBytes) × IdealAffineTable.WordBytes =>
        IdealAffineTablePrivacy.translatePad values.1.1 values.1.2 values.2) ∘
      (fun state : Randomness source × LabelPairs =>
        ((payloadAt source state.1 wire bit purpose,
          payloadAt target
            (targetRandomness input source target hequal state.1)
            wire bit purpose), state.2 wire bit purpose)))
    exact hop.comp hvalues

theorem productChange_measurePreserving (input : Input)
    (source target : Hidden)
    (hequal : reference Profile source input = reference Profile target input) :
    MeasureTheory.MeasurePreserving
      (fun state : Randomness source × LabelPairs =>
        (targetRandomness input source target hequal state.1,
          transformPairs input source target state.1
            (targetRandomness input source target hequal state.1) state.2))
      ((randomnessLaw source).prod labelPairsLaw)
      ((randomnessLaw target).prod labelPairsLaw) := by
  let hsSource : SFinite (randomnessLaw source) := by
    change SFinite (uniformOn Set.univ : Measure (Randomness source))
    infer_instance
  exact @MeasurePreserving.skew_product
    (Randomness source) (Randomness target) LabelPairs
    (inferInstance : MeasurableSpace (Randomness source))
    (inferInstance : MeasurableSpace (Randomness target))
    (inferInstance : MeasurableSpace LabelPairs)
    LabelPairs (inferInstance : MeasurableSpace LabelPairs)
    (randomnessLaw source) (randomnessLaw target)
    labelPairsLaw labelPairsLaw hsSource (by infer_instance)
    (randomnessEquiv input source target hequal)
    (randomnessEquiv_measurePreserving input source target hequal)
    (fun randomness pairs =>
      transformPairs input source target randomness
        (targetRandomness input source target hequal randomness) pairs)
    (transformPairs_joint_measurable input source target hequal)
    (Filter.Eventually.of_forall fun randomness =>
      transformPairs_preservesLaw input source target randomness
        (targetRandomness input source target hequal randomness))

@[simp] theorem transformPairs_selected (input : Input) (source target : Hidden)
    (sourceRandomness : Randomness source)
    (targetRandomness : Randomness target) (pairs : LabelPairs)
    (wire : BitIndex) (purpose : Purpose) :
    transformPairs input source target sourceRandomness targetRandomness pairs
        wire (inputBit input wire) purpose =
      pairs wire (inputBit input wire) purpose := by
  simp [transformPairs]

theorem transformPairs_swapped (input : Input) (source target : Hidden)
    (sourceRandomness : Randomness source)
    (targetRandomness : Randomness target) (pairs : LabelPairs) :
    transformPairs input target source targetRandomness sourceRandomness
        (transformPairs input source target sourceRandomness targetRandomness
          pairs) = pairs := by
  funext wire bit purpose
  by_cases hselected : bit = inputBit input wire
  · simp [transformPairs, hselected]
  · simp only [transformPairs, hselected, if_false]
    exact IdealAffineTablePrivacy.translatePad_source_target_source _ _ _

theorem transformPairs_activeLabels (input : Input) (source target : Hidden)
    (sourceRandomness : Randomness source)
    (targetRandomness : Randomness target) (pairs : LabelPairs) :
    activeLabels
        (transformPairs input source target sourceRandomness targetRandomness
          pairs) input =
      activeLabels pairs input := by
  funext wire purpose
  exact transformPairs_selected input source target sourceRandomness
    targetRandomness pairs wire purpose

theorem targetTableMask_eq (input : Input) (source target : Hidden)
    (hequal : reference Profile source input = reference Profile target input)
    (randomness : Randomness source) (index : Fin 91)
    (kind : GLVProjectiveMap.TableKind) :
    let targetRandomness :=
      targetRandomness input source target hequal randomness
    let sourceParams :=
      (mapHidden source randomness.offsets randomness.randomizers
        randomness.chainMasks index).params kind
    let targetParams :=
      (mapHidden target targetRandomness.offsets targetRandomness.randomizers
        targetRandomness.chainMasks index).params kind
    (⟨targetRandomness.tableMasks index kind,
        targetRandomness.tableMasks_sum index kind⟩ :
      IdealAffineTable.MaskFiber targetParams.constant) =
      IdealAffineTablePrivacy.maskEquiv sourceParams targetParams
        (bitsFor kind input)
        (tableOutput_preserved input source target hequal randomness.offsets
          randomness.randomizers randomness.chainMasks index kind)
        (⟨randomness.tableMasks index kind,
          randomness.tableMasks_sum index kind⟩ :
          IdealAffineTable.MaskFiber sourceParams.constant) := by
  apply Subtype.ext
  rfl

theorem tableCipher_preserved (input : Input) (source target : Hidden)
    (hequal : reference Profile source input = reference Profile target input)
    (randomness : Randomness source) (pairs : LabelPairs)
    (mapIndex : Fin 91) (kind : GLVProjectiveMap.TableKind)
    (index : Fin IdealAffineTable.tableWidth) (bit : Bool) :
    let targetRandomness :=
      targetRandomness input source target hequal randomness
    let targetPairs := transformPairs input source target randomness
      targetRandomness pairs
    let sourceParams :=
      (mapHidden source randomness.offsets randomness.randomizers
        randomness.chainMasks mapIndex).params kind
    let targetParams :=
      (mapHidden target targetRandomness.offsets targetRandomness.randomizers
        targetRandomness.chainMasks mapIndex).params kind
    Bytes.xor
        (IdealAffineTablePrivacy.payload targetParams
          (targetRandomness.tableMasks mapIndex kind) index bit)
        (targetPairs (tableWire kind index) bit
          (GLVProjectiveMap.purpose mapIndex.val kind)) =
      Bytes.xor
        (IdealAffineTablePrivacy.payload sourceParams
          (randomness.tableMasks mapIndex kind) index bit)
        (pairs (tableWire kind index) bit
          (GLVProjectiveMap.purpose mapIndex.val kind)) := by
  dsimp only
  let sourceParams :=
    (mapHidden source randomness.offsets randomness.randomizers
      randomness.chainMasks mapIndex).params kind
  let transformed := targetRandomness input source target hequal randomness
  let targetParams :=
    (mapHidden target transformed.offsets transformed.randomizers
      transformed.chainMasks mapIndex).params kind
  let sourceMask : IdealAffineTable.MaskFiber sourceParams.constant :=
    ⟨randomness.tableMasks mapIndex kind,
      randomness.tableMasks_sum mapIndex kind⟩
  let targetMask : IdealAffineTable.MaskFiber targetParams.constant :=
    ⟨transformed.tableMasks mapIndex kind,
      transformed.tableMasks_sum mapIndex kind⟩
  have houtput : sourceParams.coefficient *
          IdealAffineTable.decodeBits (bitsFor kind input) +
        sourceParams.constant =
      targetParams.coefficient *
          IdealAffineTable.decodeBits (bitsFor kind input) +
        targetParams.constant :=
    tableOutput_preserved input source target hequal randomness.offsets
      randomness.randomizers randomness.chainMasks mapIndex kind
  have hmask : targetMask =
      IdealAffineTablePrivacy.maskEquiv sourceParams targetParams
        (bitsFor kind input) houtput sourceMask := by
    exact targetTableMask_eq input source target hequal randomness mapIndex kind
  by_cases hselected : bit = bitsFor kind input index
  · have hinput : bit = inputBit input (tableWire kind index) := by
      rw [inputBit_tableWire]
      exact hselected
    unfold transformPairs
    rw [if_pos hinput]
    rw [show IdealAffineTablePrivacy.payload targetParams
          (transformed.tableMasks mapIndex kind) index bit =
        IdealAffineTablePrivacy.payload targetParams targetMask.1 index bit by
      rfl]
    rw [hmask]
    subst bit
    unfold IdealAffineTablePrivacy.payload
    rw [IdealAffineTablePrivacy.share_maskEquiv sourceParams targetParams
      (bitsFor kind input) houtput sourceMask index]
  · have hinput : bit ≠ inputBit input (tableWire kind index) := by
      rw [inputBit_tableWire]
      exact hselected
    unfold transformPairs
    rw [if_neg hinput]
    rw [payloadAt_tableWire, payloadAt_tableWire]
    exact IdealAffineTablePrivacy.payload_xor_translatePad _ _ _

theorem tableGarble_preserved (input : Input) (source target : Hidden)
    (hequal : reference Profile source input = reference Profile target input)
    (randomness : Randomness source) (pairs : LabelPairs)
    (mapIndex : Fin 91) (kind : GLVProjectiveMap.TableKind) :
    let transformed := targetRandomness input source target hequal randomness
    let targetPairs := transformPairs input source target randomness transformed
      pairs
    IdealAffineTable.garble (GLVProjectiveMap.purpose mapIndex.val kind)
        (GLVProjectiveMap.pairsFor (xPairs targetPairs) (yPairs targetPairs) kind)
        ((mapHidden target transformed.offsets transformed.randomizers
          transformed.chainMasks mapIndex).params kind)
        ⟨transformed.tableMasks mapIndex kind,
          transformed.tableMasks_sum mapIndex kind⟩ =
      IdealAffineTable.garble (GLVProjectiveMap.purpose mapIndex.val kind)
        (GLVProjectiveMap.pairsFor (xPairs pairs) (yPairs pairs) kind)
        ((mapHidden source randomness.offsets randomness.randomizers
          randomness.chainMasks mapIndex).params kind)
        ⟨randomness.tableMasks mapIndex kind,
          randomness.tableMasks_sum mapIndex kind⟩ := by
  dsimp only
  apply IdealAffineTable.Table.ext
  funext pair
  unfold IdealAffineTable.garble
  apply congrArg IdealAffineTable.packCiphertexts
  unfold IdealAffineTable.materializeCiphertexts
  apply congrArg Vector.ofFn
  funext slot
  let index := IdealAffineTable.slotRow pair slot
  let bit := IdealAffineTable.slotSelected slot
  have h := tableCipher_preserved input source target hequal randomness
    pairs mapIndex kind index bit
  unfold IdealAffineTablePrivacy.payload at h
  unfold IdealAffineTable.ciphertextForSlot
  cases kind <;>
    simpa only [GLVProjectiveMap.pairsFor, xPairs, yPairs, tableWire, kindUsesX,
      Bool.false_eq_true, if_true, if_false] using
      h

theorem mapGarble_preserved (input : Input) (source target : Hidden)
    (hequal : reference Profile source input = reference Profile target input)
    (randomness : Randomness source) (pairs : LabelPairs)
    (mapIndex : Fin 91) :
    let transformed := targetRandomness input source target hequal randomness
    let targetPairs := transformPairs input source target randomness transformed
      pairs
    GLVProjectiveMap.garble mapIndex.val (xPairs targetPairs) (yPairs targetPairs)
        (mapHidden target transformed.offsets transformed.randomizers
          transformed.chainMasks mapIndex)
        (fun kind => ⟨transformed.tableMasks mapIndex kind,
          transformed.tableMasks_sum mapIndex kind⟩) =
      GLVProjectiveMap.garble mapIndex.val (xPairs pairs) (yPairs pairs)
        (mapHidden source randomness.offsets randomness.randomizers
          randomness.chainMasks mapIndex)
        (fun kind => ⟨randomness.tableMasks mapIndex kind,
          randomness.tableMasks_sum mapIndex kind⟩) := by
  dsimp only
  apply GLVProjectiveMap.Artifact.ext
  funext kind
  exact tableGarble_preserved input source target hequal randomness pairs
    mapIndex kind

theorem garble_preserved (input : Input) (source target : Hidden)
    (hequal : reference Profile source input = reference Profile target input)
    (randomness : Randomness source) (pairs : LabelPairs) :
    let transformed := targetRandomness input source target hequal randomness
    let targetPairs := transformPairs input source target randomness transformed
      pairs
    garble target transformed targetPairs = garble source randomness pairs := by
  dsimp only
  apply GLVFamilyArtifact.Artifact.ext
  funext index
  exact mapGarble_preserved input source target hequal randomness pairs index

def productChange (input : Input) (source target : Hidden)
    (hequal : reference Profile source input = reference Profile target input)
    (state : Randomness source × LabelPairs) :
    Randomness target × LabelPairs :=
  (targetRandomness input source target hequal state.1,
    transformPairs input source target state.1
      (targetRandomness input source target hequal state.1) state.2)

def derivedState (hidden : Hidden) (state : HiddenState) :
    Randomness hidden × LabelPairs :=
  (randomnessFromOracle hidden state.internalOracle, state.pairs)

set_option maxRecDepth 4096 in
theorem derivedState_measurable (hidden : Hidden) :
    Measurable (derivedState hidden) := by
  have hstate := HiddenState.measurableEquiv.measurable
  have horacle : Measurable (fun state : HiddenState =>
      randomnessFromOracle hidden state.internalOracle) :=
    (randomnessFromOracle_measurable hidden).comp
      (measurable_fst.comp hstate)
  have hpairs : Measurable (fun state : HiddenState => state.pairs) :=
    measurable_snd.comp hstate
  exact horacle.prodMk hpairs

set_option maxRecDepth 4096 in
theorem derivedState_measurePreserving (hidden : Hidden) :
    MeasurePreserving (derivedState hidden) hiddenStateLaw
      ((randomnessLaw hidden).prod labelPairsLaw) := by
  have horacle : MeasurePreserving (randomnessFromOracle hidden)
      internalOracleLaw (randomnessLaw hidden) :=
    ⟨randomnessFromOracle_measurable hidden,
      randomnessFromOracle_law hidden⟩
  have hproduct := horacle.prod (MeasurePreserving.id labelPairsLaw)
  have hstate : MeasurePreserving HiddenState.measurableEquiv hiddenStateLaw
      (internalOracleLaw.prod labelPairsLaw) := by
    unfold hiddenStateLaw
    exact (HiddenState.measurableEquiv.symm.measurable
      |>.measurePreserving (internalOracleLaw.prod labelPairsLaw)).symm
        HiddenState.measurableEquiv.symm
  have hcomposed := hproduct.comp hstate
  apply hcomposed.congr (derivedState_measurable hidden)
  filter_upwards [] with state
  rfl

set_option maxRecDepth 4096 in
theorem productArtifactBytes_measurable (hidden : Hidden) :
    Measurable (fun state : Randomness hidden × LabelPairs =>
      GLVFamilyArtifact.encode (garble hidden state.1 state.2)) := by
  have hpads : Measurable (fun state : Randomness hidden × LabelPairs =>
      artifactPads state.2) := artifactPads_measurable.comp measurable_snd
  have hobservation : Measurable
      (fun state : Randomness hidden × LabelPairs =>
        (state.1, artifactPads state.2)) := measurable_fst.prodMk hpads
  have hgarble : Measurable
      (fun observation : Randomness hidden × ArtifactPads =>
        GLVFamilyArtifact.encode
          (garble hidden observation.1 (expandArtifactPads observation.2))) :=
    measurable_of_finite _
  have hcomposed := hgarble.comp hobservation
  convert hcomposed using 1
  funext state
  exact congrArg GLVFamilyArtifact.encode
    (garble_expandArtifactPads_artifactPads hidden state.1 state.2).symm

noncomputable def productView (hidden : Hidden) (input : Input)
    (state : Randomness hidden × LabelPairs) : PublicView Profile :=
  (PublicView.measurableEquiv Profile).symm
    ((GLVFamilyArtifact.encode (garble hidden state.1 state.2),
      activeLabels state.2 input),
      .ok (Profile.outputEquiv.symm (reference Profile hidden input)))

theorem productView_measurable (hidden : Hidden) (input : Input) :
    Measurable (productView hidden input) := by
  have hartifact := productArtifactBytes_measurable hidden
  have hlabels : Measurable
      (fun state : Randomness hidden × LabelPairs =>
        activeLabels state.2 input) :=
    (activeLabels_measurable input).comp measurable_snd
  exact (PublicView.measurableEquiv Profile).symm.measurable.comp
    ((hartifact.prodMk hlabels).prodMk measurable_const)

set_option maxRecDepth 4096 in
theorem productView_productChange (input : Input) (source target : Hidden)
    (hequal : reference Profile source input = reference Profile target input)
    (state : Randomness source × LabelPairs) :
    productView target input (productChange input source target hequal state) =
      productView source input state := by
  let transformed := targetRandomness input source target hequal state.1
  let transformedPairs := transformPairs input source target state.1
    transformed state.2
  have hartifact : garble target transformed transformedPairs =
      garble source state.1 state.2 :=
    garble_preserved input source target hequal state.1 state.2
  have hlabels : activeLabels transformedPairs input =
      activeLabels state.2 input :=
    transformPairs_activeLabels input source target state.1 transformed state.2
  apply PublicView.ext
  · exact congrArg
      (fun artifact : GLVFamilyArtifact.Artifact 91 =>
        GLVFamilyArtifact.encode artifact)
      hartifact
  · exact hlabels
  · exact congrArg (fun point => Except.ok (Profile.outputEquiv.symm point))
      hequal.symm

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem stateView_eq_productView (hidden : Hidden) (input : Input)
    (state : HiddenState) :
    stateView scheme hidden state input =
      productView hidden input (derivedState hidden state) := by
  obtain ⟨output, hresult, hreference⟩ :=
    correct hidden state.internalOracle state.pairs input
  have houtput : output =
      Profile.outputEquiv.symm (reference Profile hidden input) := by
    apply Profile.outputEquiv.injective
    simpa using hreference
  apply PublicView.ext
  · exact congrArg
      (fun artifact : GLVFamilyArtifact.Artifact 91 =>
        GLVFamilyArtifact.encode artifact)
      (garbleWithOracle_eq hidden state.internalOracle state.pairs)
  · rfl
  · unfold stateView publicView productView derivedState
    dsimp only
    rw [hresult, houtput]
    rfl

set_option maxRecDepth 4096 in
theorem stateView_measurable (hidden : Hidden) (input : Input) :
    Measurable (fun state : HiddenState =>
      stateView scheme hidden state input) := by
  rw [show (fun state : HiddenState => stateView scheme hidden state input) =
      productView hidden input ∘ derivedState hidden by
    funext state
    exact stateView_eq_productView hidden input state]
  exact (productView_measurable hidden input).comp
    (derivedState_measurable hidden)

set_option maxRecDepth 4096 in
theorem publicView_identDistrib (input : Input) (source target : Hidden)
    (hequal : reference Profile source input = reference Profile target input) :
    IdentDistrib
      (fun state => stateView scheme source state input)
      (fun state => stateView scheme target state input)
      hiddenStateLaw hiddenStateLaw := by
  refine ⟨(stateView_measurable source input).aemeasurable,
    (stateView_measurable target input).aemeasurable, ?_⟩
  rw [show (fun state : HiddenState => stateView scheme source state input) =
      productView source input ∘ derivedState source by
    funext state
    exact stateView_eq_productView source input state]
  rw [show (fun state : HiddenState => stateView scheme target state input) =
      productView target input ∘ derivedState target by
    funext state
    exact stateView_eq_productView target input state]
  rw [← Measure.map_map (productView_measurable source input)
    (derivedState_measurable source)]
  rw [← Measure.map_map (productView_measurable target input)
    (derivedState_measurable target)]
  rw [(derivedState_measurePreserving source).map_eq,
    (derivedState_measurePreserving target).map_eq]
  rw [show productView source input =
      productView target input ∘ productChange input source target hequal by
    funext state
    exact (productView_productChange input source target hequal state).symm]
  unfold productChange
  rw [← Measure.map_map (productView_measurable target input)
    (productChange_measurePreserving input source target hequal).measurable]
  rw [(productChange_measurePreserving input source target hequal).map_eq]

theorem functionPrivate : FunctionPrivate scheme where
  stateView_measurable := stateView_measurable
  publicView_identDistrib := publicView_identDistrib

theorem valid : ValidCandidate scheme claimedBytes where
  correct := correct
  function_private := functionPrivate
  codec := codec
  artifact_bound := artifactBoundOracle

end GarblingPrize.Submission.GLVCompactPrivacy
