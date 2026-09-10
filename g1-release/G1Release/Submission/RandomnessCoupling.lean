import G1Release.Submission.RandomizedCorrect
import G1Release.Submission.AffineTablePrivacy
import G1Release.Submission.ProjectiveMapPrivacy

/-! Algebraic coupling of the complete selected arithmetic view. This does
not assert ROM privacy: the finite-tape and bounded-query transports follow
separately. -/
namespace G1Release.Submission.Randomized
open G1Release.Math G1Release.Protected
open G1Release.Submission.BalancedTernary
open Scheme (offsetAt digitAt inputG1 rawMap rawMap_valid rawMap_eq_addFormula
  decode_rawMap xBits yBits decodeBits_xBits decodeBits_yBits runtimeOfGroup digitRuntime)
open scoped BigOperators

set_option maxHeartbeats 800000
set_option maxRecDepth 4096

def targetOffsets (input : Input) (source target : Hidden)
    (hequal : OffsetFamily.mapAt source input = OffsetFamily.mapAt target input)
    (offsets : OffsetFamily.Fiber source) : OffsetFamily.Fiber target :=
  OffsetFamily.equiv input source target hequal offsets

theorem fullMapOutputs (hidden : Hidden) (offsets : OffsetFamily.Fiber hidden)
    (input : Input) :
    TernaryFullWidth.mapOutputs offsets.values (OffsetFamily.digits hidden).values
        (-inputG1 input) =
      (List.finRange 161).map (fun i =>
        offsetAt offsets i + (digitAt hidden i).value • inputG1 input) := by
  apply List.ext_getElem
  · simp [TernaryFullWidth.mapOutputs, offsets.length_eq, (OffsetFamily.digits hidden).length_eq]
  · intro i hi hj
    simp [TernaryFullWidth.mapOutputs, TernaryFullWidth.mapOutput,
      offsetAt, digitAt, Digits.get, List.get_eq_getElem]

theorem mapOutput_preserved (input : Input) (source target : Hidden)
    (hequal : OffsetFamily.mapAt source input = OffsetFamily.mapAt target input)
    (offsets : OffsetFamily.Fiber source) (index : Fin 161) :
    offsetAt (targetOffsets input source target hequal offsets) index +
        (digitAt target index).value • inputG1 input =
      offsetAt offsets index + (digitAt source index).value • inputG1 input := by
  have h := OffsetFamily.selectedOutputs_preserved input source target hequal offsets
  change TernaryFullWidth.mapOutputs
      (targetOffsets input source target hequal offsets).values
      (OffsetFamily.digits target).values (-inputG1 input) =
    TernaryFullWidth.mapOutputs offsets.values (OffsetFamily.digits source).values
      (-inputG1 input) at h
  rw [fullMapOutputs, fullMapOutputs] at h
  have hget := congrArg (fun xs => xs[index.val]?) h
  simpa using hget

theorem rawMap_wellFormed (offset : BN254.G1) (digit : Digit)
    (input : Input) :
    RepresentativeAlignment.WellFormed (rawMap offset digit input) := by
  rw [rawMap_eq_addFormula]
  exact FormulaSemantics.Law.formula_wellFormed
    (runtimeOfGroup offset).1 (digitRuntime digit input).1
    (runtimeOfGroup offset).2 (digitRuntime digit input).2

theorem rawMap_decode_eq (input : Input) (source target : Hidden)
    (hequal : OffsetFamily.mapAt source input = OffsetFamily.mapAt target input)
    (offsets : OffsetFamily.Fiber source) (index : Fin 161) :
    FormulaSemantics.Law.decode
        (rawMap (offsetAt offsets index) (digitAt source index) input) =
      FormulaSemantics.Law.decode
        (rawMap (offsetAt (targetOffsets input source target hequal offsets)
          index) (digitAt target index) input) := by
  rw [decode_rawMap, decode_rawMap]
  exact (mapOutput_preserved input source target hequal offsets index).symm

theorem rawMap_normalize_eq (input : Input) (source target : Hidden)
    (hequal : OffsetFamily.mapAt source input = OffsetFamily.mapAt target input)
    (offsets : OffsetFamily.Fiber source) (index : Fin 161) :
    RepresentativeAlignment.normalize
        (rawMap (offsetAt offsets index) (digitAt source index) input) =
      RepresentativeAlignment.normalize
        (rawMap (offsetAt (targetOffsets input source target hequal offsets)
          index) (digitAt target index) input) := by
  apply FormulaSemantics.Law.normalize_eq_of_decode_eq
    (rawMap_valid _ _ _) (rawMap_valid _ _ _)
  exact rawMap_decode_eq input source target hequal offsets index

def targetRandomizer (input : Input) (source target : Hidden)
    (hequal : OffsetFamily.mapAt source input = OffsetFamily.mapAt target input)
    (offsets : OffsetFamily.Fiber source) (index : Fin 161)
    (randomizer : Wordˣ) : Wordˣ :=
  RepresentativeAlignment.randomizerEquiv
    (rawMap (offsetAt offsets index) (digitAt source index) input)
    (rawMap (offsetAt (targetOffsets input source target hequal offsets) index)
      (digitAt target index) input)
    (rawMap_wellFormed _ _ _) (rawMap_wellFormed _ _ _)
    (rawMap_normalize_eq input source target hequal offsets index) randomizer

theorem randomizedPolynomial_preserved (input : Input)
    (source target : Hidden)
    (hequal : OffsetFamily.mapAt source input = OffsetFamily.mapAt target input)
    (offsets : OffsetFamily.Fiber source) (index : Fin 161)
    (randomizer : Wordˣ) :
    ProjectiveMap.polynomial
        (coefficients
          (offsetAt (targetOffsets input source target hequal offsets) index)
          (digitAt target index)
          (targetRandomizer input source target hequal offsets index randomizer))
        (input.val.1.val : Word) (input.val.2.val : Word) =
      ProjectiveMap.polynomial
        (coefficients (offsetAt offsets index)
          (digitAt source index) randomizer)
        (input.val.1.val : Word) (input.val.2.val : Word) := by
  rw [polynomial_coefficients,
    polynomial_coefficients]
  apply congrArg ProjectiveMap.Coordinates.ofHomogeneous
  exact RepresentativeAlignment.randomize_randomizerEquiv
    (rawMap (offsetAt offsets index) (digitAt source index) input)
    (rawMap (offsetAt (targetOffsets input source target hequal offsets) index)
      (digitAt target index) input)
    (rawMap_wellFormed _ _ _) (rawMap_wellFormed _ _ _)
    (rawMap_normalize_eq input source target hequal offsets index) randomizer

def targetChainMasks (input : Input) (source target : Hidden)
    (hequal : OffsetFamily.mapAt source input = OffsetFamily.mapAt target input)
    (offsets : OffsetFamily.Fiber source) (randomizers : Fin 161 → Wordˣ)
    (chainMasks : Fin 161 → ProjectiveMap.ChainMasks Word)
    (index : Fin 161) : ProjectiveMap.ChainMasks Word :=
  ProjectiveMapPrivacy.chainMaskEquiv
    (coefficients (offsetAt offsets index)
      (digitAt source index) (randomizers index))
    (coefficients
      (offsetAt (targetOffsets input source target hequal offsets) index)
      (digitAt target index)
      (targetRandomizer input source target hequal offsets index
        (randomizers index)))
    (input.val.1.val : Word) (input.val.2.val : Word) (chainMasks index)

def bitsFor (kind : ProjectiveMap.TableKind) (input : Input) :
    Fin 254 → Bool :=
  match kind with
  | .shared | .xXY | .yCubic | .yQuadratic | .yLinear |
      .zSquare | .zCross | .zLinear =>
      xBits input
  | .xYY | .xCorrection | .zCorrection =>
      yBits input

theorem decodeBits_bitsFor (kind : ProjectiveMap.TableKind) (input : Input) :
    AffineTable.decodeBits (bitsFor kind input) =
      ProjectiveMapPrivacy.tableInput kind
        (input.val.1.val : Word) (input.val.2.val : Word) := by
  cases kind <;>
    simp [bitsFor, ProjectiveMapPrivacy.tableInput, decodeBits_xBits,
      decodeBits_yBits]

theorem tableOutput_preserved (input : Input) (source target : Hidden)
    (hequal : OffsetFamily.mapAt source input = OffsetFamily.mapAt target input)
    (offsets : OffsetFamily.Fiber source) (randomizers : Fin 161 → Wordˣ)
    (chainMasks : Fin 161 → ProjectiveMap.ChainMasks Word)
    (index : Fin 161) (kind : ProjectiveMap.TableKind) :
    let sourceMap := mapHidden source offsets randomizers chainMasks index
    let targetMap := mapHidden target
      (targetOffsets input source target hequal offsets)
      (fun index => targetRandomizer input source target hequal offsets index
        (randomizers index))
      (targetChainMasks input source target hequal offsets randomizers chainMasks)
      index
    (sourceMap.params kind).coefficient *
          AffineTable.decodeBits (bitsFor kind input) +
        (sourceMap.params kind).constant =
      (targetMap.params kind).coefficient *
          AffineTable.decodeBits (bitsFor kind input) +
        (targetMap.params kind).constant := by
  dsimp only
  rw [decodeBits_bitsFor]
  symm
  apply ProjectiveMapPrivacy.params_output_chainMaskEquiv
  · exact (randomizedPolynomial_preserved input source target hequal offsets
      index (randomizers index)).symm
  · exact input.property
  · exact coefficients_xX (offsetAt offsets index)
      (digitAt source index) (randomizers index)
  · exact coefficients_xX
      (offsetAt (targetOffsets input source target hequal offsets) index)
      (digitAt target index)
      (targetRandomizer input source target hequal offsets index
        (randomizers index))
  · exact coefficients_zXX (offsetAt offsets index)
      (digitAt source index) (randomizers index)
  · exact coefficients_zXX
      (offsetAt (targetOffsets input source target hequal offsets) index)
      (digitAt target index)
      (targetRandomizer input source target hequal offsets index
        (randomizers index))

def targetTableMasks (input : Input) (source target : Hidden)
    (hequal : OffsetFamily.mapAt source input = OffsetFamily.mapAt target input)
    (offsets : OffsetFamily.Fiber source) (randomizers : Fin 161 → Wordˣ)
    (chainMasks : Fin 161 → ProjectiveMap.ChainMasks Word)
    (tableMasks : Fin 161 → ProjectiveMap.TableKind →
      Fin 254 → Word)
    (tableMasks_sum : ∀ index kind, ∑ i, tableMasks index kind i =
      ((mapHidden source offsets randomizers chainMasks index).params kind).constant)
    (index : Fin 161) (kind : ProjectiveMap.TableKind) :=
  AffineTablePrivacy.maskEquiv
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
      AffineTable.MaskFiber
        ((mapHidden source offsets randomizers chainMasks index).params kind).constant)

def targetRandomness (input : Input) (source target : Hidden)
    (hequal : OffsetFamily.mapAt source input = OffsetFamily.mapAt target input)
    (randomness : Randomness source) : Randomness target where
  offsets := targetOffsets input source target hequal randomness.offsets
  scales := fun index =>
    targetRandomizer input source target hequal randomness.offsets index
      (randomness.scales index)
  chains := targetChainMasks input source target hequal randomness.offsets
    randomness.scales randomness.chains
  tableMasks := fun index kind =>
    (targetTableMasks input source target hequal randomness.offsets
      randomness.scales randomness.chains randomness.tableMasks
      randomness.tableMasks_sum index kind).1
  tableMasks_sum := fun index kind =>
    (targetTableMasks input source target hequal randomness.offsets
      randomness.scales randomness.chains randomness.tableMasks
      randomness.tableMasks_sum index kind).2

@[simp] theorem targetOffsets_swapped (input : Input) (source target : Hidden)
    (hequal : OffsetFamily.mapAt source input = OffsetFamily.mapAt target input)
    (offsets : OffsetFamily.Fiber source) :
    targetOffsets input target source hequal.symm
        (targetOffsets input source target hequal offsets) = offsets := by
  exact (OffsetFamily.equiv input source target hequal).left_inv offsets

theorem targetRandomizer_swapped (input : Input) (source target : Hidden)
    (hequal : OffsetFamily.mapAt source input = OffsetFamily.mapAt target input)
    (offsets : OffsetFamily.Fiber source) (index : Fin 161)
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
    (hequal : OffsetFamily.mapAt source input = OffsetFamily.mapAt target input)
    (offsets : OffsetFamily.Fiber source) (randomizers : Fin 161 → Wordˣ)
    (chainMasks : Fin 161 → ProjectiveMap.ChainMasks Word) :
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
  exact ProjectiveMapPrivacy.translateMasks_source_target_source _ _ _ _ _

theorem targetRandomness_swapped (input : Input) (source target : Hidden)
    (hequal : OffsetFamily.mapAt source input = OffsetFamily.mapAt target input)
    (randomness : Randomness source) :
    targetRandomness input target source hequal.symm
        (targetRandomness input source target hequal randomness) = randomness := by
  let round := targetRandomness input target source hequal.symm
    (targetRandomness input source target hequal randomness)
  have hoffsets : round.offsets = randomness.offsets :=
    targetOffsets_swapped input source target hequal randomness.offsets
  have hrandomizers : round.scales = randomness.scales := by
    funext index
    exact targetRandomizer_swapped input source target hequal randomness.offsets
      index (randomness.scales index)
  have hchains : round.chains = randomness.chains :=
    targetChainMasks_swapped input source target hequal
      randomness.offsets randomness.scales randomness.chains
  have htables : round.tableMasks = randomness.tableMasks := by
    funext index kind maskIndex
    let sourceParams :=
      (mapHidden source randomness.offsets randomness.scales
        randomness.chains index).params kind
    let middle := targetRandomness input source target hequal randomness
    let middleParams :=
      (mapHidden target middle.offsets middle.scales middle.chains
        index).params kind
    let roundParams :=
      (mapHidden source round.offsets round.scales round.chains
        index).params kind
    have hroundParams : roundParams = sourceParams := by
      simp only [roundParams, sourceParams, hoffsets, hrandomizers, hchains]
    have hsourceMiddle :
        sourceParams.coefficient *
              AffineTable.decodeBits (bitsFor kind input) +
            sourceParams.constant =
          middleParams.coefficient *
              AffineTable.decodeBits (bitsFor kind input) +
            middleParams.constant := by
      exact tableOutput_preserved input source target hequal
        randomness.offsets randomness.scales randomness.chains
        index kind
    have hmiddleRound :
        middleParams.coefficient *
              AffineTable.decodeBits (bitsFor kind input) +
            middleParams.constant =
          roundParams.coefficient *
              AffineTable.decodeBits (bitsFor kind input) +
            roundParams.constant := by
      rw [hroundParams]
      exact hsourceMiddle.symm
    change ((AffineTablePrivacy.maskEquiv middleParams roundParams
        (bitsFor kind input) hmiddleRound)
      ((AffineTablePrivacy.maskEquiv sourceParams middleParams
        (bitsFor kind input) hsourceMiddle)
        (⟨randomness.tableMasks index kind,
          randomness.tableMasks_sum index kind⟩ :
          AffineTable.MaskFiber sourceParams.constant))).1 maskIndex =
      randomness.tableMasks index kind maskIndex
    dsimp only [AffineTablePrivacy.maskEquiv]
    unfold AffineTablePrivacy.transformMask
    change (randomness.tableMasks index kind maskIndex +
          AffineTable.weight maskIndex *
            (sourceParams.coefficient - middleParams.coefficient) *
            AffineTable.bitWord (bitsFor kind input maskIndex)) +
        AffineTable.weight maskIndex *
          (middleParams.coefficient - roundParams.coefficient) *
          AffineTable.bitWord (bitsFor kind input maskIndex) =
      randomness.tableMasks index kind maskIndex
    linear_combination
      -(AffineTable.weight maskIndex *
        AffineTable.bitWord (bitsFor kind input maskIndex)) *
      congrArg AffineTable.Params.coefficient hroundParams
  exact Randomness.ext round randomness hoffsets hrandomizers hchains htables

def randomnessEquiv (input : Input) (source target : Hidden)
    (hequal : OffsetFamily.mapAt source input = OffsetFamily.mapAt target input) :
    Randomness source ≃ Randomness target where
  toFun := targetRandomness input source target hequal
  invFun := targetRandomness input target source hequal.symm
  left_inv := targetRandomness_swapped input source target hequal
  right_inv := targetRandomness_swapped input target source hequal.symm


end G1Release.Submission.Randomized
