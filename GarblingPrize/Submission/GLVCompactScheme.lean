import GarblingPrize.Submission.GLVFamilyArtifact
import GarblingPrize.Submission.GLVOffsetFamily
import GarblingPrize.Submission.GLVProjectiveMapPrivacy
import GarblingPrize.Submission.GLVProjectiveMapRuntime
import GarblingPrize.Submission.RuntimeG1GLV

namespace GarblingPrize.Submission.GLVCompactScheme

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

def decodeArtifact (bytes : ByteArray) : Except DecodeError Artifact :=
  match GLVFamilyArtifact.decode 91 bytes with
  | .ok artifact => .ok artifact
  | .error .trailingBytes => .error .trailingBytes
  | .error _ => .error .malformedArtifact

def scheme : Scheme Profile :=
  Scheme.ofFunctions Artifact Randomness garble evaluate encodeArtifact
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
  exact Scheme.correct_ofFunctions Artifact Randomness garble evaluate
    encodeArtifact decodeArtifact codec artifactCorrect

def seedInstantiation : Scheme.SeedInstantiation scheme where
  randomnessFromPads := fun hidden _ => canonicalRandomness hidden

def claimedBytes : Nat := 16145129

set_option maxRecDepth 4096 in
theorem artifactBound (hidden : Hidden) (randomness : Randomness hidden)
    (pairs : LabelPairs) :
    (scheme.garbleBytes hidden randomness pairs).size ≤ claimedBytes := by
  change (GLVFamilyArtifact.encode (garble hidden randomness pairs)).size ≤ _
  rw [GLVFamilyArtifact.encode_size, GLVFamilyArtifact.ninetyOne_byteCount]
  rfl


end GarblingPrize.Submission.GLVCompactScheme
