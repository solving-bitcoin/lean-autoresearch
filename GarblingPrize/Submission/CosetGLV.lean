import GarblingPrize.Submission.CosetFieldSampling
import GarblingPrize.Submission.GLVCompactPrivacy

namespace GarblingPrize.Submission.CosetGLV

open GarblingPrize.Protected
open EisensteinRadix GLVCompactScheme
open CosetCoordinates FourAffineQuotient

abbrev Word := BN254.Fq

local instance concreteGroup : AddCommGroup BN254.G1 := BN254.bn254.addCommGroup
local instance profileGroup : AddCommGroup Profile.G1 := concreteGroup

def digitE : Digit → Word
  | .negOne | .negOmega | .negOmegaSq => -1
  | _ => 1

theorem digitE_sq (digit : Digit) : digitE digit ^ 2 = 1 := by cases digit <;> simp [digitE]

def mapBase (offset : BN254.G1) (digit : Digit) : Base K :=
  CosetAffineMap.base (runtimeOfGroup offset) (digitSelector digit) (digitScale digit) (digitE digit)

theorem mapBase_denominator_ne_zero (offset : BN254.G1) (digit : Digit) (input : Input) :
    denominator (mapBase offset digit) (C (input.x.val : Word)) ≠ 0 :=
  CosetAffineMap.denominator_ne_zero _ _ _ _ (inputAffine input) (digitScale_cube digit)
    (inputAffine_onCurve input)

theorem transformed_eq_digitRuntime (digit : Digit) (input : Input) (hd : digit ≠ .zero) :
    RuntimeG1.ofAffine (CosetAffineMap.transformed (digitScale digit) (digitE digit) (inputAffine input))
      (CosetAffineMap.transformed_onCurve _ _ _ (digitScale_cube digit) (digitE_sq digit)
        (inputAffine_onCurve input)) = digitRuntime digit input := by
  cases digit <;> simp_all [digitRuntime, digitBaseRuntime, digitAffine,
    CosetAffineMap.transformed, digitE, inputAffine, RuntimeG1.ofAffine,
    HomogeneousRCBG1GroupLaw.negAffine] <;> apply Subtype.ext <;> rfl

theorem mapBase_value (offset : BN254.G1) (digit : Digit) (input : Input) :
    value (mapBase offset digit) (C (input.x.val : Word)) (C (input.y.val : Word)) =
      CosetCoordinates.encode (runtimeOfGroup
        (EisensteinFullWidth.mapOutput offset digit (-inputG1 input))) := by
  by_cases hd : digit = .zero
  · subst digit
    have hout : EisensteinFullWidth.mapOutput offset .zero (-inputG1 input) = offset := by
      rw [mapOutput_eq]
      simp [EisensteinFullWidth.digitTerm, EisensteinRadix.Digit.value, EisensteinRadix.evaluate]
      exact add_zero offset
    rw [hout]
    exact CosetAffineMap.value_base_false _ _ _ _ _
  · have hsel : digitSelector digit = true := by cases digit <;> simp_all [digitSelector]
    unfold mapBase
    rw [hsel]
    apply CosetAffineMap.value_base_true _ _ _ _ (inputAffine input)
      (digitScale_cube digit) (digitE_sq digit) (inputAffine_onCurve input)
    rw [transformed_eq_digitRuntime digit input hd, toPoint_runtimeOfGroup,
      toPoint_runtimeOfGroup, toPoint_digitRuntime, mapOutput_eq]

theorem mapBase_value_preserved (input : Input) (source target : Hidden)
    (hequal : reference Profile source input = reference Profile target input)
    (offsets : GLVOffsetFamily.Fiber source) (index : Fin 91) :
    value (mapBase (offsetAt offsets index) (digitAt source index))
        (C (input.x.val : Word)) (C (input.y.val : Word)) =
      value (mapBase (offsetAt (GLVCompactPrivacy.targetOffsets input source target hequal offsets)
        index) (digitAt target index)) (C (input.x.val : Word)) (C (input.y.val : Word)) := by
  rw [mapBase_value, mapBase_value, GLVCompactPrivacy.mapOutput_preserved]

theorem decode_openings (offset : BN254.G1) (digit : Digit) (input : Input) (state : State K) :
    CosetCoordinates.decode (reconstruct
      (opened (mapBase offset digit) state (C (input.x.val : Word)) (C (input.y.val : Word)))
      (C (input.x.val : Word))) =
      some (runtimeOfGroup (EisensteinFullWidth.mapOutput offset digit (-inputG1 input))) := by
  rw [reconstruct_opened _ _ _ _ (mapBase_denominator_ne_zero offset digit input),
    mapBase_value, CosetCoordinates.decode_encode]

end GarblingPrize.Submission.CosetGLV
