import G1Release.Submission.Scheme
import G1Release.Submission.GLVOffsetFamily

namespace G1Release.Submission.GLVDigits
open GarblingPrize.Protected G1Release.Protected EisensteinRadix
open Scheme (runtimeOfGroup toPoint_runtimeOfGroup inputAffine inputAffine_onCurve
  inputRuntime inputG1)
abbrev Word := BN254.Fq
abbrev Point := RuntimeG1.Point
abbrev Hidden := Private

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
  ⟨digitScale digit * (input.val.1.val : Word), (input.val.2.val : Word)⟩

theorem digitAffine_onCurve (digit : Digit) (input : Input) :
    HomogeneousRCBG1GroupLaw.AffineOnCurve (digitAffine digit input) := by
  change (digitScale digit * (input.val.1.val : Word)) ^ 3 + 3 =
    (input.val.2.val : Word) ^ 2
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


theorem mapOutput_eq (offset : BN254.G1) (digit : Digit) (input : Input) :
    EisensteinFullWidth.mapOutput offset digit (-inputG1 input) =
      offset + EisensteinFullWidth.digitTerm digit (inputG1 input) := by
  unfold EisensteinFullWidth.mapOutput
  rw [EisensteinFullWidth.digitTerm_neg]
  abel

def offsetAt {hidden : Hidden} (offsets : GLVOffsetFamily.Fiber hidden)
    (index : Fin 91) : BN254.G1 :=
  offsets.values.get ⟨index.val, by rw [offsets.length_eq]; exact index.isLt⟩

def digitAt (hidden : Hidden) (index : Fin 91) : Digit :=
  (GLVOffsetFamily.digits hidden).get ⟨index.val, by rw [GLVOffsetFamily.digits_length]; exact index.isLt⟩

end G1Release.Submission.GLVDigits
