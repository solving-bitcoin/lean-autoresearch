import GarblingPrize.Submission.IdealAffineTablePrivacy
import GarblingPrize.Submission.ProjectiveMap

namespace GarblingPrize.Submission.ProjectiveMapPrivacy

open GarblingPrize.Protected
open GarblingPrize.Submission

abbrev Word := ProjectiveMap.Word
abbrev Coefficients := ProjectiveMap.Coefficients Word
abbrev ChainMasks := ProjectiveMap.ChainMasks Word
abbrev TableKind := ProjectiveMap.TableKind

/-- The public field value fed to one affine table. -/
def tableInput (kind : TableKind) (x y : Word) : Word :=
  match kind with
  | .shared | .xXY | .yCubic | .yQuadratic | .yLinear |
      .zSquare | .zCross | .zLinear => x
  | .xYY | .xCorrection | .zCorrection => y

/-- The complete selected opening of one table before its outer public
multiplication.  This is the value that must be identical in the one-shot
privacy proof, because artifact bytes and the corresponding active label are
both part of the protected public view. -/
def opened (coefficients : Coefficients) (masks : ChainMasks)
    (kind : TableKind) (x y : Word) : Word :=
  let hidden : ProjectiveMap.Hidden := ⟨coefficients, masks⟩
  (hidden.params kind).coefficient * tableInput kind x y +
    (hidden.params kind).constant

/-- Reconstruct the three projective coordinates from the ordered selected
table openings. -/
def reconstruct (values : TableKind → Word) (x y : Word) :
    ProjectiveMap.Coordinates Word where
  x := (values .xXY + values .xYY) * y + values .xCorrection -
    2 * ProjectiveMap.curveC * values .shared
  y := (values .yCubic * x + values .yQuadratic) * x +
    values .yLinear
  z := values .shared * x ^ 2 + values .zSquare * x +
    values .zCross * y + values .zLinear + values .zCorrection

theorem reconstruct_opened (coefficients : Coefficients)
    (masks : ChainMasks) (x y : Word)
    (hcurve : y ^ 2 = x ^ 3 + 3)
    (hxX : coefficients.xX =
      -(2 * ProjectiveMap.curveC * coefficients.zYY))
    (hzXX : coefficients.zXX = 3 * coefficients.xYY) :
    reconstruct (fun kind => opened coefficients masks kind x y) x y =
      ProjectiveMap.polynomial coefficients x y := by
  apply ProjectiveMap.Coordinates.ext <;>
    simp [reconstruct, opened, tableInput, ProjectiveMap.Hidden.params,
      ProjectiveMap.polynomial]
  · rw [hxX]
    ring
  · linear_combination -coefficients.yYY * hcurve
  · rw [hzXX]
    linear_combination -coefficients.zYY * hcurve

/-- Triangular mask translation.  The first openings in each coordinate are
chosen freely to equal the source openings.  Equality of the reconstructed
coordinate then forces the final correction opening to agree as well. -/
def translateMasks (source target : Coefficients) (x y : Word)
    (masks : ChainMasks) : ChainMasks :=
  let sourceOpened := fun kind => opened source masks kind x y
  let shared := sourceOpened .shared - target.zYY * x - 3 * target.xYY
  let xCross := sourceOpened .xXY - target.xXY * x
  let xOuter := sourceOpened .xYY - target.xYY * y - target.xY + xCross
  let yCubic := sourceOpened .yCubic - target.yYY * x
  let yQuadratic := sourceOpened .yQuadratic -
    (target.yXX - yCubic) * x
  let zSquare := sourceOpened .zSquare + shared * x
  let zCross := sourceOpened .zCross - target.zXY * x
  let zLinear := sourceOpened .zLinear + zSquare * x
  { shared, xCross, xOuter, yCubic, yQuadratic,
    zSquare, zCross, zLinear }

theorem opened_translateMasks (source target : Coefficients) (x y : Word)
    (hcoordinates : ProjectiveMap.polynomial source x y =
      ProjectiveMap.polynomial target x y)
    (hcurve : y ^ 2 = x ^ 3 + 3)
    (hsourceX : source.xX =
      -(2 * ProjectiveMap.curveC * source.zYY))
    (htargetX : target.xX =
      -(2 * ProjectiveMap.curveC * target.zYY))
    (hsourceZ : source.zXX = 3 * source.xYY)
    (htargetZ : target.zXX = 3 * target.xYY)
    (masks : ChainMasks) (kind : TableKind) :
    opened target (translateMasks source target x y masks) kind x y =
      opened source masks kind x y := by
  have hx := congrArg ProjectiveMap.Coordinates.x hcoordinates
  have hy := congrArg ProjectiveMap.Coordinates.y hcoordinates
  have hz := congrArg ProjectiveMap.Coordinates.z hcoordinates
  cases kind <;>
    simp [opened, tableInput, translateMasks, ProjectiveMap.Hidden.params,
      ProjectiveMap.polynomial] at hx hy hz ⊢
  case xCorrection =>
    rw [hsourceX, htargetX] at hx
    linear_combination -hx
  case yLinear =>
    linear_combination -hy + (source.yYY - target.yYY) * hcurve
  case zCorrection =>
    rw [hsourceZ, htargetZ] at hz
    linear_combination -hz + (source.zYY - target.zYY) * hcurve
  all_goals ring

theorem translateMasks_source_target_source
    (source target : Coefficients) (x y : Word) (masks : ChainMasks) :
    translateMasks target source x y
      (translateMasks source target x y masks) = masks := by
  apply ProjectiveMap.ChainMasks.ext <;>
    simp [translateMasks, opened, tableInput, ProjectiveMap.Hidden.params] <;>
    ring

theorem translateMasks_target_source_target
    (source target : Coefficients) (x y : Word) (masks : ChainMasks) :
    translateMasks source target x y
      (translateMasks target source x y masks) = masks := by
  exact translateMasks_source_target_source target source x y masks

/-- Explicit equivalence of the threaded coordinate-mask states. -/
def chainMaskEquiv (source target : Coefficients) (x y : Word) :
    ChainMasks ≃ ChainMasks where
  toFun := translateMasks source target x y
  invFun := translateMasks target source x y
  left_inv := translateMasks_source_target_source source target x y
  right_inv := translateMasks_target_source_target source target x y

@[simp] theorem chainMaskEquiv_apply (source target : Coefficients)
    (x y : Word) (masks : ChainMasks) :
    chainMaskEquiv source target x y masks =
      translateMasks source target x y masks := rfl

theorem params_output_chainMaskEquiv
    (source target : Coefficients) (x y : Word)
    (hcoordinates : ProjectiveMap.polynomial source x y =
      ProjectiveMap.polynomial target x y)
    (hcurve : y ^ 2 = x ^ 3 + 3)
    (hsourceX : source.xX =
      -(2 * ProjectiveMap.curveC * source.zYY))
    (htargetX : target.xX =
      -(2 * ProjectiveMap.curveC * target.zYY))
    (hsourceZ : source.zXX = 3 * source.xYY)
    (htargetZ : target.zXX = 3 * target.xYY)
    (masks : ChainMasks) (kind : TableKind) :
    let sourceHidden : ProjectiveMap.Hidden := ⟨source, masks⟩
    let targetHidden : ProjectiveMap.Hidden :=
      ⟨target, chainMaskEquiv source target x y masks⟩
    (targetHidden.params kind).coefficient * tableInput kind x y +
        (targetHidden.params kind).constant =
      (sourceHidden.params kind).coefficient * tableInput kind x y +
        (sourceHidden.params kind).constant := by
  exact opened_translateMasks source target x y hcoordinates hcurve
    hsourceX htargetX hsourceZ htargetZ masks kind

end GarblingPrize.Submission.ProjectiveMapPrivacy
