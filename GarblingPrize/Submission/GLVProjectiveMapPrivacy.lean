import GarblingPrize.Submission.GLVProjectiveMap

namespace GarblingPrize.Submission.GLVProjectiveMapPrivacy

abbrev Word := GLVProjectiveMap.Word
abbrev Coefficients := GLVProjectiveMap.Coefficients
abbrev ChainMasks := GLVProjectiveMap.ChainMasks
abbrev TableKind := GLVProjectiveMap.TableKind

def tableInput (kind : TableKind) (x y : Word) : Word :=
  match kind with
  | .xLinear | .xCross | .yCubic | .yQuadratic | .yLinear |
      .zCross | .zCubic => x
  | .xOuter | .xCorrection | .zLinear | .zOuter => y

def opened (coefficients : Coefficients) (masks : ChainMasks)
    (kind : TableKind) (x y : Word) : Word :=
  let hidden : GLVProjectiveMap.Hidden := ⟨coefficients, masks⟩
  (hidden.params kind).coefficient * tableInput kind x y +
    (hidden.params kind).constant

def reconstruct (values : TableKind → Word) (x y : Word) :
    ProjectiveMap.Coordinates Word where
  x := values .xLinear + (values .xCross + values .xOuter) * y +
    values .xCorrection
  y := (values .yCubic * x + values .yQuadratic) * x +
    values .yLinear
  z := values .zCross * y + values .zCubic * x ^ 2 +
    values .zLinear + values .zOuter * y

theorem reconstruct_opened (coefficients : Coefficients)
    (masks : ChainMasks) (x y : Word)
    (hcurve : y ^ 2 = x ^ 3 + 3) :
    reconstruct (fun kind => opened coefficients masks kind x y) x y =
      ProjectiveMap.polynomial coefficients x y := by
  apply ProjectiveMap.Coordinates.ext <;>
    simp [reconstruct, opened, tableInput, GLVProjectiveMap.Hidden.params,
      ProjectiveMap.polynomial]
  · ring
  · linear_combination -coefficients.yYY * hcurve
  · linear_combination -masks.zCubic * hcurve

/-- Triangularly translate eight internal masks so the eleven selected table
openings are identical whenever the final randomized coordinates agree. -/
def translateMasks (source target : Coefficients) (x y : Word)
    (masks : ChainMasks) : ChainMasks :=
  let sourceOpened := fun kind => opened source masks kind x y
  let xLinear := sourceOpened .xLinear - target.xX * x
  let xCross := sourceOpened .xCross - target.xXY * x
  let xOuter := sourceOpened .xOuter - target.xYY * y - target.xY + xCross
  let yCubic := sourceOpened .yCubic - target.yYY * x
  let yQuadratic := sourceOpened .yQuadratic -
    (target.yXX - yCubic) * x
  let zCross := sourceOpened .zCross - target.zXY * x
  let zCubic := (sourceOpened .zCubic - target.zXX) / x
  let zLinear := (target.zYY - zCubic) * y + target.zY - zCross -
    sourceOpened .zOuter
  { xLinear, xCross, xOuter, yCubic, yQuadratic,
    zCross, zCubic, zLinear }

theorem opened_translateMasks (source target : Coefficients) (x y : Word)
    (hcoordinates : ProjectiveMap.polynomial source x y =
      ProjectiveMap.polynomial target x y)
    (hcurve : y ^ 2 = x ^ 3 + 3)
    (hx0 : x ≠ 0)
    (masks : ChainMasks) (kind : TableKind) :
    opened target (translateMasks source target x y masks) kind x y =
      opened source masks kind x y := by
  have hx := congrArg ProjectiveMap.Coordinates.x hcoordinates
  have hy := congrArg ProjectiveMap.Coordinates.y hcoordinates
  have hz := congrArg ProjectiveMap.Coordinates.z hcoordinates
  cases kind <;>
    simp [opened, tableInput, translateMasks,
      GLVProjectiveMap.Hidden.params, ProjectiveMap.polynomial] at hx hy hz ⊢
  case xCorrection => linear_combination -hx
  case yLinear =>
    linear_combination -hy + (source.yYY - target.yYY) * hcurve
  case zLinear =>
    field_simp [hx0] at hz ⊢
    linear_combination -x * hz -
      (source.zXX - target.zXX) * hcurve
  all_goals field_simp [hx0] <;> ring

theorem translateMasks_source_target_source
    (source target : Coefficients) (x y : Word) (hx0 : x ≠ 0)
    (masks : ChainMasks) :
    translateMasks target source x y
      (translateMasks source target x y masks) = masks := by
  apply GLVProjectiveMap.ChainMasks.ext <;>
    simp [translateMasks, opened, tableInput,
      GLVProjectiveMap.Hidden.params] <;> field_simp [hx0] <;> ring

theorem translateMasks_target_source_target
    (source target : Coefficients) (x y : Word) (hx0 : x ≠ 0)
    (masks : ChainMasks) :
    translateMasks source target x y
      (translateMasks target source x y masks) = masks := by
  exact translateMasks_source_target_source target source x y hx0 masks

def chainMaskEquiv (source target : Coefficients) (x y : Word) (hx0 : x ≠ 0) :
    ChainMasks ≃ ChainMasks where
  toFun := translateMasks source target x y
  invFun := translateMasks target source x y
  left_inv := translateMasks_source_target_source source target x y hx0
  right_inv := translateMasks_target_source_target source target x y hx0

@[simp] theorem chainMaskEquiv_apply (source target : Coefficients)
    (x y : Word) (hx0 : x ≠ 0) (masks : ChainMasks) :
    chainMaskEquiv source target x y hx0 masks =
      translateMasks source target x y masks := rfl

theorem params_output_chainMaskEquiv
    (source target : Coefficients) (x y : Word)
    (hcoordinates : ProjectiveMap.polynomial source x y =
      ProjectiveMap.polynomial target x y)
    (hcurve : y ^ 2 = x ^ 3 + 3)
    (hx0 : x ≠ 0)
    (masks : ChainMasks) (kind : TableKind) :
    let sourceHidden : GLVProjectiveMap.Hidden := ⟨source, masks⟩
    let targetHidden : GLVProjectiveMap.Hidden :=
      ⟨target, chainMaskEquiv source target x y hx0 masks⟩
    (targetHidden.params kind).coefficient * tableInput kind x y +
        (targetHidden.params kind).constant =
      (sourceHidden.params kind).coefficient * tableInput kind x y +
        (sourceHidden.params kind).constant := by
  exact opened_translateMasks source target x y hcoordinates hcurve hx0 masks kind

end GarblingPrize.Submission.GLVProjectiveMapPrivacy
