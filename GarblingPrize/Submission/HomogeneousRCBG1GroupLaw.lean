import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.NormNum.Parity
import GarblingPrize.Protected.Target
import GarblingPrize.Submission.BaseFieldCharacters
import GarblingPrize.Submission.HomogeneousRCB
import GarblingPrize.Submission.JacobianAffineAddMap

namespace GarblingPrize.Submission.HomogeneousRCBG1GroupLaw

/-!
# Total concrete meaning of the homogeneous RCB map

The executable public G1 pairing-source map never feeds arbitrary homogeneous
representatives to the RCB polynomial.  Its hidden operand is either the
canonical homogeneous identity or an affine normalization of a valid
Jacobian offset, and its selected operand is either the same identity or the
finite affine proof point.  This module proves totality on exactly that
domain and lands directly in the concrete Jacobian quotient used by the
subgroup checker.

The only exceptional locus of the polynomial is eliminated algebraically.
For two affine inputs with distinct abscissas, its output denominator is

`-(x₁-x₂)^3 * y(P₁-P₂)`.

The difference is a genuine affine curve point.  The checked BN254 theorem
that `-3` is not a cube implies that no finite G1 point has zero
ordinate, hence this denominator is nonzero.  Equal abscissas split into the
doubling and inverse branches.  The executable conversion canonicalizes the
inverse branch to Jacobian infinity.
-/

open GarblingPrize.Protected
open WeierstrassCurve
open WeierstrassCurve.Jacobian

noncomputable section

abbrev Field := BN254.Fq

@[ext] structure Affine where
  x : Field
  y : Field

/-- The BN254 G1 short-Weierstrass constant.  Writing the natural cast
directly keeps polynomial normalization aligned with `BN254.curve`. -/
abbrev curveB : Field := 3

theorem curveB_eq_fromNat :
    curveB = (GarblingPrize.Protected.curveB : BN254.Fq) := rfl

abbrev Homogeneous := HomogeneousRCB.Point Field
abbrev JacobianCoordinates := Fin 3 → Field
abbrev JacobianClass := WeierstrassCurve.Jacobian.PointClass Field

local notation3 "Xc" => (0 : Fin 3)
local notation3 "Yc" => (1 : Fin 3)
local notation3 "Zc" => (2 : Fin 3)

/-- The ordinary affine G1 equation in the base field. -/
abbrev AffineOnCurve (point : Affine) : Prop :=
  point.x ^ 3 + curveB = point.y ^ 2

theorem affine_nonsingular (point : Affine)
    (hpoint : AffineOnCurve point) :
    BN254.curve.toAffine.Nonsingular point.x point.y := by
  apply (BN254.curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero
    BN254.discriminant_ne_zero).mp
  rw [WeierstrassCurve.Affine.equation_iff]
  simpa [AffineOnCurve, BN254.curve] using hpoint.symm

private theorem two_ne_zero : (2 : Field) ≠ 0 := by
  intro hzero
  have hdiv : baseFieldModulus ∣ 2 :=
    (ZMod.natCast_eq_zero_iff 2 baseFieldModulus).mp hzero
  norm_num [baseFieldModulus] at hdiv

private def cubicExponent : Nat :=
  (baseFieldModulus - 1) / 3

private theorem cubicExponent_even : Even cubicExponent := by
  norm_num [cubicExponent, baseFieldModulus]

private theorem three_mul_cubicExponent :
    3 * cubicExponent = baseFieldModulus - 1 := by
  norm_num [cubicExponent, baseFieldModulus]

private def quadraticExponent : Nat :=
  (baseFieldModulus - 1) / 2

private theorem two_mul_quadraticExponent :
    2 * quadraticExponent = baseFieldModulus - 1 := by
  norm_num [quadraticExponent, baseFieldModulus]

/-- The fixed BN254 base-field element `3` is not a square. -/
theorem three_not_square (value : Field) :
    value ^ 2 ≠ (3 : Field) := by
  intro hsquare
  have hthree : (3 : Field) ≠ 0 := by
    intro hzero
    have hdiv : baseFieldModulus ∣ 3 :=
      (ZMod.natCast_eq_zero_iff 3 baseFieldModulus).mp hzero
    norm_num [baseFieldModulus] at hdiv
  have hvalue : value ≠ 0 := by
    intro hzero
    apply hthree
    simpa [hzero] using hsquare.symm
  apply BaseFieldCharacters.Q2.properPower
  calc
    (BaseFieldCharacters.witness : Field) ^
          ((BaseFieldCharacters.modulus - 1) / 2) =
        (3 : Field) ^ quadraticExponent := by
          rfl
    _ = (value ^ 2) ^ quadraticExponent := by rw [hsquare]
    _ = value ^ (2 * quadraticExponent) := by rw [pow_mul]
    _ = value ^ (baseFieldModulus - 1) := by
      rw [two_mul_quadraticExponent]
    _ = 1 := ZMod.pow_card_sub_one_eq_one hvalue

/-- The checked cube obstruction needed to rule out affine two-torsion. -/
theorem neg_three_not_cube (value : Field) :
    value ^ 3 ≠ -(3 : Field) := by
  intro hcube
  have hthree : (3 : Field) ≠ 0 := by
    intro hzero
    have hdiv : baseFieldModulus ∣ 3 :=
      (ZMod.natCast_eq_zero_iff 3 baseFieldModulus).mp hzero
    norm_num [baseFieldModulus] at hdiv
  have hvalue : value ≠ 0 := by
    intro hzero
    apply hthree
    apply neg_eq_zero.mp
    simpa [hzero] using hcube.symm
  have hpower : (-(3 : Field)) ^ cubicExponent = 1 := by
    calc
      (-(3 : Field)) ^ cubicExponent =
          (value ^ 3) ^ cubicExponent := by rw [hcube]
      _ = value ^ (3 * cubicExponent) := by rw [pow_mul]
      _ = value ^ (baseFieldModulus - 1) := by
        rw [three_mul_cubicExponent]
      _ = 1 := ZMod.pow_card_sub_one_eq_one hvalue
  have hthreePower : (3 : Field) ^ cubicExponent = 1 := by
    simpa only [cubicExponent_even.neg_pow] using hpower
  change (3 : ZMod baseFieldModulus) ^
    ((baseFieldModulus - 1) / 3) = 1 at hthreePower
  exact BaseFieldCharacters.Q3.properPower hthreePower

/-- Canonical ordinary-homogeneous infinity. -/
def infinity : Homogeneous where
  x := 0
  y := 1
  z := 0

/-- Embed one finite affine point into ordinary homogeneous coordinates. -/
def ofAffine (point : Affine) : Homogeneous where
  x := point.x
  y := point.y
  z := 1

/-- The exact two-case domain produced by the executable. -/
def encode : Option Affine → Homogeneous
  | none => infinity
  | some point => ofAffine point

/-- Curve membership for the exact two-case executable domain. -/
def InputOnCurve : Option Affine → Prop
  | none => True
  | some point => AffineOnCurve point

/-- Canonical Jacobian representative of an executable input. -/
def inputJacobian : Option Affine → JacobianCoordinates
  | none => ![(1 : Field), 1, 0]
  | some point => ![point.x, point.y, 1]

/-- Convert ordinary homogeneous `(X:Y:Z)` to the Jacobian convention used
by the executable.  A zero denominator is deliberately canonicalized. -/
def toJacobian (point : Homogeneous) : JacobianCoordinates :=
  if point.z = 0 then
    ![(1 : Field), 1, 0]
  else
    ![point.x * point.z, point.y * point.z ^ 2, point.z]

/-- The exact RCB specialization used by the public G1 maps. -/
def addFormula (left right : Homogeneous) : Homogeneous :=
  HomogeneousRCB.formula (3 * curveB) left right

@[simp] theorem encode_none : encode none = infinity := rfl

@[simp] theorem encode_some (point : Affine) :
    encode (some point) = ofAffine point := rfl

@[simp] theorem toJacobian_infinity :
    toJacobian infinity = ![(1 : Field), 1, 0] := by
  simp [toJacobian, infinity]

@[simp] theorem toJacobian_ofAffine (point : Affine) :
    toJacobian (ofAffine point) = ![point.x, point.y, 1] := by
  simp [toJacobian, ofAffine]

@[simp] theorem toJacobian_encode (input : Option Affine) :
    toJacobian (encode input) = inputJacobian input := by
  cases input <;> simp [inputJacobian]

/-- Positive Boolean selection is exactly the executable two-case domain. -/
theorem selectedInput_positive_eq_encode (selector : Bool)
    (point : Affine) :
    HomogeneousRCB.selectedInput selector .positive (ofAffine point) =
      encode (if selector then some point else none) := by
  cases selector <;>
    apply HomogeneousRCB.Point.ext <;>
    simp [HomogeneousRCB.selectedInput, HomogeneousRCB.selectorValue,
      HomogeneousRCB.Sign.value, ofAffine, encode, infinity]

/-! ## Exact no-two-torsion support -/

/-- No finite point on the exact BN254 G1 curve has zero ordinate. -/
theorem affine_y_ne_zero (point : Affine)
    (hpoint : AffineOnCurve point) : point.y ≠ 0 := by
  intro hy
  apply neg_three_not_cube point.x
  have hzero : point.x ^ 3 + curveB = 0 := by
    simpa [AffineOnCurve, hy] using hpoint
  simpa [curveB] using
    eq_neg_of_add_eq_zero_left hzero

/-- The affine tangent denominator is nonzero on every finite input in the
exact executable domain.  Keeping this as one named fact avoids repeatedly
asking the polynomial tactic to rediscover characteristic-not-two. -/
theorem affine_y_ne_negY (point : Affine)
    (hpoint : AffineOnCurve point) :
    point.y ≠ BN254.curve.toAffine.negY point.x point.y := by
  simp only [BN254.curve, WeierstrassCurve.Affine.negY, zero_mul,
    sub_zero]
  intro hequal
  have htwice : (2 : Field) * point.y = 0 := by
    linear_combination hequal
  exact (mul_ne_zero two_ne_zero
    (affine_y_ne_zero point hpoint)) htwice

/-- A finite executable input is a valid concrete Jacobian representative. -/
theorem affineJacobian_valid (point : Affine)
    (hpoint : AffineOnCurve point) :
    BN254.curve.toJacobian.Nonsingular ![point.x, point.y, (1 : Field)] := by
  rw [BN254.curve.toJacobian.nonsingular_some]
  exact affine_nonsingular point hpoint

theorem inputJacobian_valid (input : Option Affine)
    (hinput : InputOnCurve input) :
    BN254.curve.toJacobian.Nonsingular (inputJacobian input) := by
  cases input with
  | none =>
      simpa [inputJacobian] using
        BN254.curve.toJacobian.nonsingular_zero
  | some point =>
      simpa [inputJacobian] using affineJacobian_valid point hinput

/-- A finite ordinary-homogeneous result is the corresponding affine
Jacobian representative, up to the exact Jacobian scaling by `Z`. -/
theorem toJacobian_eq_smul_normalized (point : Homogeneous)
    (hz : point.z ≠ 0) :
    toJacobian point = point.z •
      ![point.x / point.z, point.y / point.z, (1 : Field)] := by
  rw [toJacobian, if_neg hz, smul_fin3]
  refine funext fun index => ?_
  fin_cases index
  · -- X: `z^2 * (x/z) = x*z`
    change point.x * point.z = point.z ^ 2 * (point.x / point.z)
    field_simp [hz]
  · -- Y: `z^3 * (y/z) = y*z^2`
    change point.y * point.z ^ 2 = point.z ^ 3 * (point.y / point.z)
    field_simp [hz]
  · change point.z = point.z * (1 : Field)
    ring

theorem pointClass_toJacobian_eq_normalized (point : Homogeneous)
    (hz : point.z ≠ 0) :
    (⟦toJacobian point⟧ : JacobianClass) =
      ⟦![point.x / point.z, point.y / point.z, (1 : Field)]⟧ := by
  rw [toJacobian_eq_smul_normalized point hz]
  exact smul_eq _ (Ne.isUnit hz)

/-! ## Literal polynomial cases -/

@[simp] theorem formula_infinity_infinity :
    addFormula infinity infinity = infinity := by
  apply HomogeneousRCB.Point.ext <;>
    simp [addFormula, HomogeneousRCB.formula, infinity]

theorem formula_infinity_affine (point : Affine) :
    addFormula infinity (ofAffine point) =
      { x := point.x * point.y
        y := point.y ^ 2
        z := point.y } := by
  apply HomogeneousRCB.Point.ext <;>
    simp [addFormula, HomogeneousRCB.formula, infinity, ofAffine] <;>
    ring

theorem formula_affine_infinity (point : Affine) :
    addFormula (ofAffine point) infinity =
      { x := point.x * point.y
        y := point.y ^ 2
        z := point.y } := by
  apply HomogeneousRCB.Point.ext <;>
    simp [addFormula, HomogeneousRCB.formula, infinity, ofAffine] <;>
    ring

/-! ## Distinct-abscissa branch -/

/-- Affine negation in the exact short-Weierstrass model. -/
def negAffine (point : Affine) : Affine where
  x := point.x
  y := -point.y

theorem negAffine_onCurve (point : Affine)
    (hpoint : AffineOnCurve point) :
    AffineOnCurve (negAffine point) := by
  simpa [AffineOnCurve, negAffine] using hpoint

/-- Negative Boolean selection is exactly finite affine negation in the
executable two-case domain. -/
theorem selectedInput_negative_eq_encode (selector : Bool)
    (point : Affine) :
    HomogeneousRCB.selectedInput selector .negative (ofAffine point) =
      encode (if selector then some (negAffine point) else none) := by
  cases selector <;>
    apply HomogeneousRCB.Point.ext <;>
    simp [HomogeneousRCB.selectedInput, HomogeneousRCB.selectorValue,
      HomogeneousRCB.Sign.value, ofAffine, encode, infinity, negAffine]

/-- Literal affine formula for `left - right`; this is used only under
distinct abscissas, so its slope is a secant. -/
def differenceAffine (left right : Affine) : Affine :=
  let slope := BN254.curve.toAffine.slope
    left.x right.x left.y (-right.y)
  { x := BN254.curve.toAffine.addX left.x right.x slope
    y := BN254.curve.toAffine.addY left.x right.x left.y slope }

theorem differenceAffine_onCurve (left right : Affine)
    (hleft : AffineOnCurve left) (hright : AffineOnCurve right)
    (hx : left.x ≠ right.x) :
    AffineOnCurve (differenceAffine left right) := by
  let leftNonsingular := affine_nonsingular left hleft
  let rightNonsingular := affine_nonsingular (negAffine right)
    (negAffine_onCurve right hright)
  have hsum := BN254.curve.toAffine.nonsingular_add
    leftNonsingular rightNonsingular (fun h => hx h.1)
  have hequation :
      BN254.curve.toAffine.Equation
        (differenceAffine left right).x
        (differenceAffine left right).y := by
    simpa [differenceAffine, negAffine] using hsum.left
  rw [WeierstrassCurve.Affine.equation_iff] at hequation
  simpa [AffineOnCurve, BN254.curve] using hequation.symm

/-- Rewrite form of the affine curve equation. -/
theorem AffineOnCurve.x_cub_eq {point : Affine}
    (hpoint : AffineOnCurve point) :
    point.x ^ 3 = point.y ^ 2 - curveB :=
  eq_sub_of_add_eq hpoint

/-- The RCB denominator is the denominator-cleared ordinate of the genuine
difference point.  This identity is the concrete exceptional-locus audit. -/
theorem formula_z_eq_neg_cube_mul_difference_y
    (left right : Affine)
    (hleft : AffineOnCurve left) (hright : AffineOnCurve right)
    (hx : left.x ≠ right.x) :
    (addFormula (ofAffine left) (ofAffine right)).z =
      -(left.x - right.x) ^ 3 * (differenceAffine left right).y := by
  simp only [differenceAffine]
  rw [show BN254.curve.toAffine.slope
      left.x right.x left.y (-right.y) =
      (left.y + right.y) / (left.x - right.x) by
    rw [WeierstrassCurve.Affine.slope_of_X_ne hx]
    ring]
  simp only [WeierstrassCurve.Affine.addX,
    WeierstrassCurve.Affine.addY,
    WeierstrassCurve.Affine.negAddY,
    WeierstrassCurve.Affine.negY]
  simp only [BN254.curve, zero_mul, zero_add, sub_zero]
  simp only [addFormula, HomogeneousRCB.formula, ofAffine]
  field_simp [sub_ne_zero.mpr hx]
  linear_combination (norm := ring)
    (left.y + 2 * right.y) * hleft +
      (2 * left.y + right.y) * hright

theorem formula_z_ne_zero_of_x_ne
    (left right : Affine)
    (hleft : AffineOnCurve left) (hright : AffineOnCurve right)
    (hx : left.x ≠ right.x) :
    (addFormula (ofAffine left) (ofAffine right)).z ≠ 0 := by
  rw [formula_z_eq_neg_cube_mul_difference_y left right hleft hright hx]
  exact mul_ne_zero
    (neg_ne_zero.mpr (pow_ne_zero 3 (sub_ne_zero.mpr hx)))
    (affine_y_ne_zero (differenceAffine left right)
      (differenceAffine_onCurve left right hleft hright hx))

/-- The normalized RCB abscissa is the ordinary secant-addition abscissa. -/
theorem normalize_formula_x_of_x_ne
    (left right : Affine)
    (hleft : AffineOnCurve left) (hright : AffineOnCurve right)
    (hx : left.x ≠ right.x) :
    (addFormula (ofAffine left) (ofAffine right)).x /
        (addFormula (ofAffine left) (ofAffine right)).z =
      BN254.curve.toAffine.addX left.x right.x
        (BN254.curve.toAffine.slope
          left.x right.x left.y right.y) := by
  have hz := formula_z_ne_zero_of_x_ne left right hleft hright hx
  have hxsub := sub_ne_zero.mpr hx
  rw [div_eq_iff hz, WeierstrassCurve.Affine.slope_of_X_ne hx]
  simp only [BN254.curve, WeierstrassCurve.Affine.addX,
    zero_mul, sub_zero, addFormula, HomogeneousRCB.formula, ofAffine]
  -- Clear the secant-denominator, then finish by the curve equations.
  refine mul_left_cancel₀ (pow_ne_zero 2 hxsub) ?_
  field_simp [hxsub]
  grind

/-- Once the abscissa is fixed, the RCB ordinate lies on the same secant
line as the ordinary affine sum. -/
theorem normalize_formula_y_line_of_x_ne
    (left right : Affine)
    (hleft : AffineOnCurve left) (hright : AffineOnCurve right)
    (hx : left.x ≠ right.x) :
    (addFormula (ofAffine left) (ofAffine right)).y /
        (addFormula (ofAffine left) (ofAffine right)).z =
      BN254.curve.toAffine.slope left.x right.x left.y right.y *
          (left.x -
            (addFormula (ofAffine left) (ofAffine right)).x /
              (addFormula (ofAffine left) (ofAffine right)).z) -
        left.y := by
  have hz := formula_z_ne_zero_of_x_ne left right hleft hright hx
  have hxsub := sub_ne_zero.mpr hx
  rw [div_eq_iff hz, normalize_formula_x_of_x_ne left right hleft hright hx,
    WeierstrassCurve.Affine.slope_of_X_ne hx]
  simp only [BN254.curve, WeierstrassCurve.Affine.addX,
    zero_mul, sub_zero, addFormula, HomogeneousRCB.formula, ofAffine]
  refine mul_left_cancel₀ hxsub ?_
  field_simp [hxsub]
  grind

theorem normalize_formula_y_of_x_ne
    (left right : Affine)
    (hleft : AffineOnCurve left) (hright : AffineOnCurve right)
    (hx : left.x ≠ right.x) :
    (addFormula (ofAffine left) (ofAffine right)).y /
        (addFormula (ofAffine left) (ofAffine right)).z =
      BN254.curve.toAffine.addY left.x right.x left.y
        (BN254.curve.toAffine.slope
          left.x right.x left.y right.y) := by
  rw [normalize_formula_y_line_of_x_ne left right hleft hright hx]
  simp [WeierstrassCurve.Affine.addY,
    WeierstrassCurve.Affine.negAddY,
    WeierstrassCurve.Affine.negY, BN254.curve,
    normalize_formula_x_of_x_ne left right hleft hright hx]
  ring

/-! ## Doubling and inverse branches -/

private theorem eight_ne_zero : (8 : Field) ≠ 0 := by
  intro hzero
  have hdiv : baseFieldModulus ∣ 8 :=
    (ZMod.natCast_eq_zero_iff 8 baseFieldModulus).mp hzero
  norm_num [baseFieldModulus] at hdiv

theorem formula_affine_self (point : Affine)
    (hpoint : AffineOnCurve point) :
    addFormula (ofAffine point) (ofAffine point) =
      { x := 2 * point.x * point.y *
          (point.y ^ 2 - 9 * curveB)
        y := point.y ^ 4 + 18 * curveB * point.y ^ 2 -
          27 * curveB ^ 2
        z := 8 * point.y ^ 3 } := by
  apply HomogeneousRCB.Point.ext
  · -- X is an identity of the RCB polynomial alone.
    simp [addFormula, HomogeneousRCB.formula, ofAffine]
    ring
  · simp [addFormula, HomogeneousRCB.formula, ofAffine,
      curveB]
    linear_combination (norm := ring) (18 * curveB) * hpoint
  · simp [addFormula, HomogeneousRCB.formula, ofAffine,
      curveB]
    linear_combination (norm := ring) (6 * point.y) * hpoint

theorem formula_self_z_ne_zero (point : Affine)
    (hpoint : AffineOnCurve point) :
    (addFormula (ofAffine point) (ofAffine point)).z ≠ 0 := by
  rw [formula_affine_self point hpoint]
  exact mul_ne_zero eight_ne_zero
    (pow_ne_zero 3 (affine_y_ne_zero point hpoint))

theorem normalize_formula_self_x (point : Affine)
    (hpoint : AffineOnCurve point) :
    (addFormula (ofAffine point) (ofAffine point)).x /
        (addFormula (ofAffine point) (ofAffine point)).z =
      BN254.curve.toAffine.addX point.x point.x
        (BN254.curve.toAffine.slope
          point.x point.x point.y point.y) := by
  have hy := affine_y_ne_zero point hpoint
  have hyNeg := affine_y_ne_negY point hpoint
  rw [formula_affine_self point hpoint,
    WeierstrassCurve.Affine.slope_of_Y_ne rfl hyNeg]
  simp only [BN254.curve, WeierstrassCurve.Affine.addX,
    WeierstrassCurve.Affine.negY, zero_mul, sub_zero]
  have hyTwice : point.y - -point.y = 2 * point.y := by ring
  simp only [hyTwice]
  -- Match the Trace doubling pattern: clear dens, then use the curve.
  field_simp [hy, two_ne_zero, eight_ne_zero]
  linear_combination (norm := ring) (-72 * point.x) * hpoint

set_option maxHeartbeats 800000 in
theorem normalize_formula_self_y_line (point : Affine)
    (hpoint : AffineOnCurve point) :
    (addFormula (ofAffine point) (ofAffine point)).y /
        (addFormula (ofAffine point) (ofAffine point)).z =
      BN254.curve.toAffine.slope point.x point.x point.y point.y *
          (point.x -
            (addFormula (ofAffine point) (ofAffine point)).x /
              (addFormula (ofAffine point) (ofAffine point)).z) -
        point.y := by
  have hy := affine_y_ne_zero point hpoint
  have hyNeg := affine_y_ne_negY point hpoint
  rw [normalize_formula_self_x point hpoint]
  rw [formula_affine_self point hpoint,
    WeierstrassCurve.Affine.slope_of_Y_ne rfl hyNeg]
  simp only [BN254.curve, WeierstrassCurve.Affine.addX,
    WeierstrassCurve.Affine.negY, zero_mul, sub_zero]
  have hyTwice : point.y - -point.y = 2 * point.y := by ring
  simp only [hyTwice]
  field_simp [hy, two_ne_zero, eight_ne_zero]
  linear_combination (norm := ring)
    (216 * point.x ^ 3 - 216 * curveB - 54 * point.y * curveB -
        72 * point.y ^ 2 - 18 * point.y ^ 3) * hpoint
  linear_combination (norm := ring)
    (54 * point.y * curveB + 18 * point.y ^ 3) * hpoint

theorem normalize_formula_self_y (point : Affine)
    (hpoint : AffineOnCurve point) :
    (addFormula (ofAffine point) (ofAffine point)).y /
        (addFormula (ofAffine point) (ofAffine point)).z =
      BN254.curve.toAffine.addY point.x point.x point.y
        (BN254.curve.toAffine.slope
          point.x point.x point.y point.y) := by
  rw [normalize_formula_self_y_line point hpoint]
  simp [WeierstrassCurve.Affine.addY,
    WeierstrassCurve.Affine.negAddY,
    WeierstrassCurve.Affine.negY, BN254.curve,
    normalize_formula_self_x point hpoint]
  ring

theorem formula_affine_neg (point : Affine)
    (hpoint : AffineOnCurve point) :
    addFormula (ofAffine point) (ofAffine (negAffine point)) =
      { x := 0
        y := point.y ^ 4 + 18 * curveB * point.y ^ 2 -
          27 * curveB ^ 2
        z := 0 } := by
  apply HomogeneousRCB.Point.ext
  · simp [addFormula, HomogeneousRCB.formula, ofAffine, negAffine]
  · simp [addFormula, HomogeneousRCB.formula, ofAffine, negAffine,
      curveB]
    linear_combination (norm := ring) (18 * curveB) * hpoint
  · simp [addFormula, HomogeneousRCB.formula, ofAffine, negAffine]

/-- The ordinary-homogeneous infinity returned by the inverse branch has a
nonzero `Y` pivot. This closes the representative-alignment case that the
Jacobian zero-`Z` canonicalization deliberately forgets. -/
theorem formula_affine_neg_y_ne_zero (point : Affine)
    (hpoint : AffineOnCurve point) :
    point.y ^ 4 + 18 * curveB * point.y ^ 2 - 27 * curveB ^ 2 ≠ 0 := by
  intro hzero
  have hequation : point.y ^ 4 + 54 * point.y ^ 2 - 243 = 0 := by
    norm_num [curveB] at hzero ⊢
    exact hzero
  have heighteen : (18 : Field) ≠ 0 := by
    intro h
    have hdiv : baseFieldModulus ∣ 18 :=
      (ZMod.natCast_eq_zero_iff 18 baseFieldModulus).mp h
    norm_num [baseFieldModulus] at hdiv
  apply three_not_square ((point.y ^ 2 + 27) / 18)
  rw [div_pow]
  field_simp [heighteen]
  linear_combination hequation

/-! ## Point-class correctness -/

private theorem class_formula_infinity_infinity :
    (⟦toJacobian (addFormula infinity infinity)⟧ : JacobianClass) =
      BN254.curve.toJacobian.addMap
        ⟦inputJacobian none⟧ ⟦inputJacobian none⟧ := by
  rw [formula_infinity_infinity, toJacobian_infinity]
  change (⟦![(1 : Field), 1, 0]⟧ : JacobianClass) =
    BN254.curve.toJacobian.addMap
      ⟦![(1 : Field), 1, 0]⟧ ⟦![(1 : Field), 1, 0]⟧
  have hinfinity : BN254.curve.toJacobian.Nonsingular
      ![(1 : Field), 1, 0] :=
    BN254.curve.toJacobian.nonsingular_zero
  have hinfinityLift : BN254.curve.toJacobian.NonsingularLift
      (⟦![(1 : Field), 1, 0]⟧ : JacobianClass) :=
    (BN254.curve.toJacobian.nonsingularLift_iff _).2 hinfinity
  exact (BN254.curve.toJacobian.addMap_of_Z_eq_zero_left
    hinfinity hinfinityLift rfl).symm

private theorem normalized_of_mul_y (point : Affine) (hy : point.y ≠ 0) :
    (![point.x * point.y / point.y,
        point.y ^ 2 / point.y, (1 : Field)] : JacobianCoordinates) =
      inputJacobian (some point) := by
  refine funext fun index => ?_
  fin_cases index
  · exact mul_div_cancel_right₀ _ hy
  · -- `y^2 / y = y`
    change point.y ^ 2 / point.y = point.y
    field_simp [hy]
  · rfl

private theorem class_formula_infinity_left (point : Affine)
    (hpoint : AffineOnCurve point) :
    (⟦toJacobian (addFormula infinity (ofAffine point))⟧ : JacobianClass) =
      BN254.curve.toJacobian.addMap
        ⟦inputJacobian none⟧ ⟦inputJacobian (some point)⟧ := by
  have hy := affine_y_ne_zero point hpoint
  rw [formula_infinity_affine, pointClass_toJacobian_eq_normalized _ hy,
    normalized_of_mul_y point hy]
  exact (BN254.curve.toJacobian.addMap_of_Z_eq_zero_left
    BN254.curve.toJacobian.nonsingular_zero
    ((BN254.curve.toJacobian.nonsingularLift_iff _).2
      (affineJacobian_valid point hpoint)) rfl).symm

private theorem class_formula_infinity_right (point : Affine)
    (hpoint : AffineOnCurve point) :
    (⟦toJacobian (addFormula (ofAffine point) infinity)⟧ : JacobianClass) =
      BN254.curve.toJacobian.addMap
        ⟦inputJacobian (some point)⟧ ⟦inputJacobian none⟧ := by
  have hy := affine_y_ne_zero point hpoint
  rw [formula_affine_infinity, pointClass_toJacobian_eq_normalized _ hy,
    normalized_of_mul_y point hy]
  exact (BN254.curve.toJacobian.addMap_of_Z_eq_zero_right
    ((BN254.curve.toJacobian.nonsingularLift_iff _).2
      (affineJacobian_valid point hpoint))
    BN254.curve.toJacobian.nonsingular_zero rfl).symm

/-- Componentwise normalized RCB sum equals the ordinary affine sum vector. -/
theorem normalize_formula_vec_of_x_ne
    (left right : Affine)
    (hleft : AffineOnCurve left) (hright : AffineOnCurve right)
    (hx : left.x ≠ right.x) :
    (![ (addFormula (ofAffine left) (ofAffine right)).x /
          (addFormula (ofAffine left) (ofAffine right)).z,
        (addFormula (ofAffine left) (ofAffine right)).y /
          (addFormula (ofAffine left) (ofAffine right)).z,
        (1 : Field)] : JacobianCoordinates) =
      ![BN254.curve.toAffine.addX left.x right.x
          (BN254.curve.toAffine.slope left.x right.x left.y right.y),
        BN254.curve.toAffine.addY left.x right.x left.y
          (BN254.curve.toAffine.slope left.x right.x left.y right.y),
        (1 : Field)] :=
  congrArg₂ (fun x y : Field => (![x, y, (1 : Field)] : JacobianCoordinates))
    (normalize_formula_x_of_x_ne left right hleft hright hx)
    (normalize_formula_y_of_x_ne left right hleft hright hx)

/-- Componentwise normalized RCB doubling equals the ordinary affine double. -/
theorem normalize_formula_vec_self
    (point : Affine) (hpoint : AffineOnCurve point) :
    (![ (addFormula (ofAffine point) (ofAffine point)).x /
          (addFormula (ofAffine point) (ofAffine point)).z,
        (addFormula (ofAffine point) (ofAffine point)).y /
          (addFormula (ofAffine point) (ofAffine point)).z,
        (1 : Field)] : JacobianCoordinates) =
      ![BN254.curve.toAffine.addX point.x point.x
          (BN254.curve.toAffine.slope point.x point.x point.y point.y),
        BN254.curve.toAffine.addY point.x point.x point.y
          (BN254.curve.toAffine.slope point.x point.x point.y point.y),
        (1 : Field)] :=
  congrArg₂ (fun x y : Field => (![x, y, (1 : Field)] : JacobianCoordinates))
    (normalize_formula_self_x point hpoint)
    (normalize_formula_self_y point hpoint)

/-- Distinct-abscissa class glue via the generic `Z = 1` `addMap` helper. -/
private theorem class_formula_affine_of_x_ne
    (left right : Affine)
    (hleft : AffineOnCurve left) (hright : AffineOnCurve right)
    (hx : left.x ≠ right.x) :
    (⟦toJacobian (addFormula (ofAffine left) (ofAffine right))⟧ :
        JacobianClass) =
      BN254.curve.toJacobian.addMap
        ⟦inputJacobian (some left)⟧
        ⟦inputJacobian (some right)⟧ := by
  have hz := formula_z_ne_zero_of_x_ne left right hleft hright hx
  have hnorm := pointClass_toJacobian_eq_normalized
    (addFormula (ofAffine left) (ofAffine right)) hz
  have hsum :=
    GarblingPrize.Submission.JacobianAffineAddMap.addMap_of_X_ne (W := BN254.curve)
      left.x left.y right.x right.y
      (affineJacobian_valid left hleft).left
      (affineJacobian_valid right hright).left hx
  rw [hnorm, show inputJacobian (some left) = ![left.x, left.y, 1] from rfl,
    show inputJacobian (some right) = ![right.x, right.y, 1] from rfl, hsum,
    normalize_formula_vec_of_x_ne left right hleft hright hx]

/-- Doubling class glue via the generic `Z = 1` `addMap` helper. -/
private theorem class_formula_affine_self (point : Affine)
    (hpoint : AffineOnCurve point) :
    (⟦toJacobian (addFormula (ofAffine point) (ofAffine point))⟧ :
        JacobianClass) =
      BN254.curve.toJacobian.addMap
        ⟦inputJacobian (some point)⟧
        ⟦inputJacobian (some point)⟧ := by
  have hz := formula_self_z_ne_zero point hpoint
  have hnorm := pointClass_toJacobian_eq_normalized
    (addFormula (ofAffine point) (ofAffine point)) hz
  have hsum :=
    GarblingPrize.Submission.JacobianAffineAddMap.addMap_of_Y_ne_negY (W := BN254.curve)
      point.x point.y
      (affineJacobian_valid point hpoint).left
      (affine_y_ne_negY point hpoint)
  rw [hnorm, show inputJacobian (some point) = ![point.x, point.y, 1] from rfl,
    hsum, normalize_formula_vec_self point hpoint]

private theorem class_formula_affine_neg (point : Affine)
    (hpoint : AffineOnCurve point) :
    (⟦toJacobian (addFormula (ofAffine point)
        (ofAffine (negAffine point)))⟧ : JacobianClass) =
      BN254.curve.toJacobian.addMap
        ⟦inputJacobian (some point)⟧
        ⟦inputJacobian (some (negAffine point))⟧ := by
  rw [formula_affine_neg point hpoint]
  change (⟦![(1 : Field), 1, 0]⟧ : JacobianClass) =
    BN254.curve.toJacobian.addMap
      ⟦![point.x, point.y, (1 : Field)]⟧
      ⟦![point.x, -point.y, (1 : Field)]⟧
  refine (BN254.curve.toJacobian.addMap_of_Y_eq
    (affineJacobian_valid point hpoint)
    (affineJacobian_valid (negAffine point)
      (negAffine_onCurve point hpoint)).left
    (by simp) (by simp) (by simp [negAffine]) ?_).symm
  simp [negAffine, BN254.curve, WeierstrassCurve.Jacobian.negY,
    WeierstrassCurve.Affine.negY]

private theorem class_formula_affine (left right : Affine)
    (hleft : AffineOnCurve left) (hright : AffineOnCurve right) :
    (⟦toJacobian (addFormula (ofAffine left) (ofAffine right))⟧ :
        JacobianClass) =
      BN254.curve.toJacobian.addMap
        ⟦inputJacobian (some left)⟧
        ⟦inputJacobian (some right)⟧ := by
  by_cases hx : left.x = right.x
  · have hySquare : left.y ^ 2 = right.y ^ 2 := by
      calc
        left.y ^ 2 = left.x ^ 3 + curveB := hleft.symm
        _ = right.x ^ 3 + curveB := by rw [hx]
        _ = right.y ^ 2 := hright
    rcases eq_or_eq_neg_of_sq_eq_sq left.y right.y hySquare with hy | hy
    · have hpoints : right = left := by
        cases left with
        | mk leftX leftY =>
            cases right with
            | mk rightX rightY =>
                simp only at hx hy
                subst rightX
                subst rightY
                rfl
      subst right
      exact class_formula_affine_self left hleft
    · have hpoints : right = negAffine left := by
        cases left with
        | mk leftX leftY =>
            cases right with
            | mk rightX rightY =>
                simp only at hx hy
                subst rightX
                simp only [negAffine]
                congr
                have hneg := congrArg (fun value : Field => -value) hy
                simpa using hneg.symm
      subst right
      exact class_formula_affine_neg left hleft
  · exact class_formula_affine_of_x_ne left right hleft hright hx

/-- Main total group-law theorem on the exact executable domain.  It has no
generic completeness postulate: the BN254 no-two-torsion certificate is consumed
inside the distinct-abscissa proof above. -/
theorem pointClass_formula (left right : Option Affine)
    (hleft : InputOnCurve left) (hright : InputOnCurve right) :
    (⟦toJacobian (addFormula (encode left) (encode right))⟧ :
        JacobianClass) =
      BN254.curve.toJacobian.addMap
        ⟦inputJacobian left⟧ ⟦inputJacobian right⟧ := by
  cases left with
  | none =>
      cases right with
      | none =>
          exact class_formula_infinity_infinity
      | some point =>
          exact class_formula_infinity_left point hright
  | some leftPoint =>
      cases right with
      | none =>
          exact class_formula_infinity_right leftPoint hleft
      | some rightPoint =>
          exact class_formula_affine leftPoint rightPoint hleft hright

/-- Every exact executable RCB output becomes a valid concrete Jacobian
representative after the specified zero-`Z` canonicalization. -/
theorem toJacobian_formula_valid (left right : Option Affine)
    (hleft : InputOnCurve left) (hright : InputOnCurve right) :
    BN254.curve.toJacobian.Nonsingular
      (toJacobian (addFormula (encode left) (encode right))) := by
  have hclass := pointClass_formula left right hleft hright
  have hlift : BN254.curve.toJacobian.NonsingularLift
      (⟦toJacobian (addFormula (encode left) (encode right))⟧ :
        JacobianClass) := by
    rw [hclass]
    exact BN254.curve.toJacobian.nonsingularLift_addMap
      ((BN254.curve.toJacobian.nonsingularLift_iff _).2
        (inputJacobian_valid left hleft))
      ((BN254.curve.toJacobian.nonsingularLift_iff _).2
        (inputJacobian_valid right hright))
  exact (BN254.curve.toJacobian.nonsingularLift_iff _).1 hlift

end

end GarblingPrize.Submission.HomogeneousRCBG1GroupLaw
