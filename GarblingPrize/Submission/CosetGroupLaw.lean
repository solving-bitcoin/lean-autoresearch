import GarblingPrize.Submission.CosetCoordinates
import GarblingPrize.Submission.FourAffineQuotient

namespace GarblingPrize.Submission.CosetGroupLaw

/-! The non-rational translate is a genuine group translate. Associativity
then makes ordinary distinct-abscissa addition complete on the coset, even
when the corresponding base-field sum is infinity or a doubling. -/

open GarblingPrize.Protected
open CosetCoordinates
open scoped QuadraticAlgebra

abbrev curve : WeierstrassCurve K := BN254.curve.map C
abbrev ExtensionPoint := curve.toAffine.Point

theorem discriminant_ne_zero : curve.Δ ≠ 0 := by
  rw [WeierstrassCurve.map_Δ]
  exact (map_ne_zero C).mpr BN254.discriminant_ne_zero

theorem equation_iff (x y : K) : curve.toAffine.Equation x y ↔ y ^ 2 = x ^ 3 + 3 := by
  rw [WeierstrassCurve.Affine.equation_iff]
  change y ^ 2 + 0 * x * y + 0 * y = x ^ 3 + 0 * x ^ 2 + 0 * x +
    (⟨3, 0⟩ : K) ↔ _
  have hc : (⟨3, 0⟩ : K) = 3 := by ext <;> norm_num
  simp [hc]

def finite (x y : K) (h : y ^ 2 = x ^ 3 + 3) : ExtensionPoint :=
  .some x y ((curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero
    discriminant_ne_zero).mp ((equation_iff x y).mpr h))

def shift : ExtensionPoint := finite 0 sqrtThree (by simp)

noncomputable def embed : BN254.G1 →+ ExtensionPoint :=
  WeierstrassCurve.Affine.Point.map (W' := BN254.curve.toAffine) (Algebra.ofId Word K)

def translated (point : Point) : ExtensionPoint :=
  finite (encode point) (shiftedY point) (shifted_onCurve point)

set_option backward.isDefEq.respectTransparency false in
theorem translated_eq (point : Point) :
    translated point = shift + embed (RuntimeG1.toPoint point) := by
  rcases point with ⟨point, hpoint⟩
  cases point with
  | none => simp [translated, encode, shiftedY, RuntimeG1.toPoint, shift]
  | some point =>
    have hx := affine_x_ne_zero point hpoint
    have hx' : (0 : K) ≠ C point.x := by
      intro h
      exact hx (congrArg QuadraticAlgebra.re h.symm)
    change finite (encodeAffine point) (shiftedYAffine point) _ =
      finite 0 sqrtThree _ + .some (C point.x) (C point.y) _
    unfold finite
    rw [WeierstrassCurve.Affine.Point.add_of_X_ne (W := curve.toAffine) hx']
    rw [WeierstrassCurve.Affine.Point.some.injEq]
    rw [WeierstrassCurve.Affine.slope_of_X_ne hx']
    simp only [WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.addY,
      WeierstrassCurve.Affine.negY, curve, BN254.curve, WeierstrassCurve.map,
      map_zero, zero_mul, zero_add, add_zero, sub_zero, zero_sub]
    change point.x ^ 3 + 3 = point.y ^ 2 at hpoint
    simp only [div_eq_mul_inv, ← map_neg, ← map_inv₀]
    constructor
    · ext <;> simp [encodeAffine, C, sqrtThree, pow_two,
        QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul,
        QuadraticAlgebra.algebraMap_eq] <;> field_simp
      · linear_combination hpoint
      · ring
    · ext <;> simp [shiftedYAffine, C, sqrtThree, pow_two,
        QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul,
        QuadraticAlgebra.algebraMap_eq] <;> field_simp
      · linear_combination -point.y * hpoint
      · linear_combination 3 * hpoint

def abscissa : ExtensionPoint → K
  | .zero => 0
  | .some x _ _ => x

theorem translated_add (offset result : Point) (input : BN254.G1)
    (hsum : RuntimeG1.toPoint result = RuntimeG1.toPoint offset + input) :
    translated offset + embed input = translated result := by
  rw [translated_eq, translated_eq, hsum, map_add, add_assoc]

theorem addition_quotient {L : Type*} [Field L] (a b x y : L)
    (hb : b ^ 2 = a ^ 3 + 3) (hp : y ^ 2 = x ^ 3 + 3) (hd : x - a ≠ 0) :
    ((y - b) / (x - a)) ^ 2 - a - x =
      (a * x ^ 2 + a ^ 2 * x - 2 * b * y + 6) / (x - a) ^ 2 := by
  calc
    _ = ((y - b) ^ 2 - (a + x) * (x - a) ^ 2) / (x - a) ^ 2 := by
      field_simp
      ring
    _ = _ := by
      congr 1
      linear_combination hb + hp

set_option backward.isDefEq.respectTransparency false in
theorem add_abscissa (offset : Point) (input : Affine)
    (hinput : HomogeneousRCBG1GroupLaw.AffineOnCurve input) :
    abscissa (translated offset + embed (RuntimeG1.toPoint (RuntimeG1.ofAffine input hinput))) =
      (encode offset * C input.x ^ 2 + encode offset ^ 2 * C input.x -
        2 * shiftedY offset * C input.y + 6) / (C input.x - encode offset) ^ 2 := by
  have hd := base_abscissa_ne offset input.x (affine_x_ne_zero input hinput)
  have hx : encode offset ≠ C input.x := by
    intro heq
    exact hd (sub_eq_zero.mpr heq.symm)
  change abscissa (finite (encode offset) (shiftedY offset) _ +
    .some (C input.x) (C input.y) _) = _
  unfold finite
  rw [WeierstrassCurve.Affine.Point.add_of_X_ne (W := curve.toAffine) hx]
  simp only [abscissa, WeierstrassCurve.Affine.addX]
  rw [WeierstrassCurve.Affine.slope_of_X_ne hx]
  simp only [show curve.toAffine.a₁ = 0 from rfl, show curve.toAffine.a₂ = 0 from rfl,
    zero_mul, add_zero, sub_zero]
  change ((shiftedY offset - C input.y) / (encode offset - C input.x)) ^ 2 -
    encode offset - C input.x = _
  rw [show (shiftedY offset - C input.y) / (encode offset - C input.x) =
    (C input.y - shiftedY offset) / (C input.x - encode offset) by
      rw [← neg_sub (C input.y), ← neg_sub (C input.x), neg_div_neg_eq]]
  exact addition_quotient _ _ _ _ (shifted_onCurve offset)
    (affine_mapped_onCurve input hinput) hd

theorem quotient_encodes_sum (offset result : Point) (input : Affine)
    (hinput : HomogeneousRCBG1GroupLaw.AffineOnCurve input)
    (hsum : RuntimeG1.toPoint result = RuntimeG1.toPoint offset +
      RuntimeG1.toPoint (RuntimeG1.ofAffine input hinput)) :
    (encode offset * C input.x ^ 2 + encode offset ^ 2 * C input.x -
      2 * shiftedY offset * C input.y + 6) / (C input.x - encode offset) ^ 2 =
      encode result := by
  rw [← add_abscissa offset input hinput, translated_add offset result _ hsum]
  rfl

end GarblingPrize.Submission.CosetGroupLaw
