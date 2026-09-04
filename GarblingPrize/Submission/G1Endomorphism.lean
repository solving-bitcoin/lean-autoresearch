import GarblingPrize.Protected.Target

namespace GarblingPrize.Submission.G1Endomorphism

open GarblingPrize.Protected
open WeierstrassCurve

abbrev Field := BN254.Fq
abbrev Point := BN254.G1

/-- The small primitive cube root used by the BN254 G1 GLV map. -/
def beta : Field :=
  2203960485148121921418603742825762020974279258880205651966

theorem beta_pow_three : beta ^ 3 = 1 := by
  decide

theorem beta_ne_zero : beta ≠ 0 := by
  intro h
  have := congrArg (fun value : Field => value ^ 3) h
  simpa [beta_pow_three] using this

theorem beta_sq_mul_beta : beta ^ 2 * beta = 1 := by
  simpa [pow_succ] using beta_pow_three

/-- Coordinate action `(x,y) |-> (beta*x,y)` on the complete affine group. -/
def phi : Point -> Point
  | .zero => 0
  | @WeierstrassCurve.Affine.Point.some _ _ _ x y h =>
      .some (beta * x) y (by
        apply (BN254.curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero
          BN254.discriminant_ne_zero).mp
        have heq :=
          (BN254.curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero
            BN254.discriminant_ne_zero).mpr h
        rw [WeierstrassCurve.Affine.equation_iff] at heq ⊢
        simp only [BN254.curve, zero_mul, zero_add]
        rw [mul_pow, beta_pow_three, one_mul]
        simpa [BN254.curve] using heq)

@[simp] theorem phi_zero : phi 0 = 0 := rfl

@[simp] theorem phi_some {x y : Field}
    (h : BN254.curve.toAffine.Nonsingular x y) :
    phi (.some x y h) = .some (beta * x) y (by
      apply (BN254.curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero
        BN254.discriminant_ne_zero).mp
      have heq :=
        (BN254.curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero
          BN254.discriminant_ne_zero).mpr h
      rw [WeierstrassCurve.Affine.equation_iff] at heq ⊢
      simp only [BN254.curve, zero_mul, zero_add]
      rw [mul_pow, beta_pow_three, one_mul]
      simpa [BN254.curve] using heq) := rfl

private theorem beta_mul_injective : Function.Injective (beta * ·) := by
  intro left right h
  exact (mul_left_cancel₀ beta_ne_zero h)

private theorem negY_eq (x y : Field) :
    BN254.curve.toAffine.negY x y = -y := by
  simp [BN254.curve, WeierstrassCurve.Affine.negY]

private theorem scaled_slope (x₁ x₂ y₁ y₂ : Field)
    (hnotInverse : ¬(x₁ = x₂ ∧
      y₁ = BN254.curve.toAffine.negY x₂ y₂)) :
    BN254.curve.toAffine.slope (beta * x₁) (beta * x₂) y₁ y₂ =
      beta ^ 2 * BN254.curve.toAffine.slope x₁ x₂ y₁ y₂ := by
  by_cases hx : x₁ = x₂
  · subst x₂
    have hy : y₁ ≠ BN254.curve.toAffine.negY x₁ y₂ := by
      intro h
      exact hnotInverse ⟨rfl, h⟩
    have hyScaled : y₁ ≠
        BN254.curve.toAffine.negY (beta * x₁) y₂ := by
      simpa [BN254.curve, WeierstrassCurve.Affine.negY] using hy
    rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hy,
      WeierstrassCurve.Affine.slope_of_Y_ne rfl hyScaled]
    simp only [BN254.curve, zero_mul, add_zero, sub_zero,
      WeierstrassCurve.Affine.negY]
    ring
  · have hxScaled : beta * x₁ ≠ beta * x₂ := by
      exact fun h => hx (beta_mul_injective h)
    rw [WeierstrassCurve.Affine.slope_of_X_ne hx,
      WeierstrassCurve.Affine.slope_of_X_ne hxScaled]
    rw [show beta * x₁ - beta * x₂ = beta * (x₁ - x₂) by ring,
      div_eq_mul_inv, mul_inv_rev, show beta⁻¹ = beta ^ 2 by
      exact (eq_inv_of_mul_eq_one_left beta_sq_mul_beta).symm]
    ring

private theorem scaled_addX (x₁ x₂ y₁ y₂ : Field)
    (hnotInverse : ¬(x₁ = x₂ ∧
      y₁ = BN254.curve.toAffine.negY x₂ y₂)) :
    BN254.curve.toAffine.addX (beta * x₁) (beta * x₂)
        (BN254.curve.toAffine.slope (beta * x₁) (beta * x₂) y₁ y₂) =
      beta * BN254.curve.toAffine.addX x₁ x₂
        (BN254.curve.toAffine.slope x₁ x₂ y₁ y₂) := by
  rw [scaled_slope x₁ x₂ y₁ y₂ hnotInverse]
  simp only [WeierstrassCurve.Affine.addX, BN254.curve, zero_mul,
    zero_add, add_zero, sub_zero]
  let slope := BN254.curve.toAffine.slope x₁ x₂ y₁ y₂
  have hscaled : (beta ^ 2 * slope) ^ 2 = beta * slope ^ 2 := by
    calc
      (beta ^ 2 * slope) ^ 2 = beta ^ 3 * beta * slope ^ 2 := by ring
      _ = beta * slope ^ 2 := by rw [beta_pow_three, one_mul]
  change (beta ^ 2 * slope) ^ 2 - beta * x₁ - beta * x₂ =
    beta * (slope ^ 2 - x₁ - x₂)
  rw [hscaled]
  ring

private theorem scaled_addY (x₁ x₂ y₁ y₂ : Field)
    (hnotInverse : ¬(x₁ = x₂ ∧
      y₁ = BN254.curve.toAffine.negY x₂ y₂)) :
    BN254.curve.toAffine.addY (beta * x₁) (beta * x₂) y₁
        (BN254.curve.toAffine.slope (beta * x₁) (beta * x₂) y₁ y₂) =
      BN254.curve.toAffine.addY x₁ x₂ y₁
        (BN254.curve.toAffine.slope x₁ x₂ y₁ y₂) := by
  have hx := scaled_addX x₁ x₂ y₁ y₂ hnotInverse
  rw [scaled_slope x₁ x₂ y₁ y₂ hnotInverse] at hx ⊢
  unfold WeierstrassCurve.Affine.addY
  simp only [negY_eq, WeierstrassCurve.Affine.negAddY]
  rw [hx]
  have hterm :
      beta ^ 2 * BN254.curve.toAffine.slope x₁ x₂ y₁ y₂ *
          (beta * BN254.curve.toAffine.addX x₁ x₂
              (BN254.curve.toAffine.slope x₁ x₂ y₁ y₂) - beta * x₁) =
        BN254.curve.toAffine.slope x₁ x₂ y₁ y₂ *
          (BN254.curve.toAffine.addX x₁ x₂
              (BN254.curve.toAffine.slope x₁ x₂ y₁ y₂) - x₁) := by
    calc
      _ = beta ^ 3 *
          (BN254.curve.toAffine.slope x₁ x₂ y₁ y₂ *
            (BN254.curve.toAffine.addX x₁ x₂
              (BN254.curve.toAffine.slope x₁ x₂ y₁ y₂) - x₁)) := by ring
      _ = _ := by rw [beta_pow_three, one_mul]
  rw [hterm]

theorem phi_add (left right : Point) :
    phi (left + right) = phi left + phi right := by
  cases left with
  | zero => rfl
  | @some x₁ y₁ h₁ =>
    cases right with
    | zero => rfl
    | @some x₂ y₂ h₂ =>
      by_cases hxy : x₁ = x₂ ∧
          y₁ = BN254.curve.toAffine.negY x₂ y₂
      · rw [WeierstrassCurve.Affine.Point.add_of_Y_eq hxy.1 hxy.2]
        simp only [phi_zero, phi_some]
        symm
        apply WeierstrassCurve.Affine.Point.add_of_Y_eq
        · exact congrArg (beta * ·) hxy.1
        · simpa [BN254.curve, WeierstrassCurve.Affine.negY] using hxy.2
      · rw [WeierstrassCurve.Affine.Point.add_some hxy]
        simp only [phi_some]
        have hxyScaled : ¬(beta * x₁ = beta * x₂ ∧
            y₁ = BN254.curve.toAffine.negY (beta * x₂) y₂) := by
          intro h
          apply hxy
          exact ⟨beta_mul_injective h.1, by
            simpa [BN254.curve, WeierstrassCurve.Affine.negY] using h.2⟩
        rw [WeierstrassCurve.Affine.Point.add_some hxyScaled]
        congr 1
        · exact (scaled_addX x₁ x₂ y₁ y₂ hxy).symm
        · exact (scaled_addY x₁ x₂ y₁ y₂ hxy).symm

/-- The coordinate automorphism as a genuine additive endomorphism. -/
def phiHom : Point →+ Point where
  toFun := phi
  map_zero' := rfl
  map_add' := phi_add

end GarblingPrize.Submission.G1Endomorphism
