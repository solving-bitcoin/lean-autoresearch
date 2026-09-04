import Mathlib.Algebra.Polynomial.Roots
import Mathlib.GroupTheory.Perm.Cycle.Type
import CompPoly.Fields.BN254.Basic
import GarblingPrize.Submission.G1OrderCertificates

namespace GarblingPrize.Submission.G1Cardinality

open GarblingPrize.Protected
open Polynomial
open WeierstrassCurve

noncomputable section

abbrev Point := GarblingPrize.Protected.BN254.G1
abbrev Field := GarblingPrize.Protected.BN254.Fq

/-- Affine points are exactly infinity or a dependent pair of finite
coordinates satisfying nonsingularity. -/
private def pointEquiv :
    Point ≃ Unit ⊕ (Sigma fun x : Field =>
      { y : Field // GarblingPrize.Protected.BN254.curve.toAffine.Nonsingular x y }) where
  toFun
    | .zero => Sum.inl ()
    | @WeierstrassCurve.Affine.Point.some _ _ _ x y h =>
        Sum.inr ⟨x, ⟨y, h⟩⟩
  invFun
    | Sum.inl _ => .zero
    | Sum.inr ⟨x, ⟨y, h⟩⟩ => .some x y h
  left_inv := by
    intro point
    cases point <;> rfl
  right_inv := by
    intro value
    rcases value with (_ | ⟨x, ⟨y, h⟩⟩) <;> rfl

instance point_finite : Finite Point :=
  Finite.of_injective pointEquiv pointEquiv.injective

private def ordinatePolynomial (x : Field) : Field[X] :=
  X ^ 2 - C (x ^ 3 + 3)

private theorem nonsingular_mem_ordinateRoots (x y : Field)
    (hpoint : GarblingPrize.Protected.BN254.curve.toAffine.Nonsingular x y) :
    y ∈ (ordinatePolynomial x).rootSet Field := by
  apply (monic_X_pow_sub_C (x ^ 3 + 3)
    (by decide : (2 : Nat) ≠ 0)).mem_rootSet.mpr
  have hequation :
      GarblingPrize.Protected.BN254.curve.toAffine.Equation x y :=
    (GarblingPrize.Protected.BN254.curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero
        GarblingPrize.Protected.BN254.discriminant_ne_zero).mpr hpoint
  rw [WeierstrassCurve.Affine.equation_iff] at hequation
  simpa [ordinatePolynomial, GarblingPrize.Protected.BN254.curve] using
    sub_eq_zero.mpr hequation

private theorem ordinateFiber_card_le_two (x : Field) :
    Nat.card { y : Field //
      GarblingPrize.Protected.BN254.curve.toAffine.Nonsingular x y } ≤ 2 := by
  change Set.ncard
    { y : Field |
      GarblingPrize.Protected.BN254.curve.toAffine.Nonsingular x y } ≤ 2
  calc
    Set.ncard { y : Field |
        GarblingPrize.Protected.BN254.curve.toAffine.Nonsingular x y }
        ≤ Set.ncard ((ordinatePolynomial x).rootSet Field) := by
          apply Set.ncard_le_ncard
          · intro y hy
            exact nonsingular_mem_ordinateRoots x y hy
          · exact Polynomial.rootSet_finite (ordinatePolynomial x) Field
    _ ≤ (ordinatePolynomial x).natDegree :=
      Polynomial.ncard_rootSet_le (ordinatePolynomial x) Field
    _ = 2 := by exact natDegree_X_pow_sub_C

/-- Elementary quadratic-fiber point bound. -/
theorem pointCardinality_le_two_mul_base_add_one :
    Nat.card Point ≤ 2 * baseFieldModulus + 1 := by
  calc
    Nat.card Point = Nat.card
        (Unit ⊕ (Sigma fun x : Field =>
          { y : Field //
            GarblingPrize.Protected.BN254.curve.toAffine.Nonsingular x y })) :=
      Nat.card_congr pointEquiv
    _ = 1 + ∑ x : Field,
          Nat.card { y : Field //
            GarblingPrize.Protected.BN254.curve.toAffine.Nonsingular x y } := by
      rw [Nat.card_sum, Nat.card_sigma]
      simp
    _ ≤ 1 + ∑ _x : Field, 2 := by
      apply Nat.add_le_add_left
      exact Finset.sum_le_sum fun x _ => ordinateFiber_card_le_two x
    _ = 2 * baseFieldModulus + 1 := by
      simp [Nat.mul_comm, Nat.add_comm]

/-- The concrete affine group has no element of additive order two. -/
private theorem no_addOrderOf_two (point : Point) :
    addOrderOf point ≠ 2 := by
  intro horder
  have hdouble : 2 • point = 0 := by
    rw [← horder]
    exact addOrderOf_nsmul_eq_zero point
  have hselfNeg : point = -point := by
    apply eq_neg_iff_add_eq_zero.mpr
    simpa [two_nsmul] using hdouble
  cases hpoint : point with
  | zero =>
      subst point
      change addOrderOf (0 : Point) = 2 at horder
      rw [addOrderOf_zero] at horder
      omega
  | @some x y hnonsingular =>
      have hsome :
          (WeierstrassCurve.Affine.Point.some x y hnonsingular : Point) =
            -(WeierstrassCurve.Affine.Point.some x y hnonsingular : Point) := by
        simpa [hpoint] using hselfNeg
      rw [WeierstrassCurve.Affine.Point.neg_some,
        WeierstrassCurve.Affine.Point.some.injEq] at hsome
      have hyNeg : y = -y := by
        simpa [GarblingPrize.Protected.BN254.curve,
          WeierstrassCurve.Affine.negY] using hsome.2
      have hyZero : y = 0 := by
        have htwoY : (2 : Field) * y = 0 := by
          calc
            (2 : Field) * y = y + y := by ring
            _ = 0 :=
              (congrArg (fun value : Field => value + y) hyNeg).trans
                (neg_add_cancel y)
        have htwo : (2 : Field) ≠ 0 := by decide
        exact (mul_eq_zero.mp htwoY).resolve_left htwo
      have hequation :
          GarblingPrize.Protected.BN254.curve.toAffine.Equation x y :=
        (GarblingPrize.Protected.BN254.curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero
            GarblingPrize.Protected.BN254.discriminant_ne_zero).mpr hnonsingular
      rw [WeierstrassCurve.Affine.equation_iff] at hequation
      have hsum : x ^ 3 + (3 : Field) = 0 := by
        simpa [GarblingPrize.Protected.BN254.curve, hyZero] using
          hequation.symm
      exact HomogeneousRCBG1GroupLaw.neg_three_not_cube x
        (eq_neg_of_add_eq_zero_left hsum)

private theorem pointCardinality_odd : Odd (Nat.card Point) := by
  by_contra hodd
  have heven : Even (Nat.card Point) := Nat.not_odd_iff_even.mp hodd
  have hdvd : 2 ∣ Nat.card Point := even_iff_two_dvd.mp heven
  letI : Fact (Nat.Prime 2) := ⟨by decide⟩
  obtain ⟨point, hpoint⟩ := exists_prime_addOrderOf_dvd_card' 2 hdvd
  exact no_addOrderOf_two point hpoint

private theorem scalarFieldModulus_prime : scalarFieldModulus.Prime := by
  simpa [scalarFieldModulus, _root_.BN254.scalarFieldSize] using
    _root_.BN254.ScalarField_is_prime

local instance scalarPrimeFact : Fact scalarFieldModulus.Prime :=
  ⟨scalarFieldModulus_prime⟩

/-- The checked standard generator has exact order `r`. -/
theorem generator_addOrderOf :
    addOrderOf G1GeneratorCertificateBase.generatorPoint =
      scalarFieldModulus :=
  addOrderOf_eq_prime
    G1OrderCertificates.generator_nsmul_scalarFieldModulus
    G1GeneratorCertificateBase.generatorPoint_ne_zero

private theorem scalarFieldModulus_dvd_pointCardinality :
    scalarFieldModulus ∣ Nat.card Point := by
  rw [← generator_addOrderOf]
  exact addOrderOf_dvd_natCard _

/-- Kernel-checked cofactor-one theorem for the exact protected G1 type. -/
theorem pointCardinality : Nat.card Point = scalarFieldModulus := by
  have hbound : Nat.card Point < 3 * scalarFieldModulus :=
    lt_of_le_of_lt pointCardinality_le_two_mul_base_add_one (by
      norm_num [baseFieldModulus, scalarFieldModulus])
  obtain ⟨multiplier, hcard⟩ := scalarFieldModulus_dvd_pointCardinality
  have hpositive : 0 < Nat.card Point := Nat.card_pos
  have hmultiplierPositive : 0 < multiplier := by
    by_contra hnotPositive
    have hzero : multiplier = 0 := Nat.eq_zero_of_not_pos hnotPositive
    rw [hzero, Nat.mul_zero] at hcard
    omega
  have hmultiplierLt : multiplier < 3 := by
    have hscaled : scalarFieldModulus * multiplier <
        scalarFieldModulus * 3 := by
      rw [← hcard]
      simpa [Nat.mul_comm] using hbound
    exact Nat.lt_of_mul_lt_mul_left hscaled
  have hmultiplier : multiplier = 1 ∨ multiplier = 2 := by omega
  rcases hmultiplier with hone | htwo
  · simpa [hone] using hcard
  · have hdvdTwo : 2 ∣ Nat.card Point := by
      rw [hcard, htwo]
      simp
    exact (pointCardinality_odd.not_two_dvd_nat hdvdTwo).elim

end

end GarblingPrize.Submission.G1Cardinality
