import WotsLamport.Submission.ShamirLaw
import Mathlib.Algebra.Polynomial.Eval.Coeff

namespace WotsLamport.Submission.Shamir
open Polynomial MeasureTheory ProbabilityTheory

variable {F : Type} [Field F] [DecidableEq F]

noncomputable def coefficientPolynomial (secret : F) {k : Nat} (coefficients : Fin k → F) : F[X] :=
  C secret + ∑ j : Fin k, C (coefficients j) * X^(j.val+1)

theorem coefficientPolynomial_zero (secret : F) {k : Nat} (coefficients : Fin k → F) :
    (coefficientPolynomial secret coefficients).coeff 0 = secret := by
  simp [coefficientPolynomial, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow]

theorem coefficientPolynomial_eval_zero (secret : F) {k : Nat} (coefficients : Fin k → F) :
    (coefficientPolynomial secret coefficients).eval 0 = secret := by
  simp [coefficientPolynomial, Polynomial.eval_finsetSum]

theorem coefficientPolynomial_coefficient (secret : F) {k : Nat}
    (coefficients : Fin k → F) (j : Fin k) :
    (coefficientPolynomial secret coefficients).coeff (j.val+1) = coefficients j := by
  simp only [coefficientPolynomial, Polynomial.coeff_add,
    Polynomial.coeff_C_of_ne_zero (by omega : j.val+1 ≠ 0), zero_add,
    Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hne
    have hv : j.val+1 ≠ i.val+1 := by
      intro he
      apply hne
      apply Fin.ext
      omega
    exact if_neg hv
  · intro hj
    exact False.elim (hj (Finset.mem_univ j))

theorem coefficientPolynomial_degree (secret : F) {k : Nat} (coefficients : Fin k → F) :
    (coefficientPolynomial secret coefficients).degree < (k+1 : Nat) := by
  apply (Polynomial.degree_lt_iff_coeff_zero _ _).mpr
  intro n hn
  simp only [coefficientPolynomial, Polynomial.coeff_add,
    Polynomial.coeff_C_of_ne_zero (by omega : n ≠ 0), zero_add,
    Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow]
  apply Finset.sum_eq_zero
  intro j _
  have hne : n ≠ j.val+1 := by have hj := j.isLt; omega
  exact if_neg hne

/-- Uniform nonconstant coefficients and uniform bounded-degree polynomials
with a fixed constant term are equivalent finite sample spaces. -/
noncomputable def coefficientEquiv (secret : F) (k : Nat) :
    (Fin k → F) ≃ SecretPolynomials (k+1) secret where
  toFun c := ⟨coefficientPolynomial secret c,
    coefficientPolynomial_degree secret c, coefficientPolynomial_eval_zero secret c⟩
  invFun p := fun j => p.val.coeff (j.val+1)
  left_inv c := by
    funext j
    exact coefficientPolynomial_coefficient secret c j
  right_inv p := by
    apply Subtype.ext
    apply Polynomial.ext
    intro n
    cases n with
    | zero =>
      rw [coefficientPolynomial_zero]
      rw [Polynomial.coeff_zero_eq_eval_zero]
      exact p.property.2.symm
    | succ n =>
      by_cases hn : n < k
      · exact coefficientPolynomial_coefficient secret _ ⟨n, hn⟩
      · have hge : k+1 ≤ n+1 := by omega
        rw [(Polynomial.degree_lt_iff_coeff_zero _ _).mp
          (coefficientPolynomial_degree secret _) (n+1) hge,
          (Polynomial.degree_lt_iff_coeff_zero _ _).mp p.property.1 (n+1) hge]

theorem uniform_coefficients_secret_independent [Finite F] [MeasurableSpace F]
    [DiscreteMeasurableSpace F] (s : Finset F) (nonzero : (0 : F) ∉ s)
    (k : Nat) (few : s.card < k+1) (a b : F) (event : Set (s → F)) :
    uniformOn (Set.univ : Set (Fin k → F))
      {c | observedValues s (coefficientEquiv a k c) ∈ event} =
    uniformOn (Set.univ : Set (Fin k → F))
      {c | observedValues s (coefficientEquiv b k c) ∈ event} := by
  calc
    _ = uniformOn (Set.univ : Set (SecretPolynomials (k+1) a))
        {p | observedValues s p ∈ event} := uniform_event_equiv (coefficientEquiv a k) _
    _ = uniformOn (Set.univ : Set (SecretPolynomials (k+1) b))
        {p | observedValues s p ∈ event} :=
      uniform_shares_secret_independent s nonzero (k+1) few a b event
    _ = _ := (uniform_event_equiv (coefficientEquiv b k) _).symm

/-- All polynomial coefficient vectors move together through a product
bijection. This is a joint law for arbitrary events on the complete family. -/
theorem uniform_joint_coefficients_secret_independent [Finite F] [MeasurableSpace F]
    [DiscreteMeasurableSpace F] {I : Type} [Fintype I]
    (s : I → Finset F) (nonzero : ∀ j, (0 : F) ∉ s j)
    (k : I → Nat) (few : ∀ j, (s j).card < k j+1) (a b : I → F)
    (event : Set ((j : I) → s j → F)) :
    uniformOn (Set.univ : Set ((j : I) → Fin (k j) → F))
      {c | (fun j => observedValues (s j) (coefficientEquiv (a j) (k j) (c j))) ∈ event} =
    uniformOn (Set.univ : Set ((j : I) → Fin (k j) → F))
      {c | (fun j => observedValues (s j) (coefficientEquiv (b j) (k j) (c j))) ∈ event} := by
  let ea := Equiv.piCongrRight fun j => coefficientEquiv (a j) (k j)
  let eb := Equiv.piCongrRight fun j => coefficientEquiv (b j) (k j)
  calc
    _ = uniformOn (Set.univ : Set ((j : I) → SecretPolynomials (k j+1) (a j)))
        {p | (fun j => observedValues (s j) (p j)) ∈ event} := uniform_event_equiv ea _
    _ = uniformOn (Set.univ : Set ((j : I) → SecretPolynomials (k j+1) (b j)))
        {p | (fun j => observedValues (s j) (p j)) ∈ event} :=
      uniform_joint_shares_secret_independent s nonzero (fun j => k j+1) few a b event
    _ = _ := (uniform_event_equiv eb _).symm

end WotsLamport.Submission.Shamir
