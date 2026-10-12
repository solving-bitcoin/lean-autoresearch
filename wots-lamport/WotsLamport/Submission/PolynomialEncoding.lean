import WotsLamport.Submission.PolynomialLaw
import WotsLamport.Submission.LabelBridge

namespace WotsLamport.Submission
open Polynomial SecretRelease

theorem fieldPolynomial_coefficient (coefficients : List Nat) (n : Nat) :
    (fieldPolynomial coefficients).coeff n = ((coefficients[n]! : Nat) : ZMod 65537) := by
  induction coefficients generalizing n with
  | nil => simp [fieldPolynomial]
  | cons a rest ih =>
    cases n <;> simp [fieldPolynomial, Polynomial.coeff_X_mul, ih]

theorem fieldPolynomial_as_coefficients (coefficients : List Nat) (k : Nat)
    (length : coefficients.length = k+1) :
    fieldPolynomial coefficients = Shamir.coefficientPolynomial
      ((coefficients[0]! : Nat) : ZMod 65537)
      (fun j : Fin k => ((coefficients[j.val+1]! : Nat) : ZMod 65537)) := by
  apply Polynomial.ext
  intro n
  cases n with
  | zero => rw [fieldPolynomial_coefficient, Shamir.coefficientPolynomial_zero]
  | succ n =>
    by_cases hn : n < k
    · rw [fieldPolynomial_coefficient]
      exact (Shamir.coefficientPolynomial_coefficient
        ((coefficients[0]! : Nat) : ZMod 65537)
        (fun j : Fin k => ((coefficients[j.val+1]! : Nat) : ZMod 65537)) ⟨n, hn⟩).symm
    · have hge : k+1 ≤ n+1 := by omega
      have hd : (fieldPolynomial coefficients).degree < (k+1 : Nat) := by
        simpa only [length] using fieldPolynomial_degree coefficients
      rw [(Polynomial.degree_lt_iff_coeff_zero _ _).mp hd (n+1) hge,
        (Polynomial.degree_lt_iff_coeff_zero _ _).mp
          (Shamir.coefficientPolynomial_degree
            ((coefficients[0]! : Nat) : ZMod 65537)
            (fun j : Fin k => ((coefficients[j.val+1]! : Nat) : ZMod 65537))) (n+1) hge]

/-- The polynomial evaluated by the executable Horner loop is exactly the
fixed-secret polynomial used in the uniform coefficient-law theorem. -/
theorem actual_polynomial_as_coefficients (coins : ByteArray) (label : Label)
    (wire limb : Nat) (value : Bool) :
    fieldPolynomial (polynomial coins label wire limb value) =
      Shamir.coefficientPolynomial
        (readLE (ByteArray.mk label.toArray) (2*limb) 2 : ZMod 65537)
        (fun j : Fin (threshold value-1) =>
          (((polynomial coins label wire limb value)[j.val+1]! : Nat) : ZMod 65537)) := by
  have ht : threshold value = (threshold value-1)+1 := by cases value <;> decide
  have hl : (polynomial coins label wire limb value).length = (threshold value-1)+1 :=
    (polynomial_length coins label wire limb value).trans ht
  have hc : (((polynomial coins label wire limb value)[0]! : Nat) : ZMod 65537) =
      (readLE (ByteArray.mk label.toArray) (2*limb) 2 : ZMod 65537) := by
    calc
      _ = (fieldPolynomial (polynomial coins label wire limb value)).coeff 0 :=
        (fieldPolynomial_coefficient _ 0).symm
      _ = (fieldPolynomial (polynomial coins label wire limb value)).eval 0 :=
        Polynomial.coeff_zero_eq_eval_zero _
      _ = (evaluatePolynomial (polynomial coins label wire limb value) 0 : ZMod 65537) :=
        evaluatePolynomial_field _ 0
      _ = _ := by rw [polynomial_eval_zero]
  rw [fieldPolynomial_as_coefficients _ _ hl, hc]

end WotsLamport.Submission
