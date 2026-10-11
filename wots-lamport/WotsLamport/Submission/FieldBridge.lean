import WotsLamport.Submission.Sharing
import WotsLamport.Submission.Shamir
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod

namespace WotsLamport.Submission
open Polynomial

instance fieldPrime : Fact (Nat.Prime 65537) := ⟨fieldSize_prime⟩

def coordinate (i : Fin 1984) : ZMod 65537 := (i.val + 1 : Nat)

theorem coordinate_nonzero (i : Fin 1984) : coordinate i ≠ 0 := by
  intro h
  have hi : i.val + 1 < 65537 := by omega
  have hm := (ZMod.natCast_eq_natCast_iff' (i.val+1) 0 65537).mp h
  rw [Nat.mod_eq_of_lt hi, Nat.zero_mod] at hm
  omega

theorem coordinate_injective : Function.Injective coordinate := by
  intro i j h
  have hi : i.val + 1 < 65537 := by omega
  have hj : j.val + 1 < 65537 := by omega
  have hm := (ZMod.natCast_eq_natCast_iff' (i.val+1) (j.val+1) 65537).mp h
  rw [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at hm
  apply Fin.ext
  omega

/-- The mathematical polynomial represented by the executable coefficient list. -/
noncomputable def fieldPolynomial : List Nat → Polynomial (ZMod 65537)
  | [] => 0
  | a :: rest => C (a : ZMod 65537) + X * fieldPolynomial rest

theorem fieldPolynomial_degree (coefficients : List Nat) :
    (fieldPolynomial coefficients).degree < coefficients.length := by
  induction coefficients with
  | nil => simp [fieldPolynomial]
  | cons a rest ih =>
    apply (Polynomial.degree_lt_iff_coeff_zero _ _).mpr
    intro n hn
    cases n with
    | zero => simp at hn
    | succ n =>
      have hz := (Polynomial.degree_lt_iff_coeff_zero _ _).mp ih n
        (by simp only [List.length_cons] at hn; omega)
      simpa [fieldPolynomial, Polynomial.coeff_X_mul] using hz

theorem polynomial_degree (coins : ByteArray) (label : SecretRelease.Label)
    (wire limb : Nat) (value : Bool) :
    (fieldPolynomial (polynomial coins label wire limb value)).degree < threshold value := by
  simpa only [polynomial, List.length_map, List.length_range] using
    fieldPolynomial_degree (polynomial coins label wire limb value)

theorem fieldPolynomial_secret (coefficients : List Nat) :
    (fieldPolynomial coefficients).eval 0 = (coefficients.headD 0 : ZMod 65537) := by
  cases coefficients <;> simp [fieldPolynomial]

/-- The actual modular Horner loop computes the field polynomial evaluation,
for arbitrary coefficients and points; no random-oracle assumption is used. -/
theorem evaluatePolynomial_field (coefficients : List Nat) (x : Nat) :
    (fieldPolynomial coefficients).eval (x : ZMod 65537) =
      (evaluatePolynomial coefficients x : ZMod 65537) := by
  induction coefficients with
  | nil => simp [fieldPolynomial, evaluatePolynomial]
  | cons a rest ih =>
    change (C (a : ZMod 65537) + X * fieldPolynomial rest).eval (x : ZMod 65537) =
      (fadd a (fmul x (evaluatePolynomial rest x)) : ZMod 65537)
    simp [fadd, fmul, prime, ih]

theorem evaluatePolynomial_lt (coefficients : List Nat) (x : Nat) :
    evaluatePolynomial coefficients x < prime := by
  cases coefficients with
  | nil => simp [evaluatePolynomial, prime]
  | cons a rest =>
    change (a + fmul x (evaluatePolynomial rest x)) % prime < prime
    exact Nat.mod_lt _ (by decide)

/-- The executable result is the canonical natural representative, not just
an arbitrary integer congruent to the polynomial evaluation. -/
theorem evaluatePolynomial_eq_val (coefficients : List Nat) (x : Nat) :
    evaluatePolynomial coefficients x =
      ((fieldPolynomial coefficients).eval (x : ZMod 65537)).val := by
  have h := congrArg ZMod.val (evaluatePolynomial_field coefficients x)
  have hb : evaluatePolynomial coefficients x < 65537 := evaluatePolynomial_lt coefficients x
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt hb] at h
  exact h.symm

/-- Abstract reconstruction now applies to values of the concrete Horner loop.
Connecting the executable inverse/serialization/coordinate list remains open. -/
theorem reconstruct_evaluated_secret (s : Finset (ZMod 65537))
    (coefficients : List Nat)
    (small : (fieldPolynomial coefficients).degree < s.card) :
    (Lagrange.interpolate s id
      (fun x => (fieldPolynomial coefficients).eval x)).eval 0 =
      (evaluatePolynomial coefficients 0 : ZMod 65537) := by
  rw [Shamir.reconstruct_secret s _ small]
  exact evaluatePolynomial_field coefficients 0

end WotsLamport.Submission
