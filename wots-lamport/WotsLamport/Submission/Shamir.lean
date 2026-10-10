import WotsLamport.Submission.Threshold
import Mathlib.LinearAlgebra.Lagrange

/-! Abstract field obligations. These do not yet connect the byte-array
implementation to field polynomials, or prove the joint ROM distribution. -/
namespace WotsLamport.Submission.Shamir
open Polynomial

variable {F : Type*} [Field F] [DecidableEq F]

/-- Any sufficiently large set of distinct shares reconstructs the constant
coefficient. This theorem is independent of the selected field and limb count. -/
theorem reconstruct_secret (s : Finset F) (p : F[X])
    (degree_lt : p.degree < s.card) :
    (Lagrange.interpolate s id (fun x => p.eval x)).eval 0 = p.eval 0 := by
  rw [← Lagrange.eq_interpolate (fun _ _ _ _ h => h) degree_lt]

/-- A polynomial which is one at the secret coordinate and zero at all
observed nonzero coordinates. Its degree is at most the observation count. -/
noncomputable def privacyMask (s : Finset F) : F[X] :=
  Lagrange.interpolate (insert 0 s) id (fun x => if x = 0 then 1 else 0)

theorem privacyMask_zero (s : Finset F) : (privacyMask s).eval 0 = 1 := by
  simpa [privacyMask] using
    (Lagrange.eval_interpolate_at_node (s := insert 0 s) (v := id)
      (fun x => if x = 0 then (1 : F) else 0)
      (fun _ _ _ _ h => h) (Finset.mem_insert_self 0 s))

theorem privacyMask_observed (s : Finset F) (nonzero : (0 : F) ∉ s)
    (x : F) (hx : x ∈ s) : (privacyMask s).eval x = 0 := by
  have hne : x ≠ 0 := by intro h; subst x; exact nonzero hx
  simpa [privacyMask, hne] using
    (Lagrange.eval_interpolate_at_node (s := insert 0 s) (v := id)
      (fun x => if x = 0 then (1 : F) else 0)
      (fun _ _ _ _ h => h) (Finset.mem_insert_of_mem hx))

theorem privacyMask_degree (s : Finset F) (nonzero : (0 : F) ∉ s) :
    (privacyMask s).degree ≤ s.card := by
  simpa [privacyMask, Finset.card_insert_of_notMem nonzero] using
    (Lagrange.degree_interpolate_le (s := insert 0 s) (v := id)
      (fun x => if x = 0 then (1 : F) else 0) (fun _ _ _ _ h => h))

noncomputable def shift (s : Finset F) (delta : F) (p : F[X]) : F[X] :=
  p + C delta * privacyMask s

theorem shift_secret (s : Finset F) (delta : F) (p : F[X]) :
    (shift s delta p).eval 0 = p.eval 0 + delta := by
  simp [shift, privacyMask_zero]

theorem shift_observed (s : Finset F) (nonzero : (0 : F) ∉ s)
    (delta : F) (p : F[X]) (x : F) (hx : x ∈ s) :
    (shift s delta p).eval x = p.eval x := by
  simp [shift, privacyMask_observed s nonzero x hx]

/-- Translation is invertible; this is the algebraic ingredient of a uniform
Shamir privacy proof, not a claim that biased bytes have a uniform field law. -/
theorem shift_inverse (s : Finset F) (delta : F) (p : F[X]) :
    shift s (-delta) (shift s delta p) = p := by
  simp [shift]

theorem shift_degree (s : Finset F) (nonzero : (0 : F) ∉ s)
    (t : Nat) (few : s.card < t) (delta : F) (p : F[X])
    (hp : p.degree < t) : (shift s delta p).degree < t := by
  have hm : (C delta * privacyMask s).degree ≤ (s.card : WithBot Nat) := by
    simpa using (Polynomial.degree_mul_le_of_le
      (p := C delta) (q := privacyMask s) Polynomial.degree_C_le
      (privacyMask_degree s nonzero))
  have hc : (s.card : WithBot Nat) < (t : WithBot Nat) := WithBot.coe_lt_coe.mpr few
  exact (Polynomial.degree_add_le _ _).trans_lt (max_lt hp (hm.trans_lt hc))

def Fiber (s : Finset F) (t : Nat) (secret : F) (values : F → F) :=
  {p : F[X] // p.degree < t ∧ p.eval 0 = secret ∧ ∀ x ∈ s, p.eval x = values x}

/-- For fewer than t nonzero observed coordinates, the compatible polynomial
sets for any two secrets are in bijection. Uniform-law transport and the actual
biased coefficient sampler remain separate obligations. -/
noncomputable def fiberEquiv (s : Finset F) (nonzero : (0 : F) ∉ s)
    (t : Nat) (few : s.card < t) (a b : F) (values : F → F) :
    Fiber s t a values ≃ Fiber s t b values where
  toFun p := ⟨shift s (b-a) p.val,
    shift_degree s nonzero t few (b-a) p.val p.property.1,
    by rw [shift_secret, p.property.2.1]; ring,
    by intro x hx; rw [shift_observed s nonzero (b-a) p.val x hx]; exact p.property.2.2 x hx⟩
  invFun p := ⟨shift s (a-b) p.val,
    shift_degree s nonzero t few (a-b) p.val p.property.1,
    by rw [shift_secret, p.property.2.1]; ring,
    by intro x hx; rw [shift_observed s nonzero (a-b) p.val x hx]; exact p.property.2.2 x hx⟩
  left_inv p := by
    apply Subtype.ext
    change shift s (a-b) (shift s (b-a) p.val) = p.val
    simp only [shift, map_sub]
    ring
  right_inv p := by
    apply Subtype.ext
    change shift s (b-a) (shift s (a-b) p.val) = p.val
    simp only [shift, map_sub]
    ring

end WotsLamport.Submission.Shamir
