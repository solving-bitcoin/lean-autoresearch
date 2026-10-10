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

end WotsLamport.Submission.Shamir
