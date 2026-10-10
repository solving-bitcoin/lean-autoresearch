import WotsLamport.Submission.FieldBridge
import Mathlib.FieldTheory.Finite.Basic

namespace WotsLamport.Submission

theorem fmul_field (a b : Nat) :
    (fmul a b : ZMod 65537) = (a : ZMod 65537) * (b : ZMod 65537) := by
  simp [fmul, prime]

/-- Subtraction uses natural numbers, so its field interpretation requires
the actual share-coordinate bound; it is not asserted for arbitrary b. -/
theorem fsub_field (a b : Nat) (hb : b ≤ prime) :
    (fsub a b : ZMod 65537) = (a : ZMod 65537) - (b : ZMod 65537) := by
  have h : b ≤ a + 65537 := by unfold prime at hb; omega
  simp [fsub, prime, Nat.cast_sub h]

private def inverseState (a n : Nat) : Nat × Nat :=
  (List.range n).foldl (fun s _ => (fmul s.1 s.2, fmul s.2 s.2)) (1, a)

private theorem inverseState_succ (a n : Nat) :
    inverseState a (n+1) =
      (fmul (inverseState a n).1 (inverseState a n).2,
       fmul (inverseState a n).2 (inverseState a n).2) := by
  simp [inverseState, List.range_succ, List.foldl_append]

/-- The repeated-squaring loop maintains the two field identities without
enumerating field elements or trusting native evaluation. -/
private theorem inverseState_field (a n : Nat) :
    ((inverseState a n).1 : ZMod 65537) * (a : ZMod 65537) = (a : ZMod 65537)^(2^n) ∧
    ((inverseState a n).2 : ZMod 65537) = (a : ZMod 65537)^(2^n) := by
  induction n with
  | zero => simp [inverseState]
  | succ n ih =>
    have hp : (a : ZMod 65537)^(2^n) * (a : ZMod 65537)^(2^n) =
        (a : ZMod 65537)^(2^(n+1)) := by
      rw [← pow_add]
      congr 1
      simp [Nat.pow_succ, Nat.mul_two]
    simp only [inverseState_succ, fmul_field]
    constructor
    · calc
        ((inverseState a n).1 : ZMod 65537) * ((inverseState a n).2 : ZMod 65537) * (a : ZMod 65537) =
            (((inverseState a n).1 : ZMod 65537) * (a : ZMod 65537)) *
              ((inverseState a n).2 : ZMod 65537) := by ring
        _ = (a : ZMod 65537)^(2^n) * (a : ZMod 65537)^(2^n) := by rw [ih.1, ih.2]
        _ = _ := hp
    · rw [ih.2]
      exact hp

/-- The actual 16-step executable inverse is a field inverse whenever its
argument represents a nonzero element. Distinct share coordinates provide
this premise for interpolation denominators. -/
theorem inverse_mul_field (a : Nat) (ha : (a : ZMod 65537) ≠ 0) :
    (inverse a : ZMod 65537) * (a : ZMod 65537) = 1 := by
  change ((inverseState a 16).1 : ZMod 65537) * (a : ZMod 65537) = 1
  rw [(inverseState_field a 16).1]
  exact ZMod.pow_card_sub_one_eq_one ha

end WotsLamport.Submission
