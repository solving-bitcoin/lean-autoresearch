import WotsLamport.Protected.Target
import Mathlib.Tactic.Conv
import Mathlib.Tactic.Convert
import Mathlib.Tactic.Ext
import Mathlib.Tactic.Lift
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Ring

namespace WotsLamport.Submission

theorem fieldSize_prime : Nat.Prime 65537 := by norm_num

/-- Positive weights and equal weighted sums prohibit strict forward movement
to another valid codeword. This applies to both fixed-sum and mixed-radix codes. -/
theorem weighted_antichain {n : Nat} (w a b : Fin n → Nat)
    (hw : ∀ i, 0 < w i) (hle : ∀ i, a i ≤ b i)
    (hs : (∑ i, w i * a i) = ∑ i, w i * b i) : a = b := by
  funext i
  by_contra hi
  have hlt : a i < b i := by have := hle i; omega
  have hsum : (∑ j, w j * a j) < ∑ j, w j * b j :=
    Finset.sum_lt_sum (fun j _ => Nat.mul_le_mul_left (w j) (hle j))
      ⟨i, Finset.mem_univ i, Nat.mul_lt_mul_of_pos_left hlt (hw i)⟩
  omega

/-- Integer arithmetic makes the falling-edge term explicit; Nat subtraction
would silently truncate it. Multiplicity is nonnegative when w ≥ 1. -/
def multiplicity (w : ℤ) (f : Nat → Bool) (k : Nat) : ℤ :=
  w + (if f k then 1 else 0) - (if f (k+1) then 1 else 0)

theorem multiplicity_bounds (w : ℤ) (hw : 1 ≤ w) (f : Nat → Bool) (k : Nat) :
    0 ≤ multiplicity w f k ∧ multiplicity w f k ≤ w+1 := by
  simp only [multiplicity]
  split_ifs <;> omega

theorem telescoping (w : ℤ) (f : Nat → Bool) (c n : Nat) :
    (∑ k ∈ Finset.range n, multiplicity w f (c+k)) =
      n*w + (if f c then 1 else 0) - (if f (c+n) then 1 else 0) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    simp only [multiplicity, Nat.cast_add, Nat.cast_one]
    have h : c + (n + 1) = c + n + 1 := by omega
    rw [h]
    ring

/-- The share-count identity, for arbitrary positive coordinate weights.
The fixed-sum microchallenge is w=1; the 67-chain track uses 1,8,64. -/
theorem threshold_rearrangement (T : ℤ) (fD fc : Bool) :
    T - (if fD then 1 else 0) + (if fc then 1 else 0) =
      (T + 1 - (if fD then 1 else 0)) - 1 + (if fc then 1 else 0) := by ring

end WotsLamport.Submission
