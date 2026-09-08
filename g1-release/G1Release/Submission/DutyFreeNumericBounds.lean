import G1Release.Submission.CosetNumericBounds

/-! Two first-query hops, two finite-coin sampling errors, and the plain-pad
tail all fit the unchanged protected 128-bit failure profile. -/
namespace G1Release.Submission.DutyFreeNumericBounds
open SecretRelease G1Release.Protected CosetSampler
set_option exponentiation.threshold 1024

private theorem profile_eq (q : Nat) :
    (challenge.rom.error q : ENNReal) = (q+1 : ENNReal) / 2^128 := by
  simp only [BoundaryFacts.profile_error, ← ENNReal.coe_nnratCast]
  push_cast
  rfl

private theorem error_small : ENNReal.ofReal samplingError ≤ (1 : ENNReal) / 2^130 := by
  have he : samplingError ≤ (1 : ℝ) / 2^130 := by
    apply samplingError_le.trans
    norm_num
  have h := ENNReal.ofReal_le_ofReal he
  rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_one,
    ENNReal.ofReal_pow (by norm_num), show ENNReal.ofReal 2 = 2 from by norm_num] at h
  exact h

theorem function_le (q : Nat) :
    2 * ((q : ENNReal) / (2^256-1 : Nat)) + 2 * ENNReal.ofReal samplingError + 1 / 2^240 ≤
      (challenge.rom.error q : ENNReal) := by
  let unit : ENNReal := 1 / 2^130
  have hd : (1 : ENNReal) / (2^256-1 : Nat) ≤ unit := by norm_num [unit]
  have ht : (1 : ENNReal) / 2^240 ≤ unit := by norm_num [unit]
  have hq : (q : ENNReal) / (2^256-1 : Nat) ≤ (q : ENNReal) * unit := by
    simpa only [div_eq_mul_inv, one_mul] using mul_le_mul_right hd (q : ENNReal)
  have hc : 3 * unit ≤ (1 : ENNReal) / 2^128 := by
    apply (ENNReal.toReal_le_toReal (by dsimp only [unit]; finiteness) (by finiteness)).mp
    norm_num [unit, ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_pow]
  calc
    _ ≤ 2 * ((q : ENNReal) * unit) + 2 * unit + unit :=
      add_le_add (add_le_add (mul_le_mul_right hq 2) (mul_le_mul_right error_small 2)) ht
    _ ≤ 3 * ((q : ENNReal) * unit) + 2 * unit + unit := by
      exact add_le_add (add_le_add (mul_le_mul_left (by norm_num : (2 : ENNReal) ≤ 3) _) le_rfl) le_rfl
    _ = (q+1 : ENNReal) * (3 * unit) := by ring
    _ ≤ (q+1 : ENNReal) * (1 / 2^128) := mul_le_mul_right hc _
    _ = (challenge.rom.error q : ENNReal) := by
      rw [profile_eq]
      simp only [div_eq_mul_inv, one_mul]

end G1Release.Submission.DutyFreeNumericBounds
