import G1Release.Submission.CosetSamplerMeasure

set_option exponentiation.threshold 1024

namespace G1Release.Submission.CosetNumericBounds
open SecretRelease G1Release.Protected CosetSampler

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

private theorem denominator_small : (1 : ENNReal) / (2^256-1 : Nat) ≤ 1 / 2^130 := by
  norm_num

theorem release_le (q : Nat) :
    (q+1 : ENNReal) / (2^256-1 : Nat) ≤ (challenge.rom.error q : ENNReal) := by
  rw [profile_eq]
  apply ENNReal.div_le_div_left
  norm_num

theorem function_le (q : Nat) :
    2 * ((q : ENNReal) / (2^256-1 : Nat)) + 2 * ENNReal.ofReal samplingError ≤
      (challenge.rom.error q : ENNReal) := by
  have hq : (q : ENNReal) / (2^256-1 : Nat) ≤ (q : ENNReal) * (1 / 2^130) := by
    simpa only [div_eq_mul_inv, one_mul] using mul_le_mul_right denominator_small (q : ENNReal)
  have hc : 2 * ((1 : ENNReal) / 2^130) ≤ 1 / 2^128 := by
    apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
    norm_num [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_pow]
  calc
    _ ≤ 2 * ((q : ENNReal) * (1 / 2^130)) + 2 * (1 / 2^130) :=
      add_le_add (mul_le_mul_right hq 2) (mul_le_mul_right error_small 2)
    _ = (q+1 : ENNReal) * (2 * (1 / 2^130)) := by ring
    _ ≤ (q+1 : ENNReal) * (1 / 2^128) := mul_le_mul_right hc _
    _ = (challenge.rom.error q : ENNReal) := by rw [profile_eq]; simp only [div_eq_mul_inv, one_mul]

end G1Release.Submission.CosetNumericBounds
