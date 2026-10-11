import WotsLamport.Submission.WithholdingBudget
import WotsLamport.Submission.SamplerMixture

namespace WotsLamport.Submission
open WotsLamport.Protected

/-- Arithmetic for three tape-collision losses, one complete coefficient
sampler loss, both adaptive query phases and chosen-wire guessing. -/
theorem adaptive_bound_fits_target (q₁ q₂ : Nat) :
    (((((1056 : ENNReal)^2/2^256 + ((512 : ENNReal)/2^256 + (1501 : ENNReal)*q₂/2^256)) +
      (3002 : ENNReal)*q₁/2^256) + (coefficientCount : ENNReal)*Sampler.exceptionWeight) +
      (1056 : ENNReal)^2/2^256) + (1056 : ENNReal)^2/2^256 ≤
        (romTarget.error (q₁+q₂) : ENNReal) := by
  have naturalBound : ((((1056^2 + (512 + 1501*q₂)) + 3002*q₁) + coefficientCount) + 1056^2) + 1056^2 ≤
      2^20*(q₁+q₂+2^32+1)^2 := by
    unfold coefficientCount
    nlinarith [Nat.zero_le ((q₁+q₂)^2)]
  have rationalNumerator :
      (((((1056 : ℚ≥0)^2 + (512 + 1501*q₂)) + 3002*q₁) + coefficientCount) + 1056^2) + 1056^2 ≤
        2^20*((q₁ : ℚ≥0)+q₂+2^32+1)^2 := by exact_mod_cast naturalBound
  have rationalBound :
      (((((1056 : ℚ≥0)^2/2^256 + ((512 : ℚ≥0)/2^256 + (1501 : ℚ≥0)*q₂/2^256)) +
        (3002 : ℚ≥0)*q₁/2^256) + (coefficientCount : ℚ≥0)/2^256) +
        (1056 : ℚ≥0)^2/2^256) + (1056 : ℚ≥0)^2/2^256 ≤ romTarget.error (q₁+q₂) := by
    simpa only [romTarget, Nat.cast_add, ← add_div] using
      div_le_div_of_nonneg_right rationalNumerator (by positivity : (0 : ℚ≥0) ≤ 2^256)
  have realBound :
      (((((1056 : NNReal)^2/2^256 + ((512 : NNReal)/2^256 + (1501 : NNReal)*q₂/2^256)) +
        (3002 : NNReal)*q₁/2^256) + (coefficientCount : NNReal)/2^256) +
        (1056 : NNReal)^2/2^256) + (1056 : NNReal)^2/2^256 ≤
          (romTarget.error (q₁+q₂) : NNReal) := by
    simpa only [NNRat.cast_add, NNRat.cast_div, NNRat.cast_mul, NNRat.cast_pow,
      NNRat.cast_natCast, NNRat.cast_ofNat] using
      (NNRat.cast_mono (K := NNReal) rationalBound)
  have castBound := ENNReal.coe_le_coe.mpr realBound
  simpa only [Sampler.exceptionWeight, Sampler.sampleSize, Nat.cast_pow, Nat.cast_ofNat,
    mul_div_assoc, mul_one, ENNReal.coe_add,
    ENNReal.coe_div (by positivity : (2 : NNReal)^256 ≠ 0), ENNReal.coe_pow,
    ENNReal.coe_mul, ENNReal.coe_natCast, ENNReal.coe_ofNat, ENNReal.coe_nnratCast] using castBound

end WotsLamport.Submission
