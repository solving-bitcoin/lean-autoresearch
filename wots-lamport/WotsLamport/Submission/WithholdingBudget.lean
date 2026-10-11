import WotsLamport.Protected.Target
import Mathlib.Data.Rat.Cast.Lemmas
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.ENNReal.Inv
import Mathlib.Tactic.Linarith

namespace WotsLamport.Submission
open WotsLamport.Protected

/-- Arithmetic only: the proposed withholding reduction fits the unchanged
challenge target, even without using its upper bound on adversarial queries. -/
theorem withholding_bound_fits_target (q : Nat) :
    (((4 : ENNReal)/2^256 + (3002 : ENNReal)*q/2^256) +
      (1056 : ENNReal)^2/2^256) + (1056 : ENNReal)^2/2^256 ≤
        (romTarget.error q : ENNReal) := by
  have naturalBound : 4 + 3002*q + 1056^2 + 1056^2 ≤
      2^20*(q+2^32+1)^2 := by nlinarith
  have rationalNumerator : (4 : ℚ≥0) + 3002*q + 1056^2 + 1056^2 ≤
      2^20*((q : ℚ≥0)+2^32+1)^2 := by exact_mod_cast naturalBound
  have rationalBound :
      (((4 : ℚ≥0)/2^256 + (3002 : ℚ≥0)*q/2^256) +
        (1056 : ℚ≥0)^2/2^256) + (1056 : ℚ≥0)^2/2^256 ≤ romTarget.error q := by
    simpa only [romTarget, ← add_div] using
      div_le_div_of_nonneg_right rationalNumerator (by positivity : (0 : ℚ≥0) ≤ 2^256)
  have realBound :
      (((4 : NNReal)/2^256 + (3002 : NNReal)*q/2^256) +
        (1056 : NNReal)^2/2^256) + (1056 : NNReal)^2/2^256 ≤
          (romTarget.error q : NNReal) := by
    simpa only [NNRat.cast_add, NNRat.cast_div, NNRat.cast_mul, NNRat.cast_pow,
      NNRat.cast_natCast, NNRat.cast_ofNat] using
      (NNRat.cast_mono (K := NNReal) rationalBound)
  have castBound := ENNReal.coe_le_coe.mpr realBound
  simpa only [ENNReal.coe_add, ENNReal.coe_div (by positivity : (2 : NNReal)^256 ≠ 0),
    ENNReal.coe_pow, ENNReal.coe_mul, ENNReal.coe_natCast, ENNReal.coe_ofNat,
    ENNReal.coe_nnratCast] using castBound

end WotsLamport.Submission
