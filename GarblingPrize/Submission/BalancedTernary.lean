import GarblingPrize.Protected.Target
import GarblingPrize.Submission.BalancedTernaryRuntime

namespace GarblingPrize.Submission.BalancedTernary

/-!
# Fixed-width balanced ternary proofs

The proof-free digit carrier, fixed-width decomposition, and evaluation
functions live in `BalancedTernaryRuntime`.  This historical module retains
the exact range, decode, and frozen-profile correctness theorems under their
existing public names.
-/

open GarblingPrize.Protected

namespace Digit

theorem value_fromNatDigit_of_lt_three (digit : Nat) (hdigit : digit < 3) :
    value (fromNatDigit digit) = (digit : Int) - 1 := by
  interval_cases digit <;> rfl

end Digit

/-- The balanced range has the expected closed form, stated without natural
division so later bounds are linear arithmetic. -/
theorem two_mul_maxValue_add_one (width : Nat) :
    2 * maxValue width + 1 = 3 ^ width := by
  induction width with
  | zero => rfl
  | succ width ih =>
      simp only [maxValue, pow_succ]
      omega

namespace Digits

/-- The operational recurrence in `encodeNat` is the shifted ordinary ternary
codec: its low digit is `(input + 1) % 3` and its tail receives
`(input + 1) / 3`. -/
private theorem decode_encodeNat (width input : Nat)
    (hinput : input ≤ maxValue width) :
    (encodeNat width input).decode = (input : Int) := by
  induction width generalizing input with
  | zero =>
      have hzero : input = 0 := by
        simpa [maxValue] using hinput
      subst input
      rfl
  | succ width ih =>
      have htail : (input + 1) / 3 ≤ maxValue width := by
        change input ≤ 1 + 3 * maxValue width at hinput
        omega
      change
        Digit.value (Digit.fromNatDigit ((input + 1) % 3)) +
            3 * (encodeNat width ((input + 1) / 3)).decode =
          (input : Int)
      have hdigit : (input + 1) % 3 < 3 :=
        Nat.mod_lt _ (by omega)
      rw [Digit.value_fromNatDigit_of_lt_three _ hdigit,
        ih ((input + 1) / 3) htail]
      have hdecompose := Nat.mod_add_div (input + 1) 3
      omega

/-- Fixed-width balanced encoding decodes to the exact input natural. -/
theorem decode_encode (input : Bounded width) :
    decode (encode input) = (input.val : Int) := by
  have hinput : input.val ≤ maxValue width := by
    omega
  simpa [encode] using decode_encodeNat width input.val hinput

end Digits

/-! ## Frozen executable-profile bounds -/

/-- Every canonical BN254 scalar fits in 161 balanced ternary digits. -/
theorem scalarFieldModulus_fits :
    scalarFieldModulus ≤ maxValue 161 := by
  have hmax := two_mul_maxValue_add_one 161
  have hscalar :
      2 * scalarFieldModulus + 1 ≤ 3 ^ 161 := by
    norm_num [scalarFieldModulus]
  omega

/-- Every unsigned 32-bit pairing chunk fits in 21 balanced ternary digits. -/
theorem uint32_fits :
    2 ^ 32 ≤ maxValue 21 := by
  have hmax := two_mul_maxValue_add_one 21
  have hvalue : 2 * (2 ^ 32) + 1 ≤ 3 ^ 21 := by
    norm_num
  omega

/-- The 161-trit scalar encoding is exact as an integer. -/
theorem decode_encodeScalar (scalar : Fin scalarFieldModulus) :
    (encodeScalar scalar).decode = (scalar.val : Int) := by
  have hscalar : scalar.val ≤ maxValue 161 :=
    Nat.le_trans (Nat.le_of_lt scalar.isLt) scalarFieldModulus_fits
  let input : Bounded 161 := ⟨scalar.val, by omega⟩
  simpa [encodeScalar, Digits.encode, input] using Digits.decode_encode input

/-- The 21-trit chunk encoding is exact as an integer. -/
theorem decode_encodeUInt32 (value : Fin (2 ^ 32)) :
    (encodeUInt32 value).decode = (value.val : Int) := by
  have hvalue : value.val ≤ maxValue 21 :=
    Nat.le_trans (Nat.le_of_lt value.isLt) uint32_fits
  let input : Bounded 21 := ⟨value.val, by omega⟩
  simpa [encodeUInt32, Digits.encode, input] using Digits.decode_encode input

end GarblingPrize.Submission.BalancedTernary
