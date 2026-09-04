import GarblingPrize.Protected.Target

namespace GarblingPrize.Submission.BalancedTernary

/-!
# Proof-free fixed-width balanced ternary

This leaf owns the signed ternary carrier and the little-endian fixed-width
decomposition evaluated by the executable pairing artifact.  The historical
`BalancedTernary` module retains the range, decode, and profile-bound proofs.

For an input `n`, the recursive encoder emits the ordinary radix-three digits
of `n + maxValue width`, shifted down by one.  Writing
`maxValue (width + 1) = 1 + 3 * maxValue width` makes that computation local:
the low digit is `(n + 1) % 3` and the remaining balanced word encodes
`(n + 1) / 3`.
-/

open GarblingPrize.Protected

/-- One signed radix-three digit. -/
inductive Digit where
  | negative
  | zero
  | positive
  deriving DecidableEq, Repr

namespace Digit

/-- Integer interpretation of a signed digit. -/
def value : Digit → Int
  | .negative => -1
  | .zero => 0
  | .positive => 1

/-- Shift an ordinary ternary digit in `{0,1,2}` down by one.  The total
fallback keeps this operational function defined on every natural number. -/
def fromNatDigit : Nat → Digit
  | 0 => .negative
  | 1 => .zero
  | 2 => .positive
  | _ => .zero

end Digit

/-- Maximum nonnegative integer represented by `width` balanced digits. -/
def maxValue : Nat → Nat
  | 0 => 0
  | width + 1 => 1 + 3 * maxValue width

/-- Values accepted by the total width-indexed encoder. -/
abbrev Bounded (width : Nat) := Fin (maxValue width + 1)

/-- A literal fixed-width digit list. -/
structure Digits (width : Nat) where
  values : List Digit
  length_eq : values.length = width
  deriving DecidableEq, Repr

namespace Digits

/-- Little-endian signed radix-three evaluation of an arbitrary list. -/
def decodeList : List Digit → Int
  | [] => 0
  | digit :: tail => digit.value + 3 * decodeList tail

/-- Integer decoded by a fixed-width balanced word. -/
def decode (digits : Digits width) : Int :=
  decodeList digits.values

/-- Pointwise access at a statically valid digit index. -/
def get (digits : Digits width) (index : Fin width) : Digit :=
  digits.values.get ⟨index.val, by
    rw [digits.length_eq]
    exact index.isLt⟩

/-- Total fixed-width balanced decomposition of a natural number.  Callers
with a `Bounded width` input obtain the exact nontruncating profile codec;
the total form also keeps the executable recurrence defined outside that
proof-only range. -/
def encodeNat : (width : Nat) → Nat → Digits width
  | 0, _ =>
      { values := []
        length_eq := rfl }
  | Nat.succ width, input =>
      let tail := encodeNat width ((input + 1) / 3)
      { values := Digit.fromNatDigit ((input + 1) % 3) :: tail.values
        length_eq := congrArg Nat.succ tail.length_eq }

/-- Fixed-width balanced encoding of a range-bounded natural. -/
def encode (input : Bounded width) : Digits width :=
  encodeNat width input.val

end Digits

/-! ## Frozen executable-profile encoders -/

/-- Canonical 161-trit decomposition of a BN254 scalar representative. -/
def encodeScalar (scalar : Fin scalarFieldModulus) : Digits 161 :=
  Digits.encodeNat 161 scalar.val

/-- Canonical 21-trit decomposition of an unsigned 32-bit pairing chunk. -/
def encodeUInt32 (value : Fin (2 ^ 32)) : Digits 21 :=
  Digits.encodeNat 21 value.val

end GarblingPrize.Submission.BalancedTernary
