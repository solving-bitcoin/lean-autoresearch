import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.ZMod.Basic

namespace GarblingPrize.Submission.PowCertificate

/-!
# Bounded modular-power certificates

This is submission-owned proof machinery for the official RCB solution. Large
powers are checked as a left-to-right binary residue fold over natural numbers.
The soundness proof connects that computable fold to exponentiation in `ZMod`.
-/

def bitValue : Bool → Nat
  | false => 0
  | true => 1

def exponentStep (acc : Nat) (bit : Bool) : Nat :=
  2 * acc + bitValue bit

def residueStep (modulus base acc : Nat) (bit : Bool) : Nat :=
  (acc * acc * if bit then base else 1) % modulus

def exponent (bits : List Bool) : Nat :=
  bits.foldl exponentStep 0

def residue (modulus base : Nat) (bits : List Bool) : Nat :=
  bits.foldl (residueStep modulus base) (1 % modulus)

def binaryDigits (n : Nat) : List Bool :=
  (Nat.digits 2 n).reverse.map (fun digit => digit = 1)

private theorem cast_residueStep (modulus base acc : Nat) (bit : Bool) :
    ((residueStep modulus base acc bit : Nat) : ZMod modulus) =
      (acc : ZMod modulus) * acc *
        (if bit then (base : ZMod modulus) else 1) := by
  simp [residueStep, ZMod.natCast_mod]

private theorem fold_correct (modulus base : Nat) (bits : List Bool)
    (acc currentExponent : Nat)
    (hacc : (acc : ZMod modulus) =
      (base : ZMod modulus) ^ currentExponent) :
    ((bits.foldl (residueStep modulus base) acc : Nat) : ZMod modulus) =
      (base : ZMod modulus) ^
        bits.foldl exponentStep currentExponent := by
  induction bits generalizing acc currentExponent with
  | nil => simpa using hacc
  | cons bit tail ih =>
      simp only [List.foldl_cons]
      apply ih
      rw [cast_residueStep, hacc]
      cases bit
      · simp [exponentStep, bitValue,
          show 2 * currentExponent =
            currentExponent + currentExponent by omega,
          pow_add]
      · simp [exponentStep, bitValue,
          show 2 * currentExponent + 1 =
            currentExponent + currentExponent + 1 by omega,
          pow_add, mul_assoc]

theorem residue_correct (modulus base : Nat) (bits : List Bool) :
    ((residue modulus base bits : Nat) : ZMod modulus) =
      (base : ZMod modulus) ^ exponent bits := by
  apply fold_correct modulus base bits (1 % modulus) 0
  simp [ZMod.natCast_mod]

theorem pow_eq_of_certificate (modulus base claimedExponent result : Nat)
    (bits : List Bool)
    (hexponent : exponent bits = claimedExponent)
    (hresidue : residue modulus base bits = result) :
    (base : ZMod modulus) ^ claimedExponent = (result : ZMod modulus) := by
  rw [← hexponent, ← residue_correct, hresidue]

theorem pow_ne_one_of_certificate (modulus base claimedExponent result : Nat)
    (bits : List Bool)
    (hexponent : exponent bits = claimedExponent)
    (hresidue : residue modulus base bits = result)
    (hresult : (result : ZMod modulus) ≠ 1) :
    (base : ZMod modulus) ^ claimedExponent ≠ 1 := by
  rw [pow_eq_of_certificate modulus base claimedExponent result bits
    hexponent hresidue]
  exact hresult

end GarblingPrize.Submission.PowCertificate
