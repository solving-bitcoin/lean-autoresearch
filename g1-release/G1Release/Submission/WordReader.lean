import G1Release.Submission.FlatArithmetic

namespace G1Release.Submission.WordReader
open SecretRelease

/-- A fully unrolled, machine-word read of eight little-endian bytes. -/
@[inline] def word (byte : Fin 8 → UInt8) : UInt64 :=
  (UInt64.ofNat (byte 7).toNat * 72057594037927936 + (UInt64.ofNat (byte 6).toNat * 281474976710656 + (UInt64.ofNat (byte 5).toNat * 1099511627776 + (UInt64.ofNat (byte 4).toNat * 4294967296 + (UInt64.ofNat (byte 3).toNat * 16777216 + (UInt64.ofNat (byte 2).toNat * 65536 + (UInt64.ofNat (byte 1).toNat * 256 + (UInt64.ofNat (byte 0).toNat * 1 + 0))))))))

theorem word_eq (byte : Fin 8 → UInt8) :
    word byte = UInt64.ofNat (FlatArithmetic.read byte 8 (Nat.le_refl 8)) := by
  unfold word
  simp only [FlatArithmetic.read,Nat.shiftLeft_eq,UInt64.ofNat_add,UInt64.ofNat_mul]
  rfl

theorem word_nat (byte : Fin 8 → UInt8) :
    (word byte).toNat = FlatArithmetic.read byte 8 (Nat.le_refl 8) := by
  rw [word_eq,UInt64.toNat_ofNat',Nat.mod_eq_of_lt]
  rw [FlatArithmetic.read_ofFn]
  exact ByteArithmetic.read_lt (Vector.ofFn byte)

end G1Release.Submission.WordReader
