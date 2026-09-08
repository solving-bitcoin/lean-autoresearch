import G1Release.Submission.ByteArithmetic

namespace G1Release.Submission.BytePacking
open SecretRelease

def encode (width value : Nat) : SecretRelease.Bytes width :=
  Vector.ofFn fun i => UInt8.ofNat (value >>> (8*i.val))

theorem read_encode (width value : Nat) :
    ByteArithmetic.read (encode width value) width (Nat.le_refl width) = value % 2^(width*8) := by
  rw [ByteArithmetic.read_eq]
  unfold ByteArithmetic.bitNat
  have hf :
      (fun i : Fin (width*8) => ((encode width value).get ⟨i.val/8,by omega⟩).toNat.testBit (i.val%8)) =
      (fun i : Fin (width*8) => value.testBit i.val) := by
    funext i
    simp only [encode, Vector.get_ofFn, UInt8.toNat_ofNat', Nat.testBit_mod_two_pow,
      Nat.testBit_shiftRight]
    have hm : i.val%8 < 8 := Nat.mod_lt _ (by decide)
    simp only [hm, decide_true, Bool.true_and]
    congr 1
    omega
  rw [hf, Nat.ofBits_testBit]

end G1Release.Submission.BytePacking
