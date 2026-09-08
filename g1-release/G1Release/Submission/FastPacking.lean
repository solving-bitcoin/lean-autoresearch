import G1Release.Submission.BytePacking
import GarblingPrize.Protected.Bytes

set_option maxRecDepth 4096
set_option maxHeartbeats 200000

namespace G1Release.Submission.FastPacking
open SecretRelease

@[inline] def byte (word : UInt64) (index : Fin 8) : UInt8 :=
  (word >>> UInt64.ofNat (index.val*8)).toUInt8

theorem byte_eq (value : Nat) (index : Fin 8) :
    byte (UInt64.ofNat value) index = UInt8.ofNat (value >>> (index.val*8)) := by
  apply UInt8.toNat.inj
  have hs : index.val*8 < 64 := by omega
  have hl : index.val*8 < 2^64 := hs.trans (by decide)
  simp only [byte,UInt64.toNat_toUInt8,UInt64.toNat_shiftRight,UInt64.toNat_ofNat',
    Nat.mod_eq_of_lt hl,Nat.mod_eq_of_lt hs,UInt8.toNat_ofNat']
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_mod_two_pow,Nat.testBit_shiftRight]
  by_cases hi : i < 8
  · have hj : index.val*8+i < 64 := by omega
    simp only [hi,hj,decide_true,Bool.true_and]
  · simp only [hi,decide_false,Bool.false_and]

/-- Four large-integer shifts followed by machine-word byte extraction. -/
def encode (value : Nat) : Bytes 32 :=
  let words := Vector.ofFn fun i : Fin 4 => UInt64.ofNat (value >>> (i.val*64))
  Vector.ofFn fun i => byte (words.get ⟨i.val/8,by omega⟩) ⟨i.val%8,Nat.mod_lt _ (by decide)⟩

theorem encode_eq (value : Nat) : encode value = BytePacking.encode 32 value := by
  apply Vector.ext
  intro i hi
  simp only [encode,BytePacking.encode,Vector.getElem_ofFn,Vector.get_ofFn,byte_eq]
  rw [← Nat.shiftRight_add]
  have hs : i/8*64+i%8*8 = 8*i := by omega
  rw [hs]

/-- Fuse byte extraction with the pad XOR, avoiding a temporary plaintext vector. -/
def encrypt (value : Nat) (pad : Bytes 32) : Bytes 32 :=
  let words := Vector.ofFn fun i : Fin 4 => UInt64.ofNat (value >>> (i.val*64))
  Vector.ofFn fun i => byte (words.get ⟨i.val/8,by omega⟩) ⟨i.val%8,Nat.mod_lt _ (by decide)⟩ ^^^ pad.get i

theorem encrypt_eq (value : Nat) (pad : Bytes 32) :
    encrypt value pad = GarblingPrize.Protected.Bytes.xor (BytePacking.encode 32 value) pad := by
  rw [← encode_eq]
  apply Vector.ext
  intro i hi
  simp only [encrypt,encode,GarblingPrize.Protected.Bytes.xor,GarblingPrize.Protected.Bytes.ofFn,
    Vector.getElem_ofFn,Vector.get_ofFn,Vector.get_eq_getElem]

end G1Release.Submission.FastPacking
