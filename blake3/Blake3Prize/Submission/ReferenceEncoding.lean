import Blake3Prize.Protected.Target
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.FinCases

set_option maxRecDepth 4096

/-! Byte/word bridges used by the two submissions. The challenge itself only
specifies Clean's byte hash and the shared byte-major, LSB-first codecs. -/
namespace Blake3Prize.Submission
open Blake3Prize.Protected SecretRelease

def inputBit (input : Input) (i : Fin 512) : Bool :=
  ((Codec.byteVector 64).encode input).get i

namespace ReferenceEncoding

theorem encoded_get (bytes : Bytes n) (i : Fin (n*8)) :
    ((Codec.byteVector n).encode bytes).get i =
      bytes[i.val/8].toNat.testBit (i.val%8) := by
  delta Codec.byteVector
  exact Vector.get_ofFn _ _

theorem word_get (input : Input) (i : Fin 16) :
    (inputWords input).get i = input[4*i.val].toNat +
      input[4*i.val+1].toNat*256 + input[4*i.val+2].toNat*65536 +
      input[4*i.val+3].toNat*16777216 := by
  delta inputWords Specs.BLAKE3.bytesToWords
  simp [Vector.get_eq_getElem, Nat.mul_comm]

theorem word_lt (input : Input) (i : Fin 16) : (inputWords input).get i < 2^32 := by
  rw [word_get]
  have h0 := input[4*i.val].toFin.isLt
  have h1 := input[4*i.val+1].toFin.isLt
  have h2 := input[4*i.val+2].toFin.isLt
  have h3 := input[4*i.val+3].toFin.isLt
  change input[4*i.val].toNat < 256 at h0
  change input[4*i.val+1].toNat < 256 at h1
  change input[4*i.val+2].toNat < 256 at h2
  change input[4*i.val+3].toNat < 256 at h3
  omega

private theorem split_four (a b c d : Nat)
    (ha : a < 256) (hb : b < 256) (hc : c < 256) (hd : d < 256) :
    let w := a+b*256+c*65536+d*16777216
    w % 256 = a ∧ w/256%256 = b ∧ w/65536%256 = c ∧ w/16777216%256 = d := by
  dsimp only
  omega

theorem word_byte (input : Input) (i : Fin 16) (j : Fin 4) :
    (inputWords input).get i / 2^(8*j.val) % 256 = input[4*i.val+j.val].toNat := by
  rw [word_get]
  have h0 : input[4*i.val].toNat < 256 := input[4*i.val].toFin.isLt
  have h1 : input[4*i.val+1].toNat < 256 := input[4*i.val+1].toFin.isLt
  have h2 : input[4*i.val+2].toNat < 256 := input[4*i.val+2].toFin.isLt
  have h3 : input[4*i.val+3].toNat < 256 := input[4*i.val+3].toFin.isLt
  have h := split_four _ _ _ _ h0 h1 h2 h3
  fin_cases j
  · simpa only [Fin.val_zero, Nat.mul_zero, Nat.pow_zero, Nat.div_one, Nat.add_zero] using h.1
  · exact h.2.1
  · exact h.2.2.1
  · exact h.2.2.2

theorem word_bit (input : Input) (i : Fin 16) (j : Fin 32) :
    ((inputWords input).get i).testBit j.val =
      inputBit input ⟨32*i.val+j.val,by omega⟩ := by
  have h := congrArg (fun n : Nat => n.testBit (j.val%8))
    (word_byte input i ⟨j.val/8,by omega⟩)
  change (((inputWords input).get i / 2^(8*(j.val/8))) % 2^8).testBit (j.val%8) = _ at h
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow] at h
  have hj : j.val%8 < 8 := Nat.mod_lt _ (by decide)
  simp only [decide_eq_true hj, Bool.true_and] at h
  have he : j.val%8+8*(j.val/8) = j.val := by omega
  rw [he] at h
  change _ = ((Codec.byteVector 64).encode input).get (⟨32*i.val+j.val,by omega⟩ : Fin 512)
  rw [encoded_get]
  have hdiv : (32*i.val+j.val)/8 = 4*i.val+j.val/8 := by omega
  have hmod : (32*i.val+j.val)%8 = j.val%8 := by omega
  simpa only [hdiv, hmod] using h

theorem output_bit (words : Vector Nat 8) (i : Fin 256) :
    ((Codec.byteVector 32).encode (wordsToBytes words)).get i =
      (words.get ⟨i.val/32,by omega⟩).testBit (i.val%32) := by
  rw [encoded_get]
  delta wordsToBytes
  simp only [Vector.getElem_ofFn, UInt8.toNat_ofNat']
  change ((words[(i.val/8)/4] >>> (8*((i.val/8)%4))) % 2^8).testBit (i.val%8) = _
  rw [Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]
  have hi : i.val%8 < 8 := Nat.mod_lt _ (by decide)
  simp only [decide_eq_true hi, Bool.true_and, Vector.get_eq_getElem]
  congr 2 <;> omega

theorem reference_encoded (input : Input) (i : Fin 256) :
    ((Codec.byteVector 32).encode (reference input)).get i =
      ((referenceWords (inputWords input)).get ⟨i.val/32,by omega⟩).testBit (i.val%32) :=
  output_bit _ i

end ReferenceEncoding
end Blake3Prize.Submission
