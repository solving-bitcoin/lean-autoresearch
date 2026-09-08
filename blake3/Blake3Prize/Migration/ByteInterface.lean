import Blake3Prize.Migration.Legacy.Reference
import Blake3Prize.Submission.ReferenceEncoding
import Blake3Prize.Protected.Wire

/-! Exact transport from the former GF(2) interface. These historical
equivalence proofs are optional evidence, not challenge requirements. -/
namespace Blake3Prize.Migration
open Blake3Prize.Protected SecretRelease
open Blake3Prize.Submission

set_option maxRecDepth 4096

@[simp] theorem legacy_bit_roundtrip (b : Legacy.Bit) : Legacy.bitOfBool (b.val == 1) = b := by
  fin_cases b <;> rfl
@[simp] theorem legacy_bool_roundtrip (b : Bool) : ((Legacy.bitOfBool b).val == 1) = b := by
  cases b <;> rfl

/-- The former protected codec, kept only to state the migration theorem. -/
def legacyCodec (n : Nat) : Codec (Vector Legacy.Bit n) where
  width := n
  encode := fun v => v.map fun b => b.val == 1
  decode := fun v => some (v.map Legacy.bitOfBool)
  decode_encode := by intro v; apply congrArg some; ext i hi; simp
  encode_decode := by
    intro bits a h
    cases Option.some.inj h
    ext i hi; simp

def toLegacy (bytes : Bytes n) : Vector Legacy.Bit (n*8) :=
  ((Codec.byteVector n).encode bytes).map Legacy.bitOfBool

def fromLegacy (bits : Vector Legacy.Bit (n*8)) : Bytes n :=
  Vector.ofFn fun i => UInt8.ofNat (Nat.ofBits fun j : Fin 8 =>
    ((legacyCodec (n*8)).encode bits).get (⟨i.val*8+j.val,by omega⟩ : Fin (n*8)))

theorem encoding_preserved (bytes : Bytes n) :
    (legacyCodec (n*8)).encode (toLegacy bytes) = (Codec.byteVector n).encode bytes := by
  change (((Codec.byteVector n).encode bytes).map Legacy.bitOfBool).map (fun b => b.val == 1) = _
  simp only [Vector.map_map, Function.comp_def, legacy_bool_roundtrip]
  exact Vector.map_id _

theorem from_to (bytes : Bytes n) : fromLegacy (toLegacy bytes) = bytes := by
  have h := (Codec.byteVector n).decode_encode bytes
  change some (Vector.ofFn fun i => UInt8.ofNat (Nat.ofBits fun j : Fin 8 =>
    ((Codec.byteVector n).encode bytes).get (⟨i.val*8+j.val,by omega⟩ : Fin (n*8)))) = some bytes at h
  unfold fromLegacy
  rw [encoding_preserved]
  exact Option.some.inj h

theorem to_from (bits : Vector Legacy.Bit (n*8)) : toLegacy (fromLegacy bits) = bits := by
  have h := (Codec.byteVector n).encode_decode ((legacyCodec (n*8)).encode bits)
    (fromLegacy bits) rfl
  unfold toLegacy
  rw [h]
  ext i hi
  simp [legacyCodec]

def byteEquiv (n : Nat) : Bytes n ≃ Vector Legacy.Bit (n*8) :=
  ⟨toLegacy, fromLegacy, from_to, to_from⟩

private theorem input_bit_bridge (bits : Vector Bool 512) (i : Fin 512) :
    Legacy.inputBit (bits.map Legacy.bitOfBool) i = bits.get i := by
  delta Legacy.inputBit
  simp only [Fin.getElem_fin, Vector.getElem_map, Vector.get_eq_getElem]
  cases h : bits[i.val] <;> rfl

theorem input_bit_preserved (input : Input) (i : Fin 512) :
    Legacy.inputBit (toLegacy input) i = ((Codec.byteVector 64).encode input).get i :=
  input_bit_bridge _ i

private theorem legacy_word (bits : Vector Bool 512) (i : Fin 16) :
    (Legacy.inputWords (bits.map Legacy.bitOfBool)).get i =
      (BitVec.ofBoolListLE ((Vector.ofFn fun j : Fin 32 =>
        bits.get ⟨32*i.val+j.val,by omega⟩).toList)).toNat := by
  delta Legacy.inputWords
  rw [Vector.get_ofFn]
  have h : (Vector.ofFn fun j : Fin 32 =>
      Legacy.inputBit (bits.map Legacy.bitOfBool) ⟨32*i.val+j.val,by omega⟩) =
      (Vector.ofFn fun j : Fin 32 => bits.get ⟨32*i.val+j.val,by omega⟩) := by
    apply Vector.ext
    intro j hj
    simp only [Vector.getElem_ofFn]
    exact input_bit_bridge bits _
  exact congrArg (fun v : Vector Bool 32 => (BitVec.ofBoolListLE v.toList).toNat) h

private theorem packed_word (bits : Vector Bool 32) (word : Nat) (hw : word < 2^32)
    (hb : ∀ j : Fin 32, word.testBit j.val = bits.get j) :
    (BitVec.ofBoolListLE bits.toList).toNat = word := by
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j < 32
  · have h : (BitVec.ofBoolListLE bits.toList).getLsbD j = bits.get ⟨j,hj⟩ := by
      rw [BitVec.getLsbD_ofBoolListLE]
      simp [hj, Vector.get_eq_getElem]
    exact h.trans (hb ⟨j,hj⟩).symm
  · have hp : 2^32 ≤ 2^j := Nat.pow_le_pow_right (by decide) (by omega)
    have bound : (BitVec.ofBoolListLE bits.toList).toNat < 2^32 := by
      simpa using (BitVec.ofBoolListLE bits.toList).isLt
    exact (Nat.testBit_eq_false_of_lt (bound.trans_le hp)).trans
      (Nat.testBit_eq_false_of_lt (hw.trans_le hp)).symm

private theorem words_bridge (bits : Vector Bool 512) (words : Vector Nat 16)
    (hw : ∀ i : Fin 16, words.get i < 2^32)
    (hb : ∀ (i : Fin 16) (j : Fin 32), (words.get i).testBit j.val =
      bits.get ⟨32*i.val+j.val,by omega⟩) :
    Legacy.inputWords (bits.map Legacy.bitOfBool) = words := by
  apply Vector.ext
  intro i hi
  let slice : Vector Bool 32 := Vector.ofFn fun j : Fin 32 => bits.get ⟨32*i+j.val,by omega⟩
  have hs (j : Fin 32) : (words.get ⟨i,hi⟩).testBit j.val = slice.get j :=
    (hb ⟨i,hi⟩ j).trans
      (Vector.get_ofFn (fun j : Fin 32 => bits.get ⟨32*i+j.val,by omega⟩) j).symm
  exact (legacy_word bits ⟨i,hi⟩).trans (packed_word slice (words.get ⟨i,hi⟩) (hw ⟨i,hi⟩) hs)

theorem words_preserved (input : Input) :
    Legacy.inputWords (toLegacy input) = inputWords input :=
  words_bridge ((Codec.byteVector 64).encode input) (inputWords input)
    (ReferenceEncoding.word_lt input) (ReferenceEncoding.word_bit input)

private theorem reference_words_preserved (words : Vector Nat 16) :
    Legacy.referenceWords words = referenceWords words := rfl

private theorem output_bits_preserved (words : Vector Nat 8) :
    toLegacy (wordsToBytes words) = Legacy.outputBits words := by
  have h : (Codec.byteVector 32).encode (wordsToBytes words) =
      (Vector.ofFn fun i : Fin 256 => (words.get ⟨i.val/32,by omega⟩).testBit (i.val%32)) := by
    apply @Vector.ext Bool 256
    intro i hi
    simp only [Vector.getElem_ofFn]
    exact ReferenceEncoding.output_bit words ⟨i,hi⟩
  exact (congrArg (fun bits : Vector Bool 256 => bits.map Legacy.bitOfBool) h).trans
    Vector.map_ofFn

theorem reference_preserved (input : Input) :
    toLegacy (reference input) = Legacy.reference (toLegacy input) := by
  delta reference Legacy.reference
  rw [words_preserved, reference_words_preserved]
  exact output_bits_preserved _

/-- Native input/output bytes are unchanged, including their bit order. -/
theorem wire_bytes_preserved (bytes : Bytes n) :
    (legacyCodec (n*8)).bytes.encode (toLegacy bytes) = (Codec.byteVector n).bytes.encode bytes := by
  change packBits ((legacyCodec (n*8)).encode (toLegacy bytes)) = _
  rw [encoding_preserved]
  rfl

end Blake3Prize.Migration
