import GarblingPrize.Submission.FixedCodec

namespace GarblingPrize.Submission.PackedBits

open GarblingPrize.Protected

/-! A linear-time, byte-aligned codec for bit functions. -/

abbrev Bits (byteCount : Nat) := Fin byteCount → Fin 8 → Bool

/-- Pack one byte with machine-word operations.  The previous
`BitVec.ofNat (Nat.ofBits ...)` formulation recomputed `2^8` through the
big-natural runtime for every emitted byte. -/
def encodeByte (bits : Fin 8 → Bool) : UInt8 :=
  Codec.byteOfBits bits

@[simp] private theorem iteByte_getElem (selected : Bool) (value : UInt8)
    (bit : Nat) (hbit : bit < 8) :
    (if selected then value else 0).toBitVec[bit] =
      (selected && value.toBitVec[bit]) := by
  cases selected <;> simp

@[simp] theorem encodeByte_getLsbD (bits : Fin 8 → Bool) (bit : Fin 8) :
    (encodeByte bits).toBitVec.getLsbD bit.val = bits bit := by
  exact Codec.byteOfBits_getLsbD bits bit

theorem encodeByte_getLsbD_nat (bits : Fin 8 → Bool) (bit : Nat)
    (hbit : bit < 8) :
    (encodeByte bits).toBitVec.getLsbD bit = bits ⟨bit, hbit⟩ := by
  exact encodeByte_getLsbD bits ⟨bit, hbit⟩

/-- Pack little-endian bits eight at a time without constructing natural
numbers. -/
def encode (bits : Bits byteCount) : Bytes byteCount :=
  Bytes.ofFn fun byte =>
    encodeByte (bits byte)

/-- The protected byte-major little-endian bit view is the inverse layout. -/
def decode (bytes : Bytes byteCount) : Bits byteCount :=
  fun byte bit => bytes.get byte |>.toBitVec.getLsbD bit.val

@[simp] theorem encode_byteSize (bits : Bits byteCount) :
    (encode bits).toByteArray.size = byteCount :=
  Bytes.size_toByteArray _

def encodeArray (bits : Bits byteCount) : ByteArray :=
  (encode bits).toByteArray

def decodeArray (byteCount : Nat) (input : ByteArray) :
    Except WireDecodeError (Bits byteCount) :=
  match Bytes.ofByteArray? byteCount input with
  | none => .error .invalidLength
  | some bytes => .ok (decode bytes)

@[simp] theorem decode_encode (bits : Bits byteCount) :
    decode (encode bits) = bits := by
  funext byte bit
  unfold decode encode
  simp only [Bytes.ofFn, Vector.get_eq_getElem, Vector.getElem_ofFn]
  exact encodeByte_getLsbD (bits byte) bit

@[simp] theorem encode_decode (bytes : Bytes byteCount) :
    encode (decode bytes) = bytes := by
  apply Vector.ext
  intro byte hbyte
  rw [← UInt8.toBitVec_inj]
  apply BitVec.eq_of_getElem_eq
  intro bit hbit
  unfold encode decode
  simp only [Bytes.ofFn, Vector.getElem_ofFn]
  simp [Vector.get_eq_getElem]
  exact encodeByte_getLsbD
    (fun selected => bytes.get ⟨byte, hbyte⟩ |>.toBitVec.getLsbD selected.val)
    ⟨bit, hbit⟩

@[simp] theorem encodeArray_size (bits : Bits byteCount) :
    (encodeArray bits).size = byteCount :=
  encode_byteSize bits

@[simp] theorem decodeArray_encodeArray (bits : Bits byteCount) :
    decodeArray byteCount (encodeArray bits) = .ok bits := by
  simp [decodeArray, encodeArray]

theorem encodeArray_decodeArray {input : ByteArray} {bits : Bits byteCount}
    (h : decodeArray byteCount input = .ok bits) :
    encodeArray bits = input := by
  unfold decodeArray at h
  cases hfixed : Bytes.ofByteArray? byteCount input with
  | none => simp [hfixed] at h
  | some fixed =>
      have hbits : decode fixed = bits := by
        simp only [hfixed] at h
        exact Except.ok.inj h
      rw [← hbits]
      simp [encodeArray]
      exact (Bytes.ofByteArray?_eq_some_iff.mp hfixed).symm

end GarblingPrize.Submission.PackedBits
