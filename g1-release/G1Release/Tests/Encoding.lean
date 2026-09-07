import G1Release.Protected.Codecs

namespace G1Release.Tests.Encoding
open SecretRelease G1Release.Protected

/-- Byte-major, least-significant-bit-first transport; no length prefixes. -/
def bitsToBytes (bits : Vector Bool (8*n)) : ByteArray :=
  ⟨(Vector.ofFn fun i : Fin n => UInt8.ofNat (readNat bits (8*i.val) 8 (by omega))).toArray⟩
def bytesToBits (n : Nat) (bytes : ByteArray) : Option (Vector Bool (8*n)) :=
  if h : bytes.size = n then
    some (Vector.ofFn fun i => bytes[i.val / 8].toNat.testBit (i.val % 8))
  else none

@[simp] theorem bytesToBits_bitsToBytes (bits : Vector Bool (8*n)) :
    bytesToBits n (bitsToBytes bits) = some bits := by
  unfold bytesToBits
  rw [dif_pos (show (bitsToBytes bits).size = n by simp [bitsToBytes, ByteArray.size])]
  apply congrArg some
  apply Vector.ext
  intro i hi
  have hm : i % 8 < 8 := Nat.mod_lt _ (by decide)
  have he : 8 * (i / 8) + i % 8 = i := by omega
  simp only [Vector.getElem_ofFn, bitsToBytes, ByteArray.getElem_eq_getElem_data, Vector.toArray_ofFn,
    Array.getElem_ofFn, readNat, UInt8.toNat_ofNat']
  rw [Nat.mod_eq_of_lt (Nat.ofBits_lt_two_pow _), Nat.testBit_ofBits_lt _ _ hm]
  simp only [he]

theorem packBits_eq_old (bits : Vector Bool (8*n)) : packBits bits = bitsToBytes bits := by
  apply ByteArray.ext
  apply Array.ext
  · simp only [packBits, bitsToBytes, Vector.toArray_ofFn, Array.size_ofFn]
    omega
  · intro i hi hi'
    have hin : i < n := by
      simpa only [bitsToBytes, Vector.toArray_ofFn, Array.size_ofFn] using hi'
    simp only [packBits, bitsToBytes, Vector.toArray_ofFn, Array.getElem_ofFn, readNat]
    apply congrArg UInt8.ofNat
    apply congrArg Nat.ofBits
    funext j
    simp only [dif_pos (by omega : 8*i+j.val < 8*n)]

theorem unpackBits_eq_old (bytes : ByteArray) : unpackBits (8*n) bytes = bytesToBits n bytes := by
  unfold unpackBits bytesToBits
  have hwidth : (8*n+7)/8 = n := by omega
  simp only [hwidth]

theorem output_bytes_unchanged (out : Output) :
    encodeOutput out = bitsToBytes (n := 65) (outputCodec.encode out) := by
  exact packBits_eq_old (n := 65) (outputCodec.encode out)

end G1Release.Tests.Encoding
