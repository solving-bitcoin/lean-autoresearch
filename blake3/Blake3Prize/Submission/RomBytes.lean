import SecretRelease.Encoding

/-! Executable label operations for the new ROM-certified candidate.
These facts concern exact bytes and do not assume anything about the hash. -/
namespace Blake3Prize.Submission.RomBytes
open SecretRelease

@[inline] def xor (left right : Bytes n) : Bytes n :=
  Vector.ofFn fun i => left.get i ^^^ right.get i

def zero (n : Nat) : Bytes n := Vector.replicate n 0

@[inline] def encode (value : Bytes n) : ByteArray := ⟨value.toArray⟩

def decode (n : Nat) (bytes : ByteArray) : Option (Bytes n) :=
  if h : bytes.size = n then some ⟨bytes.data,h⟩ else none

theorem xor_cancel_right (left right : Bytes n) : xor (xor left right) right = left := by
  apply Vector.ext
  intro i hi
  simp only [xor,Vector.getElem_ofFn,Vector.get_eq_getElem]
  rw [UInt8.xor_assoc]
  simp

theorem xor_cancel_left (left right : Bytes n) : xor left (xor left right) = right := by
  apply Vector.ext
  intro i hi
  simp only [xor,Vector.getElem_ofFn,Vector.get_eq_getElem]
  rw [← UInt8.xor_assoc]
  simp

@[simp] theorem zero_xor (value : Bytes n) : xor (zero n) value = value := by
  apply Vector.ext
  intro i hi
  simp [xor,zero,Vector.get_eq_getElem]

@[simp] theorem encode_size (value : Bytes n) : (encode value).size = n :=
  value.size_toArray

theorem decode_encode (value : Bytes n) : decode n (encode value) = some value := by
  cases value with
  | mk data h => simp [decode,encode,ByteArray.size,h]

theorem encode_decode {bytes : ByteArray} {value : Bytes n}
    (h : decode n bytes = some value) : encode value = bytes := by
  unfold decode at h
  split at h
  · cases Option.some.inj h
    cases bytes
    rfl
  · contradiction

def xorEquiv (mask : Label) : Label ≃ Label where
  toFun := xor mask
  invFun := xor mask
  left_inv := xor_cancel_left mask
  right_inv := xor_cancel_left mask

end Blake3Prize.Submission.RomBytes
