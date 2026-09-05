import Batteries.Data.ByteArray
import Batteries.Data.Vector.Lemmas

namespace Blake3Prize.Baselines.HalfGates.Framing

/-- All fields are fixed-width bytes, including the adapter selector byte.
There is no alternate serialization or unscored framing channel. -/
def encode (value : Vector UInt8 n) : ByteArray := ⟨value.toArray⟩

def decode (n : Nat) (input : ByteArray) : Option (Vector UInt8 n) :=
  if h : input.size = n then some ⟨input.data,h⟩ else none

@[simp] theorem encode_size (value : Vector UInt8 n) : (encode value).size = n :=
  value.size_toArray

@[simp] theorem decode_encode (value : Vector UInt8 n) :
    decode n (encode value) = some value := by
  cases value with
  | mk data h => simp [decode, encode, ByteArray.size, h]

theorem encode_decode {bytes : ByteArray} {value : Vector UInt8 n}
    (h : decode n bytes = some value) : encode value = bytes := by
  unfold decode at h
  split at h
  · simp only [Option.some.injEq] at h
    subst value
    cases bytes
    rfl
  · contradiction

end Blake3Prize.Baselines.HalfGates.Framing
