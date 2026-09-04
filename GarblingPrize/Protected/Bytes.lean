import Batteries.Data.ByteArray
import Batteries.Data.Vector.Lemmas

namespace GarblingPrize.Protected

/-!
# Fixed-size executable byte strings

`Bytes n` is the boundary type used by every security-critical pure API.  It
is backed by a `Vector`, so its length is part of the type while compiled data
remains a flat array of bytes.
-/

abbrev Bytes (n : Nat) := Vector UInt8 n

namespace Bytes

/-- Convert fixed bytes to the packed representation used by file codecs. -/
@[inline] def toByteArray (value : Bytes n) : ByteArray :=
  ⟨value.toArray⟩

/-- Parse exactly `n` bytes.  No prefix or truncation is accepted. -/
def ofByteArray? (n : Nat) (input : ByteArray) : Option (Bytes n) :=
  if h : input.size = n then
    some ⟨input.data, h⟩
  else
    none

/-- Construct fixed bytes from a coordinate function. -/
@[inline] def ofFn (f : Fin n → UInt8) : Bytes n :=
  Vector.ofFn f

/-- The all-zero fixed byte string. -/
def zero (n : Nat) : Bytes n :=
  Vector.replicate n 0

/-- Pointwise byte XOR. -/
@[inline] def xor (left right : Bytes n) : Bytes n :=
  ofFn fun i => left.get i ^^^ right.get i

/-- Concatenate two fixed byte strings. -/
def append (left : Bytes n) (right : Bytes m) : Bytes (n + m) :=
  ⟨left.toArray ++ right.toArray, by simp⟩

/-- Take a statically bounded prefix. -/
def take (count : Nat) (value : Bytes n) (h : count ≤ n) : Bytes count :=
  ofFn fun i => value.get ⟨i.val, Nat.lt_of_lt_of_le i.isLt h⟩

@[simp] theorem size_toByteArray (value : Bytes n) :
    value.toByteArray.size = n := by
  exact value.size_toArray

@[simp] theorem ofByteArray?_toByteArray (value : Bytes n) :
    ofByteArray? n value.toByteArray = some value := by
  cases value with
  | mk data h =>
      unfold ofByteArray? toByteArray
      split
      · congr
      · contradiction

theorem ofByteArray?_eq_some_iff {input : ByteArray} {value : Bytes n} :
    ofByteArray? n input = some value ↔ input = value.toByteArray := by
  constructor
  · intro h
    unfold ofByteArray? at h
    split at h
    · simp only [Option.some.injEq] at h
      subst value
      cases input
      rfl
    · contradiction
  · intro h
    subst input
    exact ofByteArray?_toByteArray value

@[simp] theorem toByteArray_injective :
    Function.Injective (@toByteArray n) := by
  intro left right h
  have := congrArg (ofByteArray? n) h
  simpa using this

@[simp] theorem xor_self (value : Bytes n) : xor value value = zero n := by
  apply Vector.ext
  intro i hi
  simp [xor, zero, ofFn, Vector.get_eq_getElem]

@[simp] theorem xor_zero (value : Bytes n) : xor value (zero n) = value := by
  apply Vector.ext
  intro i hi
  simp [xor, zero, ofFn, Vector.get_eq_getElem]

@[simp] theorem zero_xor (value : Bytes n) : xor (zero n) value = value := by
  apply Vector.ext
  intro i hi
  simp [xor, zero, ofFn, Vector.get_eq_getElem]

theorem xor_cancel_right (left right : Bytes n) :
    xor (xor left right) right = left := by
  apply Vector.ext
  intro i hi
  simp only [xor, ofFn, Vector.getElem_ofFn, Vector.get_eq_getElem]
  rw [UInt8.xor_assoc]
  simp

theorem xor_cancel_left (left right : Bytes n) :
    xor left (xor left right) = right := by
  apply Vector.ext
  intro i hi
  simp only [xor, ofFn, Vector.getElem_ofFn, Vector.get_eq_getElem]
  rw [← UInt8.xor_assoc]
  simp

@[simp] theorem toByteArray_append (left : Bytes n) (right : Bytes m) :
    (append left right).toByteArray =
      left.toByteArray ++ right.toByteArray := by
  apply ByteArray.ext
  simp [append, toByteArray]

end Bytes

end GarblingPrize.Protected
