import GarblingPrize.Protected.Bytes
import Batteries.Data.Nat.Basic
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.FinCases

namespace GarblingPrize.Protected

/-!
# Canonical byte codecs

The decoder is deliberately small and total.  Every top-level parser finishes
with `Decoder.done`, which makes trailing bytes an explicit error.
-/

inductive WireDecodeError where
  | unexpectedEnd
  | invalidMagic
  | invalidVersion
  | invalidProfile
  | invalidLength
  | trailingBytes
  | malformed
deriving Repr, DecidableEq

structure Decoder where
  input : ByteArray
  position : Nat
deriving DecidableEq

namespace Decoder

def remaining (decoder : Decoder) : Nat :=
  decoder.input.size - decoder.position

def take (decoder : Decoder) (count : Nat) :
    Except WireDecodeError (ByteArray × Decoder) :=
  if _h : decoder.position + count ≤ decoder.input.size then
    let bytes := decoder.input.extract decoder.position (decoder.position + count)
    .ok (bytes, { decoder with position := decoder.position + count })
  else
    .error .unexpectedEnd

def takeFixed (decoder : Decoder) (count : Nat) :
    Except WireDecodeError (Bytes count × Decoder) := do
  let (bytes, next) ← decoder.take count
  match Bytes.ofByteArray? count bytes with
  | some fixed => pure (fixed, next)
  | none => throw .invalidLength

def byte (decoder : Decoder) : Except WireDecodeError (UInt8 × Decoder) := do
  let (bytes, next) ← decoder.takeFixed 1
  pure (bytes.get 0, next)

def done (decoder : Decoder) : Except WireDecodeError Unit :=
  if decoder.position = decoder.input.size then
    .ok ()
  else
    .error .trailingBytes

/-- Parse a fixed number of homogeneous values without partial array access. -/
def many (count : Nat) (decoder : Decoder)
    (parse : Decoder → Except WireDecodeError (α × Decoder)) :
    Except WireDecodeError (Array α × Decoder) :=
  loop count decoder #[]
where
  loop : Nat → Decoder → Array α → Except WireDecodeError (Array α × Decoder)
    | 0, current, output => pure (output, current)
    | remaining + 1, current, output => do
        let (value, next) ← parse current
        loop remaining next (output.push value)

end Decoder

namespace Codec

/-- Encode a natural into exactly `width` little-endian bytes.

Uses `>>>` instead of ` / 2 ^ _` so the native path does not call
`lean_nat_pow` on every byte of SHA padding / label codecs. -/
def natLE (width value : Nat) : Bytes width :=
  Bytes.ofFn fun i => UInt8.ofNat (value >>> (8 * i.val))

/-- The common field-word specialization.  Its Lean body keeps all codec
proofs tied to `natLE`; the protected executable replaces it with the exact
native byte export to avoid 32 separate big-natural shifts per ciphertext. -/
@[extern "lean_g1_nat_le_32"]
def natLE32 (value : Nat) : Bytes 32 :=
  natLE 32 value

/-- Encode a natural into exactly `width` big-endian bytes. -/
def natBE (width value : Nat) : Bytes width :=
  Bytes.ofFn fun i =>
    UInt8.ofNat (value >>> (8 * (width - 1 - i.val)))

/-- Flatten fixed bytes in byte-major, least-significant-bit-first order. -/
def byteBitsLE (bytes : Bytes width) : Fin (8 * width) → Bool :=
  fun bit =>
    let byteIndex : Fin width := ⟨bit.val / 8, by omega⟩
    (bytes.get byteIndex).toBitVec.getLsbD (bit.val % 8)

/-- Construct one byte from its little-endian bits using fixed machine-word
operations. -/
def byteOfBits (bits : Fin 8 → Bool) : UInt8 :=
  (if bits 0 then 1 else 0) |||
  (if bits 1 then 2 else 0) |||
  (if bits 2 then 4 else 0) |||
  (if bits 3 then 8 else 0) |||
  (if bits 4 then 16 else 0) |||
  (if bits 5 then 32 else 0) |||
  (if bits 6 then 64 else 0) |||
  (if bits 7 then 128 else 0)

@[simp] private theorem iteByte_getElem (selected : Bool) (value : UInt8)
    (bit : Nat) (hbit : bit < 8) :
    (if selected then value else 0).toBitVec[bit] =
      (selected && value.toBitVec[bit]) := by
  cases selected <;> simp

@[simp] theorem byteOfBits_getLsbD (bits : Fin 8 → Bool) (bit : Fin 8) :
    (byteOfBits bits).toBitVec.getLsbD bit.val = bits bit := by
  fin_cases bit <;> simp [byteOfBits]

/-- Pack four 254-bit prefixes into 127 bytes.  The transparent definition is
the wire-format specification; the protected executable uses the exact native
implementation to avoid one Lean function/proof boundary per emitted bit. -/
@[extern "lean_g1_pack_four_254"]
def packFour254 (words : Vector (Bytes 32) 4) : Bytes 127 :=
  Bytes.ofFn fun byte =>
    byteOfBits fun bit =>
      let flat := 8 * byte.val + bit.val
      byteBitsLE (words.get ⟨flat / 254, by
        have hbyte := byte.isLt
        have hbit := bit.isLt
        omega⟩) ⟨flat % 254, by
          have := Nat.mod_lt flat (by omega : 0 < 254)
          omega⟩

@[simp] theorem packFour254_getLsbD (words : Vector (Bytes 32) 4)
    (byte : Fin 127) (bit : Fin 8) :
    ((packFour254 words).get byte).toBitVec.getLsbD bit.val =
      let flat := 8 * byte.val + bit.val
      byteBitsLE (words.get ⟨flat / 254, by
        have hbyte := byte.isLt
        have hbit := bit.isLt
        omega⟩) ⟨flat % 254, by
          have := Nat.mod_lt flat (by omega : 0 < 254)
          omega⟩ := by
  unfold packFour254
  simp only [Bytes.ofFn, Vector.get_eq_getElem, Vector.getElem_ofFn]
  exact byteOfBits_getLsbD _ bit

/-- Decode little-endian fixed bytes to a natural.

Uses shifts instead of `2 ^ (8 * i)` so the native path does not call
`lean_nat_pow` on every byte.  `CodecLemmas.decodeNatLE_eq_ofBits` still
identifies this with the historical bit-major `Nat.ofBits` wire layout. -/
@[inline] def decodeNatLE (bytes : Bytes width) : Nat :=
  Fin.foldl width
    (fun acc i =>
      acc + (bytes.get i).toNat * (1 <<< (8 * i.val))) 0

/-- Historical bit-level decoder retained for layout proofs. -/
def decodeNatLEBits (bytes : Bytes width) : Nat :=
  Nat.ofBits (byteBitsLE bytes)

/-- Decode big-endian fixed bytes to a natural. -/
def decodeNatBE (bytes : Bytes width) : Nat :=
  Fin.foldl width
    (fun acc i =>
      acc + (bytes.get i).toNat * 2 ^ (8 * (width - 1 - i.val))) 0

def u16LE (value : UInt16) : Bytes 2 :=
  natLE 2 value.toNat

def u32LE (value : UInt32) : Bytes 4 :=
  natLE 4 value.toNat

def u64LE (value : UInt64) : Bytes 8 :=
  natLE 8 value.toNat

def u64BE (value : UInt64) : Bytes 8 :=
  natBE 8 value.toNat

/-- ASCII constants used for magic values and domain separation. -/
def ascii (value : String) : ByteArray :=
  value.toUTF8

def expectMagic (decoder : Decoder) (magic : String) :
    Except WireDecodeError Decoder := do
  let expected := ascii magic
  let (actual, next) ← decoder.take expected.size
  if actual = expected then
    pure next
  else
    throw .invalidMagic

def expectByte (decoder : Decoder) (expected : UInt8)
    (error : WireDecodeError) : Except WireDecodeError Decoder := do
  let (actual, next) ← decoder.byte
  if actual = expected then
    pure next
  else
    throw error

def expectFixed (decoder : Decoder) (expected : Bytes n)
    (error : WireDecodeError) : Except WireDecodeError Decoder := do
  let (actual, next) ← decoder.takeFixed n
  if actual = expected then
    pure next
  else
    throw error

end Codec

end GarblingPrize.Protected

/-- Definitional `Except` bind reduction on a successful value.  Kept in the
root `Except` namespace so sequential `do`-block roundtrips across the
executable codecs can rewrite one bind at a time. -/
@[simp] theorem Except.bind_ok {α β ε : Type _} (a : α) (f : α → Except ε β) :
    Except.bind (Except.ok a) f = f a :=
  rfl

@[simp] theorem Except.bind_error {α β ε : Type _} (e : ε)
    (f : α → Except ε β) :
    Except.bind (Except.error e) f = Except.error e :=
  rfl
