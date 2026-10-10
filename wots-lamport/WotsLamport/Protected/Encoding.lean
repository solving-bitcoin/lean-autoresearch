import SecretRelease.Encoding
import Mathlib.Tactic

namespace WotsLamport.Protected
open SecretRelease

abbrev Message := Bytes 32
abbrev Word := Fin 67 → Nat
abbrev EncodedMessage := Message

def inputCodec : Codec Message := Codec.byteVector 32
def outputCodec : Codec Message := Codec.byteVector 32
def privateCodec : Codec Unit := Codec.unit

/-- Upstream byte order: high nibble, then low nibble. -/
def messageDigit (m : Message) (i : Fin 64) : Nat :=
  if i.val % 2 = 0 then m[i.val / 2].toNat / 16 else m[i.val / 2].toNat % 16

theorem messageDigit_le (m : Message) (i : Fin 64) : messageDigit m i ≤ 15 := by
  have hb := (m[i.val / 2]).toFin.isLt
  unfold messageDigit
  split <;> omega

def messageSum (m : Message) : Nat := ∑ i : Fin 64, messageDigit m i
def checksum (m : Message) : Nat := 960 - messageSum m

theorem messageSum_le (m : Message) : messageSum m ≤ 960 := by
  have h := Finset.sum_le_sum (s := Finset.univ)
    (fun (i : Fin 64) _ => messageDigit_le m i)
  simpa [messageSum] using h

def maximum (i : Fin 67) : Nat := if i.val = 64 ∨ i.val = 65 then 7 else 15
def weight (i : Fin 67) : Nat := if i.val = 65 then 8 else if i.val = 66 then 64 else 1

/-- Checksum coordinates are least-significant first, radix 8,8,16. -/
def encodeWord (m : Message) (i : Fin 67) : Nat :=
  if h : i.val < 64 then messageDigit m ⟨i.val,h⟩
  else if i.val = 64 then checksum m % 8
  else if i.val = 65 then (checksum m / 8) % 8
  else checksum m / 64

def parseWord (w : Word) : Message := Vector.ofFn fun i =>
  UInt8.ofNat (16 * w ⟨2*i.val, by omega⟩ + w ⟨2*i.val+1, by omega⟩)

/-- Re-encoding prevents bad checksums, out-of-range digits and aliases of words.
This says nothing about uniqueness of raw Script witness bytes. -/
def decodeWord (w : Word) : Option Message :=
  let m := parseWord w
  if encodeWord m = w then some m else none

theorem parse_encode (m : Message) : parseWord (encodeWord m) = m := by
  apply Vector.ext
  intro i hi
  have hsplit : 16 * (m[i].toNat / 16) + m[i].toNat % 16 = m[i].toNat := by omega
  simp [parseWord, encodeWord, messageDigit, hi, show 2*i < 64 by omega,
    show 2*i+1 < 64 by omega, show 2*i/2 = i by omega,
    show (2*i+1)/2 = i by omega, show 2*i%2 = 0 by omega,
    show (2*i+1)%2 = 1 by omega, hsplit]

theorem decode_encode (m : Message) : decodeWord (encodeWord m) = some m := by
  simp [decodeWord, parse_encode]

theorem checksum_weighted (m : Message) :
    messageSum m + checksum m % 8 + 8 * ((checksum m / 8) % 8) +
      64 * (checksum m / 64) = 960 := by
  have hs := messageSum_le m
  dsimp [checksum]
  omega

theorem encodeWord_le (m : Message) (i : Fin 67) : encodeWord m i ≤ maximum i := by
  have hs : checksum m ≤ 960 := Nat.sub_le _ _
  by_cases hi : i.val < 64
  · simpa [encodeWord, maximum, hi, show i.val ≠ 64 by omega,
      show i.val ≠ 65 by omega] using messageDigit_le m ⟨i.val,hi⟩
  · simp only [encodeWord, dif_neg hi, maximum]
    split_ifs <;> omega

/-- Output bit i belongs to nibble 2*(i/8)+1 for low bits and 2*(i/8) for high bits. -/
def bitChain (i : Fin 256) : Fin 64 :=
  ⟨2*(i.val/8) + if i.val%8 < 4 then 1 else 0, by split <;> omega⟩
def bitInNibble (i : Fin 256) : Nat := i.val % 4
def digitBit (i : Fin 256) (d : Nat) : Bool := d.testBit (bitInNibble i)

abbrev AcceptedWord := {w : Word // ∃ m, encodeWord m = w}

end WotsLamport.Protected
