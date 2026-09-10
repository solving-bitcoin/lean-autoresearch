import G1Release.Submission.BytePacking
import G1Release.Submission.FixedCodec

namespace G1Release.Submission.HintCodec
open G1Release.Math
abbrev natLE := BytePacking.encode
abbrev natLE32 := BytePacking.encode 32
abbrev decodeNatLE (bytes : Bytes n) := ByteArithmetic.read bytes n (Nat.le_refl n)

theorem decodeNatLE_natLE_of_lt (n value : Nat) (h : value < 2^(8*n)) :
    decodeNatLE (natLE n value) = value := by
  change ByteArithmetic.read (BytePacking.encode n value) n _ = value
  rw [BytePacking.read_encode, Nat.mod_eq_of_lt (by simpa [Nat.mul_comm] using h)]

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


end G1Release.Submission.HintCodec
