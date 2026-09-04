import GarblingPrize.Submission.FixedCodec
import GarblingPrize.Submission.PackedBits

namespace GarblingPrize.Submission.IdealAffineTable

open scoped BigOperators
open GarblingPrize.Protected

abbrev Word := BN254.Fq
abbrev WordBytes := Bytes 32
abbrev Row := Bytes 64

/-- BN254 base-field elements have 254 significant bits.  The protected input
carrier reserves 256 bits per coordinate, but its two high bits are always
zero for canonical field elements and therefore need no encrypted rows. -/
def tableWidth : Nat := 254

/-- Two table rows contain four 254-bit ciphertexts, hence exactly 127 bytes. -/
def pairCount : Nat := 127
def pairByteCount : Nat := 127

/-- A complete table is 127 row pairs of 127 bytes each. -/
def tableByteCount : Nat := pairCount * pairByteCount

abbrev Ciphertext := Fin tableWidth → Bool
abbrev PackedPair := Bytes pairByteCount

def encodeWord (value : Word) : WordBytes :=
  Codec.natLE32 value.val

def decodeWord (bytes : WordBytes) : Option Word :=
  let value := Codec.decodeNatLE bytes
  if value < baseFieldModulus then some (value : Word) else none

private theorem baseFieldModulus_lt_two_pow_256 :
    baseFieldModulus < 2 ^ (8 * 32) := by
  norm_num [baseFieldModulus]

@[simp] theorem decodeWord_encodeWord (value : Word) :
    decodeWord (encodeWord value) = some value := by
  unfold decodeWord encodeWord Codec.natLE32
  rw [Codec.decodeNatLE_natLE_of_lt 32 value.val
    (Nat.lt_trans value.val_lt baseFieldModulus_lt_two_pow_256)]
  simp only [value.val_lt, ↓reduceIte]
  congr 1
  exact ZMod.natCast_zmod_val value

/-! The byte-aligned row helpers remain available to the independent
truth-table construction, although the affine tables below use packed pairs. -/

def row (falsePayload truePayload : WordBytes)
    (falsePad truePad : WordBytes) : Row :=
  Bytes.append (Bytes.xor falsePayload falsePad)
    (Bytes.xor truePayload truePad)

def rowHalf (selected : Bool) (value : Row) : WordBytes :=
  if selected then
    Bytes.ofFn fun i => value.get ⟨32 + i.val, by omega⟩
  else
    Bytes.ofFn fun i => value.get ⟨i.val, by omega⟩

@[simp] theorem rowHalf_row_false (falsePayload truePayload : WordBytes)
    (falsePad truePad : WordBytes) :
    rowHalf false (row falsePayload truePayload falsePad truePad) =
      Bytes.xor falsePayload falsePad := by
  apply Vector.ext
  intro i hi
  simp [rowHalf, row, Bytes.append, Bytes.ofFn, Bytes.xor,
    Vector.get_eq_getElem]

@[simp] theorem rowHalf_row_true (falsePayload truePayload : WordBytes)
    (falsePad truePad : WordBytes) :
    rowHalf true (row falsePayload truePayload falsePad truePad) =
      Bytes.xor truePayload truePad := by
  apply Vector.ext
  intro i hi
  simp [rowHalf, row, Bytes.append, Bytes.ofFn, Bytes.xor,
    Vector.get_eq_getElem]

def lowBit (bytes : WordBytes) (index : Fin tableWidth) : Bool :=
  Codec.byteBitsLE bytes ⟨index.val, by
    have := index.isLt
    norm_num [tableWidth] at this ⊢
    omega⟩

@[simp] theorem lowBit_xor (left right : WordBytes)
    (index : Fin tableWidth) :
    lowBit (Bytes.xor left right) index =
      Bool.xor (lowBit left index) (lowBit right index) := by
  unfold lowBit Codec.byteBitsLE Bytes.xor Bytes.ofFn
  simp only [Vector.getElem_ofFn, Vector.get_eq_getElem,
    UInt8.toBitVec_xor, BitVec.getLsbD_xor]

def encrypt (payload pad : WordBytes) : Ciphertext :=
  fun index => lowBit (Bytes.xor payload pad) index

/-- Restore a canonical 256-bit word after opening a packed ciphertext.  The
two omitted high bits are known to be zero in every field payload. -/
def openedBytes (ciphertext : Ciphertext) (pad : WordBytes) : WordBytes :=
  PackedBits.encode fun byte bit =>
    if h : 8 * byte.val + bit.val < tableWidth then
      Bool.xor (ciphertext ⟨8 * byte.val + bit.val, h⟩)
        (lowBit pad ⟨8 * byte.val + bit.val, h⟩)
    else
      false

def openCiphertext (ciphertext : Ciphertext) (pad : WordBytes) : Option Word :=
  decodeWord (openedBytes ciphertext pad)

private theorem byteBitsLE_natLE (width value : Nat)
    (index : Fin (8 * width)) :
    Codec.byteBitsLE (Codec.natLE width value) index =
      value.testBit index.val := by
  unfold Codec.byteBitsLE Codec.natLE
  simp only [Bytes.ofFn, Vector.get_eq_getElem, Vector.getElem_ofFn,
    UInt8.toBitVec_ofNat', BitVec.getLsbD_ofNat]
  have hmod : index.val % 8 < 8 := Nat.mod_lt _ (by omega)
  have hdecompose := Nat.mod_add_div index.val 8
  simp only [hmod, decide_true, Bool.true_and]
  rw [Nat.testBit_shiftRight]
  congr 1
  omega

private theorem encodeWord_high_bit_false (value : Word)
    (index : Fin (8 * 32)) (hindex : tableWidth ≤ index.val) :
    Codec.byteBitsLE (encodeWord value) index = false := by
  unfold encodeWord Codec.natLE32
  rw [byteBitsLE_natLE]
  apply Nat.testBit_lt_two_pow
  have hmodulus : baseFieldModulus < 2 ^ tableWidth := by
    norm_num [baseFieldModulus, tableWidth]
  exact (value.val_lt.trans hmodulus).trans_le
    (Nat.pow_le_pow_right (by decide) hindex)

@[simp] theorem openedBytes_encrypt (value : Word) (pad : WordBytes) :
    openedBytes (encrypt (encodeWord value) pad) pad = encodeWord value := by
  apply Vector.ext
  intro byte hbyte
  rw [← UInt8.toBitVec_inj]
  apply BitVec.eq_of_getElem_eq
  intro bit hbit
  simp only [← BitVec.getLsbD_eq_getElem hbit]
  let byteIndex : Fin 32 := ⟨byte, hbyte⟩
  let bitIndex : Fin 8 := ⟨bit, hbit⟩
  let index : Fin (8 * 32) := ⟨8 * byte + bit, by
    omega⟩
  unfold openedBytes PackedBits.encode
  simp only [Bytes.ofFn, Vector.getElem_ofFn]
  rw [PackedBits.encodeByte_getLsbD_nat _ bit hbit]
  change
    (if h : index.val < tableWidth then
      Bool.xor (encrypt (encodeWord value) pad ⟨index.val, h⟩)
        (lowBit pad ⟨index.val, h⟩)
    else false) = ((encodeWord value).get byteIndex).toBitVec.getLsbD bit
  split
  · rename_i hlow
    have hdiv : index.val / 8 = byte := by
      dsimp [index]
      omega
    have hmod : index.val % 8 = bit := by
      dsimp [index]
      omega
    unfold encrypt
    rw [lowBit_xor]
    unfold lowBit Codec.byteBitsLE
    simp only [hdiv, hmod, Vector.get_eq_getElem]
    rw [BitVec.getLsbD_eq_getElem hbit, Bool.xor_assoc, Bool.xor_self,
      Bool.xor_false]
  · rename_i hhigh
    have hfalse := encodeWord_high_bit_false value index
      (Nat.le_of_not_gt hhigh)
    have hdiv : index.val / 8 = byte := by
      dsimp [index]
      omega
    have hmod : index.val % 8 = bit := by
      dsimp [index]
      omega
    unfold Codec.byteBitsLE at hfalse
    simpa only [hdiv, hmod, Vector.get_eq_getElem] using hfalse.symm

@[simp] theorem openCiphertext_encrypt (value : Word) (pad : WordBytes) :
    openCiphertext (encrypt (encodeWord value) pad) pad = some value := by
  simp [openCiphertext]

structure Params where
  coefficient : Word
  constant : Word

def bitWord (bit : Bool) : Word :=
  if bit then 1 else 0

/-- Shared executable table of binary weights.  Materializing this closed
vector once avoids recomputing 254 modular exponentiations in every affine
table during native garbling. -/
def weightTable : Vector Word tableWidth :=
  Vector.ofFn fun index => (2 : Word) ^ index.val

def weight (index : Fin tableWidth) : Word :=
  weightTable[index.val]

@[simp] theorem weight_eq_pow (index : Fin tableWidth) :
    weight index = (2 : Word) ^ index.val := by
  simp [weight, weightTable, Vector.ofFn]

def share (params : Params) (mask : Word)
    (index : Fin tableWidth) (bit : Bool) : Word :=
  if bit then
    if params.coefficient = 0 then mask
    else if params.coefficient = 1 then weight index + mask
    else weight index * params.coefficient + mask
  else mask

theorem share_eq_weight (params : Params) (mask : Word)
    (index : Fin tableWidth) (bit : Bool) :
    share params mask index bit =
      weight index * params.coefficient * bitWord bit + mask := by
  cases bit
  · simp [share, bitWord]
  · by_cases hzero : params.coefficient = 0
    · simp [share, bitWord, hzero]
    · by_cases hone : params.coefficient = 1
      · simp [share, bitWord, hone]
      · simp [share, bitWord, hzero, hone]

def MaskFiber (constant : Word) :=
  { masks : Fin tableWidth → Word // ∑ i, masks i = constant }

def canonicalMasks (constant : Word) : MaskFiber constant :=
  let first : Fin tableWidth := ⟨0, by norm_num [tableWidth]⟩
  ⟨fun index => if index = first then constant else 0, by
    simp [first]⟩

instance (constant : Word) : Nonempty (MaskFiber constant) :=
  ⟨canonicalMasks constant⟩

private def flattenedCiphertexts
    (ciphertexts : Vector WordBytes 4) : PackedBits.Bits pairByteCount :=
  fun byte bit =>
    let flat := 8 * byte.val + bit.val
    lowBit (ciphertexts.get ⟨flat / tableWidth, by
        have hbyte := byte.isLt
        have hbit := bit.isLt
        norm_num [pairByteCount, tableWidth] at hbyte hbit ⊢
        omega⟩)
      ⟨flat % tableWidth, Nat.mod_lt _ (by norm_num [tableWidth])⟩

def packCiphertexts (ciphertexts : Vector WordBytes 4) : PackedPair :=
  Codec.packFour254 ciphertexts

private theorem packCiphertexts_eq_spec
    (ciphertexts : Vector WordBytes 4) :
    packCiphertexts ciphertexts =
      PackedBits.encode (flattenedCiphertexts ciphertexts) := by
  apply Vector.ext
  intro byte hbyte
  rw [← UInt8.toBitVec_inj]
  apply BitVec.eq_of_getElem_eq
  intro bit hbit
  simp only [← BitVec.getLsbD_eq_getElem hbit]
  let byteIndex : Fin 127 := ⟨byte, hbyte⟩
  let bitIndex : Fin 8 := ⟨bit, hbit⟩
  unfold packCiphertexts PackedBits.encode
  simp only [Bytes.ofFn, Vector.getElem_ofFn]
  change
    ((Codec.packFour254 ciphertexts).get byteIndex).toBitVec.getLsbD
        bitIndex.val =
      (PackedBits.encodeByte _).toBitVec.getLsbD bitIndex.val
  rw [Codec.packFour254_getLsbD]
  rw [PackedBits.encodeByte_getLsbD]
  unfold flattenedCiphertexts lowBit
  rfl

def unpackCiphertext (packed : PackedPair)
    (slot : Fin 4) (position : Fin tableWidth) : Bool :=
  let flat := slot.val * tableWidth + position.val
  PackedBits.decode packed
    ⟨flat / 8, by
      have hslot := slot.isLt
      have hposition := position.isLt
      norm_num [flat, pairByteCount, tableWidth] at hslot hposition ⊢
      omega⟩
    ⟨flat % 8, Nat.mod_lt _ (by omega)⟩

@[simp] theorem unpackCiphertext_pack
    (ciphertexts : Vector WordBytes 4)
    (slot : Fin 4) (position : Fin tableWidth) :
    unpackCiphertext (packCiphertexts ciphertexts) slot position =
      lowBit ciphertexts[slot.val] position := by
  unfold unpackCiphertext
  rw [packCiphertexts_eq_spec]
  rw [PackedBits.decode_encode]
  unfold flattenedCiphertexts
  dsimp only
  let flat := slot.val * tableWidth + position.val
  have hdecompose := Nat.mod_add_div flat 8
  have hflat : 8 * (flat / 8) + flat % 8 = flat := by omega
  change lowBit
      (ciphertexts.get
        ⟨(8 * (flat / 8) + flat % 8) / tableWidth, _⟩)
      ⟨(8 * (flat / 8) + flat % 8) % tableWidth, _⟩ =
    lowBit (ciphertexts.get slot) position
  simp only [hflat]
  have hslotEq :
      (⟨flat / tableWidth, by
        have hslot := slot.isLt
        have hposition := position.isLt
        dsimp [flat]
        norm_num [tableWidth] at hslot hposition ⊢
        omega⟩ : Fin 4) = slot := by
    apply Fin.ext
    have hslot := slot.isLt
    have hposition := position.isLt
    dsimp [flat]
    norm_num [tableWidth] at hslot hposition ⊢
    omega
  have hpositionEq :
      (⟨flat % tableWidth, Nat.mod_lt _ (by norm_num [tableWidth])⟩ :
        Fin tableWidth) = position := by
    apply Fin.ext
    have hposition := position.isLt
    dsimp [flat]
    norm_num [tableWidth] at hposition ⊢
    omega
  rw [hslotEq, hpositionEq]

private def packedByteNat (packed : PackedPair) (index : Nat) : Nat :=
  if h : index < pairByteCount then packed.get ⟨index, h⟩ |>.toNat else 0

private theorem packedByteNat_testBit (packed : PackedPair)
    (index : Fin pairByteCount) (bit : Fin 8) :
    (packedByteNat packed index.val).testBit bit.val =
      PackedBits.decode packed index bit := by
  simp [packedByteNat, PackedBits.decode, Vector.get_eq_getElem,
    BitVec.getElem_eq_testBit_toNat]

private theorem packedByteNat_testBit_high (packed : PackedPair)
    (index bit : Nat) (hbit : 8 ≤ bit) :
    (packedByteNat packed index).testBit bit = false := by
  unfold packedByteNat
  split
  · apply Nat.testBit_lt_two_pow
    exact (UInt8.toNat_lt _).trans_le
      (Nat.pow_le_pow_right (by decide) hbit)
  · simp

/-- Extract one packed 254-bit ciphertext eight bits at a time.  Evaluation
uses this byte-oriented view instead of repeating quotient/remainder arithmetic
for all 254 individual bit reads. -/
def unpackCiphertextBytes (packed : PackedPair) (slot : Fin 4) : WordBytes :=
  Bytes.ofFn fun byte =>
    let flat := slot.val * tableWidth + 8 * byte.val
    let shift := flat % 8
    let first := packedByteNat packed (flat / 8)
    let second := packedByteNat packed (flat / 8 + 1)
    UInt8.ofNat ((first >>> shift) ||| (second <<< (8 - shift)))

theorem lowBit_unpackCiphertextBytes (packed : PackedPair) (slot : Fin 4)
    (position : Fin tableWidth) :
    lowBit (unpackCiphertextBytes packed slot) position =
      unpackCiphertext packed slot position := by
  unfold lowBit Codec.byteBitsLE unpackCiphertext unpackCiphertextBytes Bytes.ofFn
  simp only [Vector.get_eq_getElem, Vector.getElem_ofFn,
    UInt8.toBitVec_ofNat', BitVec.getLsbD_ofNat]
  have hposition := position.isLt
  have hslot := slot.isLt
  have hbit : position.val % 8 < 8 := Nat.mod_lt _ (by omega)
  simp only [hbit, decide_true, Bool.true_and]
  simp only [Nat.testBit_or, Nat.testBit_shiftRight, Nat.testBit_shiftLeft]
  let flat := slot.val * tableWidth + position.val
  let byteFlat := slot.val * tableWidth + 8 * (position.val / 8)
  have hpositionDecompose : 8 * (position.val / 8) + position.val % 8 =
      position.val := by omega
  have hflatEq : flat = byteFlat + position.val % 8 := by
    dsimp [flat, byteFlat]
    omega
  have hbyteDecompose :
      8 * (byteFlat / 8) + byteFlat % 8 = byteFlat := by
    have := Nat.mod_add_div byteFlat 8
    omega
  have hflatDecompose : 8 * (flat / 8) + flat % 8 = flat := by
    have := Nat.mod_add_div flat 8
    omega
  have hbyteRemainder : byteFlat % 8 < 8 := Nat.mod_lt _ (by omega)
  have hflatRemainder : flat % 8 < 8 := Nat.mod_lt _ (by omega)
  have hpositionRemainder : position.val % 8 < 8 := Nat.mod_lt _ (by omega)
  have hflatBound : flat < 4 * tableWidth := by
    dsimp [flat]
    norm_num [tableWidth] at hslot hposition ⊢
    omega
  by_cases hfirst : position.val % 8 < 8 - byteFlat % 8
  · have hshift : byteFlat % 8 + position.val % 8 < 8 := by omega
    have hbyteIndex : byteFlat / 8 < pairByteCount := by
      dsimp [byteFlat]
      norm_num [pairByteCount, tableWidth] at hslot hposition ⊢
      omega
    rw [show decide (position.val % 8 ≥ 8 - byteFlat % 8) = false by
      simp only [decide_eq_false_iff_not]
      omega]
    simp only [Bool.false_and, Bool.or_false]
    rw [packedByteNat_testBit packed
      ⟨byteFlat / 8, hbyteIndex⟩
      ⟨byteFlat % 8 + position.val % 8, hshift⟩]
    congr 2 <;> omega
  · have hcross : 8 - byteFlat % 8 ≤ position.val % 8 := by omega
    have hfirstHigh : 8 ≤ byteFlat % 8 + position.val % 8 := by omega
    rw [packedByteNat_testBit_high packed (byteFlat / 8)
      (byteFlat % 8 + position.val % 8) hfirstHigh]
    rw [show decide (position.val % 8 ≥ 8 - byteFlat % 8) = true by
      simp only [decide_eq_true_eq]
      omega]
    simp only [Bool.true_and, Bool.false_or]
    have hsecondBit : position.val % 8 - (8 - byteFlat % 8) < 8 := by omega
    have hsecondIndex : byteFlat / 8 + 1 < pairByteCount := by
      norm_num [pairByteCount, tableWidth] at hflatBound ⊢
      omega
    rw [packedByteNat_testBit packed
      ⟨byteFlat / 8 + 1, hsecondIndex⟩
      ⟨position.val % 8 - (8 - byteFlat % 8), hsecondBit⟩]
    congr 2 <;> omega

/-- Clear the two unused most-significant bits after opening a packed field
word.  Pads are full 256-bit strings, so this canonicalization must happen
after XOR rather than while extracting the ciphertext. -/
def clearHighBits (bytes : WordBytes) : WordBytes :=
  Bytes.ofFn fun byte =>
    if byte.val = 31 then UInt8.ofNat ((bytes.get byte).toNat % 64)
    else bytes.get byte

def openedPackedBytes (packed : PackedPair) (slot : Fin 4)
    (pad : WordBytes) : WordBytes :=
  clearHighBits (Bytes.xor (unpackCiphertextBytes packed slot) pad)

theorem decode_clearHighBits (bytes : WordBytes) (byte : Fin 32) (bit : Fin 8) :
    PackedBits.decode (clearHighBits bytes) byte bit =
      if 8 * byte.val + bit.val < tableWidth then
        PackedBits.decode bytes byte bit
      else false := by
  unfold PackedBits.decode clearHighBits Bytes.ofFn
  simp only [Vector.get_eq_getElem, Vector.getElem_ofFn]
  split
  · rename_i hlast
    have hbyte : byte.val = 31 := hlast
    simp only [UInt8.toBitVec_ofNat', BitVec.getLsbD_ofNat,
      bit.isLt, decide_true, Bool.true_and]
    rw [show 64 = 2 ^ 6 by norm_num, Nat.testBit_mod_two_pow]
    have hbit := bit.isLt
    by_cases hlow : bit.val < 6
    · rw [if_pos (by norm_num [tableWidth, hbyte]; omega)]
      simp only [hlow, decide_true, Bool.true_and]
      rw [BitVec.getLsbD_eq_getElem bit.isLt,
        BitVec.getElem_eq_testBit_toNat, UInt8.toNat_toBitVec]
    · rw [if_neg (by norm_num [tableWidth, hbyte]; omega)]
      simp only [hlow, decide_false, Bool.false_and]
  · rename_i hnotLast
    have hbyte := byte.isLt
    rw [if_pos (by norm_num [tableWidth] at hbyte ⊢; omega)]

private theorem decode_eq_lowBit (bytes : WordBytes)
    (byte : Fin 32) (bit : Fin 8)
    (hlow : 8 * byte.val + bit.val < tableWidth) :
    PackedBits.decode bytes byte bit =
      lowBit bytes ⟨8 * byte.val + bit.val, hlow⟩ := by
  unfold PackedBits.decode lowBit Codec.byteBitsLE
  simp only [Vector.get_eq_getElem]
  have hdiv : (8 * byte.val + bit.val) / 8 = byte.val := by
    have hbit := bit.isLt
    omega
  have hmod : (8 * byte.val + bit.val) % 8 = bit.val := by
    have hbit := bit.isLt
    omega
  simp only [hdiv, hmod]

theorem openedPackedBytes_eq (packed : PackedPair) (slot : Fin 4)
    (pad : WordBytes) :
    openedPackedBytes packed slot pad =
      openedBytes (unpackCiphertext packed slot) pad := by
  have hdecode :
      PackedBits.decode (openedPackedBytes packed slot pad) =
        PackedBits.decode (openedBytes (unpackCiphertext packed slot) pad) := by
    funext byte bit
    unfold openedPackedBytes
    rw [decode_clearHighBits]
    unfold openedBytes
    rw [PackedBits.decode_encode]
    split
    · rename_i hlow
      rw [decode_eq_lowBit _ _ _ hlow, lowBit_xor,
        lowBit_unpackCiphertextBytes, ← decode_eq_lowBit pad byte bit hlow]
    · rfl
  calc
    openedPackedBytes packed slot pad =
        PackedBits.encode (PackedBits.decode
          (openedPackedBytes packed slot pad)) :=
      (PackedBits.encode_decode _).symm
    _ = PackedBits.encode (PackedBits.decode
          (openedBytes (unpackCiphertext packed slot) pad)) :=
      congrArg PackedBits.encode hdecode
    _ = openedBytes (unpackCiphertext packed slot) pad :=
      PackedBits.encode_decode _

def openPackedCiphertext (packed : PackedPair) (slot : Fin 4)
    (pad : WordBytes) : Option Word :=
  decodeWord (openedPackedBytes packed slot pad)

@[simp] theorem openPackedCiphertext_eq (packed : PackedPair) (slot : Fin 4)
    (pad : WordBytes) :
    openPackedCiphertext packed slot pad =
      openCiphertext (unpackCiphertext packed slot) pad := by
  unfold openPackedCiphertext openCiphertext
  rw [openedPackedBytes_eq]

def slotRow (pair : Fin pairCount) (slot : Fin 4) : Fin tableWidth :=
  ⟨2 * pair.val + slot.val / 2, by
    have hpair := pair.isLt
    have hslot := slot.isLt
    norm_num [pairCount, tableWidth] at hpair hslot ⊢
    omega⟩

def slotSelected (slot : Fin 4) : Bool :=
  (slot.val % 2 = 1)

def rowPair (row : Fin tableWidth) : Fin pairCount :=
  ⟨row.val / 2, by
    have hrow := row.isLt
    norm_num [pairCount, tableWidth] at hrow ⊢
    omega⟩

def rowSlot (row : Fin tableWidth) (selected : Bool) : Fin 4 :=
  ⟨2 * (row.val % 2) + if selected then 1 else 0, by
    have hmod : row.val % 2 < 2 := Nat.mod_lt _ (by omega)
    cases selected <;> norm_num <;> omega⟩

@[simp] theorem slotRow_rowPair_rowSlot
    (row : Fin tableWidth) (selected : Bool) :
    slotRow (rowPair row) (rowSlot row selected) = row := by
  apply Fin.ext
  unfold slotRow rowPair rowSlot
  dsimp only
  have hdecompose := Nat.mod_add_div row.val 2
  have hmod : row.val % 2 < 2 := Nat.mod_lt _ (by omega)
  interval_cases hparity : row.val % 2 <;>
    cases selected <;> norm_num at * <;> omega

@[simp] theorem slotSelected_rowSlot
    (row : Fin tableWidth) (selected : Bool) :
    slotSelected (rowSlot row selected) = selected := by
  have hmod : row.val % 2 < 2 := Nat.mod_lt _ (by omega)
  interval_cases hparity : row.val % 2 <;>
    cases selected <;> simp [slotSelected, rowSlot, hparity]

@[ext] structure Table where
  pairs : Fin pairCount → PackedPair

def ciphertextForSlot (purpose : Purpose)
    (pairs : Fin tableWidth → Bool → Label)
    (params : Params) (masks : MaskFiber params.constant)
    (pair : Fin pairCount) (slot : Fin 4) : WordBytes :=
  let row := slotRow pair slot
  let selected := slotSelected slot
  Bytes.xor (encodeWord (share params (masks.1 row) row selected))
    (pairs row selected purpose)

/-- Materialize the four encrypted words in a row pair before packing its bits.
This ensures each payload and pad is computed once, rather than once per
emitted ciphertext bit. -/
def materializeCiphertexts
    (ciphertexts : Fin 4 → WordBytes) : Vector WordBytes 4 :=
  Vector.ofFn ciphertexts

@[simp] theorem materializeCiphertexts_get
    (ciphertexts : Fin 4 → WordBytes) (slot : Fin 4) :
    (materializeCiphertexts ciphertexts)[slot.val] = ciphertexts slot := by
  simp [materializeCiphertexts, Vector.ofFn]

def garble (purpose : Purpose)
    (pairs : Fin tableWidth → Bool → Label)
    (params : Params) (masks : MaskFiber params.constant) : Table where
  pairs := fun pair =>
    packCiphertexts (materializeCiphertexts
      (ciphertextForSlot purpose pairs params masks pair))

def tableCiphertext (table : Table)
    (row : Fin tableWidth) (selected : Bool) : Ciphertext :=
  unpackCiphertext (table.pairs (rowPair row)) (rowSlot row selected)

@[simp] theorem tableCiphertext_garble (purpose : Purpose)
    (pairs : Fin tableWidth → Bool → Label)
    (params : Params) (masks : MaskFiber params.constant)
    (row : Fin tableWidth) (selected : Bool) :
    tableCiphertext (garble purpose pairs params masks) row selected =
      encrypt (encodeWord (share params (masks.1 row) row selected))
        (pairs row selected purpose) := by
  funext position
  unfold tableCiphertext garble
  rw [unpackCiphertext_pack]
  rw [materializeCiphertexts_get]
  unfold ciphertextForSlot encrypt
  simp

def openShare (purpose : Purpose) (table : Table)
    (bits : Fin tableWidth → Bool)
    (labels : Fin tableWidth → Label)
    (index : Fin tableWidth) : Option Word :=
  openPackedCiphertext (table.pairs (rowPair index))
    (rowSlot index (bits index)) (labels index purpose)

def evaluateList (purpose : Purpose) (table : Table)
    (bits : Fin tableWidth → Bool)
    (labels : Fin tableWidth → Label) :
    List (Fin tableWidth) → Option Word
  | [] => some 0
  | index :: tail => do
      let value ← openShare purpose table bits labels index
      let rest ← evaluateList purpose table bits labels tail
      pure (value + rest)

def evaluate (purpose : Purpose) (table : Table)
    (bits : Fin tableWidth → Bool)
    (labels : Fin tableWidth → Label) : Option Word :=
  evaluateList purpose table bits labels (List.finRange tableWidth)

theorem openShare_garble (purpose : Purpose)
    (pairs : Fin tableWidth → Bool → Label)
    (params : Params) (masks : MaskFiber params.constant)
    (bits : Fin tableWidth → Bool) (index : Fin tableWidth) :
    openShare purpose (garble purpose pairs params masks) bits
        (fun i => pairs i (bits i)) index =
      some (share params (masks.1 index) index (bits index)) := by
  unfold openShare
  rw [openPackedCiphertext_eq]
  change openCiphertext
      (tableCiphertext (garble purpose pairs params masks) index (bits index))
      (pairs index (bits index) purpose) = _
  simp

private theorem evaluateList_garble (purpose : Purpose)
    (pairs : Fin tableWidth → Bool → Label)
    (params : Params) (masks : MaskFiber params.constant)
    (bits : Fin tableWidth → Bool)
    (indices : List (Fin tableWidth)) :
    evaluateList purpose (garble purpose pairs params masks) bits
        (fun i => pairs i (bits i)) indices =
      some (indices.foldr
        (fun index rest => share params (masks.1 index) index (bits index) + rest)
        0) := by
  induction indices with
  | nil => rfl
  | cons index tail ih =>
      rw [evaluateList, openShare_garble, ih]
      rfl

def decodeBits (bits : Fin tableWidth → Bool) : Word :=
  ∑ index, weight index * bitWord (bits index)

private theorem natCast_ofBits_eq_sum (bits : Fin width → Bool) :
    ((Nat.ofBits bits : Nat) : Word) =
      ∑ index : Fin width,
        (2 : Word) ^ index.val * bitWord (bits index) := by
  induction width with
  | zero => simp
  | succ width ih =>
      rw [Nat.ofBits_succ, Nat.cast_add, Nat.cast_mul, ih]
      rw [Fin.sum_univ_succ]
      simp only [Fin.val_zero, pow_zero, one_mul, Function.comp_apply,
        Fin.val_succ, pow_succ']
      have hbit : ((bits 0).toNat : Word) = bitWord (bits 0) := by
        cases bits 0 <;> rfl
      rw [hbit]
      norm_num only [Nat.cast_ofNat]
      rw [add_comm (2 * ∑ index : Fin width,
        2 ^ index.val * bitWord (bits index.succ))]
      apply congrArg (bitWord (bits 0) + ·)
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro index _
      ring

theorem decodeBits_eq_natCast (bits : Fin tableWidth → Bool) :
    decodeBits bits = (Nat.ofBits bits : Word) := by
  unfold decodeBits
  simp_rw [weight_eq_pow]
  exact (natCast_ofBits_eq_sum bits).symm

theorem decodeBits_testBit (value : Nat) (hvalue : value < 2 ^ tableWidth) :
    decodeBits (fun index : Fin tableWidth => value.testBit index.val) =
      (value : Word) := by
  rw [decodeBits_eq_natCast, Nat.ofBits_testBit, Nat.mod_eq_of_lt hvalue]

private theorem foldr_finRange_eq_sum {width : Nat} (values : Fin width → Word) :
    (List.finRange width).foldr (fun index rest => values index + rest) 0 =
      ∑ index, values index := by
  induction width with
  | zero => simp
  | succ width ih =>
      rw [List.finRange_succ, List.foldr_cons, List.foldr_map,
        Fin.sum_univ_succ]
      exact congrArg (values 0 + ·) (ih (values := fun index => values index.succ))

theorem evaluate_garble (purpose : Purpose)
    (pairs : Fin tableWidth → Bool → Label)
    (params : Params) (masks : MaskFiber params.constant)
    (bits : Fin tableWidth → Bool) :
    evaluate purpose (garble purpose pairs params masks) bits
        (fun i => pairs i (bits i)) =
      some (params.coefficient * decodeBits bits + params.constant) := by
  rw [evaluate, evaluateList_garble]
  apply congrArg some
  rw [foldr_finRange_eq_sum]
  rw [show (∑ index, share params (masks.1 index) index (bits index)) =
      (∑ index, (weight index * params.coefficient * bitWord (bits index) +
        masks.1 index)) by
    apply Finset.sum_congr rfl
    intro index _
    exact share_eq_weight params (masks.1 index) index (bits index)]
  unfold decodeBits
  rw [Finset.sum_add_distrib, masks.2, Finset.mul_sum]
  apply congrArg (· + params.constant)
  apply Finset.sum_congr rfl
  intro index _
  ring

private def pairCodec : FixedCodec PackedPair pairByteCount where
  encode := id
  decode := .ok
  decode_encode := by intro; rfl
  encode_decode := by
    intro bytes value h
    change value = bytes
    exact (Except.ok.inj h).symm

def Table.encode (table : Table) : ByteArray :=
  FixedCodec.encodeFin pairCodec pairCount table.pairs

def Table.decode (input : ByteArray) : Except WireDecodeError Table := do
  let pairs ← FixedCodec.decodeFin pairCodec pairCount input
  pure ⟨pairs⟩

@[simp] theorem Table.encode_size (table : Table) :
    table.encode.size = tableByteCount := by
  rw [Table.encode, FixedCodec.encodeFin_size]
  rfl

@[simp] theorem Table.decode_encode (table : Table) :
    Table.decode table.encode = .ok table := by
  unfold Table.decode Table.encode
  rw [FixedCodec.decodeFin_encode]
  rfl

theorem Table.encode_decode {bytes : ByteArray} {table : Table}
    (h : Table.decode bytes = .ok table) : table.encode = bytes := by
  unfold Table.decode at h
  cases hpairs : FixedCodec.decodeFin pairCodec pairCount bytes with
  | error error => simp [hpairs, Except.bind, bind] at h
  | ok pairs =>
      have htable : ({ pairs := pairs } : Table) = table := by
        simp only [hpairs, Except.bind, bind] at h
        change Except.ok ({ pairs := pairs } : Table) = Except.ok table at h
        exact Except.ok.inj h
      rw [← htable]
      exact FixedCodec.encodeFin_decode pairCodec hpairs

end GarblingPrize.Submission.IdealAffineTable
