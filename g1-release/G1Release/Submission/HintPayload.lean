import G1Release.Submission.AffineTable
import G1Release.Submission.PackedBits

namespace G1Release.Submission.HintPayload
open G1Release.Math
open scoped BigOperators
abbrev Word := AffineTable.Word
abbrev WordBytes := Bytes 32
abbrev tableWidth : Nat := 254
abbrev Ciphertext := Fin tableWidth → Bool
abbrev Params := AffineTable.Params
abbrev encodeWord := AffineTable.encodeWord
abbrev decodeWord := AffineTable.decodeWord
@[simp] theorem decodeWord_encodeWord (value : Word) :
    decodeWord (encodeWord value) = some value := AffineTable.decodeWord_encodeWord value

def lowBit (bytes : WordBytes) (index : Fin tableWidth) : Bool :=
  HintCodec.byteBitsLE bytes ⟨index.val, by
    exact index.isLt.trans (by decide : (254 : Nat) < 8 * 32)⟩

@[simp] theorem lowBit_xor (left right : WordBytes)
    (index : Fin tableWidth) :
    lowBit (Bytes.xor left right) index =
      Bool.xor (lowBit left index) (lowBit right index) := by
  unfold lowBit HintCodec.byteBitsLE Bytes.xor Bytes.ofFn
  simp only [Vector.getElem_ofFn, Vector.get_eq_getElem,
    UInt8.toBitVec_xor, BitVec.getLsbD_xor]

def encrypt (payload pad : WordBytes) : Ciphertext :=
  fun index => Bool.xor (lowBit payload index) (lowBit pad index)

/-- Read only the requested bit; constructing an entire XOR vector for each
bit would repeat 32 byte operations 254 times per ciphertext. -/
theorem encrypt_eq (payload pad : WordBytes) :
    encrypt payload pad = fun index => lowBit (Bytes.xor payload pad) index := by
  funext index
  exact (lowBit_xor payload pad index).symm

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
    HintCodec.byteBitsLE (HintCodec.natLE width value) index =
      value.testBit index.val := by
  unfold HintCodec.byteBitsLE HintCodec.natLE BytePacking.encode
  simp only [Vector.get_eq_getElem, Vector.getElem_ofFn,
    UInt8.toBitVec_ofNat', BitVec.getLsbD_ofNat]
  have hmod : index.val % 8 < 8 := Nat.mod_lt _ (by omega)
  have hdecompose := Nat.mod_add_div index.val 8
  simp only [hmod, decide_true, Bool.true_and]
  rw [Nat.testBit_shiftRight]
  congr 1
  omega

private theorem encodeWord_high_bit_false (value : Word)
    (index : Fin (8 * 32)) (hindex : tableWidth ≤ index.val) :
    HintCodec.byteBitsLE (encodeWord value) index = false := by
  unfold encodeWord AffineTable.encodeWord
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
    unfold lowBit HintCodec.byteBitsLE
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
    unfold HintCodec.byteBitsLE at hfalse
    simpa only [hdiv, hmod, Vector.get_eq_getElem] using hfalse.symm

@[simp] theorem openCiphertext_encrypt (value : Word) (pad : WordBytes) :
    openCiphertext (encrypt (encodeWord value) pad) pad = some value := by
  simp [openCiphertext]


def bitWord (bit : Bool) : Word := if bit then 1 else 0
def weight (index : Fin tableWidth) : Word := (2 : Word) ^ index.val
def share (params : Params) (mask : Word) (index : Fin tableWidth) (bit : Bool) : Word :=
  if bit then ((2^index.val : Nat) : Word) * params.coefficient + mask else mask
theorem weight_eq_pow (index : Fin tableWidth) : weight index = (2 : Word)^index.val := rfl
theorem share_eq_weight (params : Params) (mask : Word) (index : Fin tableWidth) (bit : Bool) :
    share params mask index bit = weight index * params.coefficient * bitWord bit + mask := by
  cases bit <;> simp [share, weight, bitWord]
def decodeBits (bits : Fin tableWidth → Bool) : Word := ∑ i, weight i * bitWord (bits i)
end G1Release.Submission.HintPayload
