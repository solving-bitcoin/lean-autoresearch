import G1Release.Submission.BytePacking
import G1Release.Submission.FastRead
import GarblingPrize.Protected.Bytes
import G1Release.Protected.Codecs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset

open scoped BigOperators

namespace G1Release.Submission.AffineTable

open GarblingPrize.Protected
open G1Release.Protected

set_option maxHeartbeats 800000
set_option maxRecDepth 4096

abbrev Word := BN254.Fq
abbrev WordBytes := GarblingPrize.Protected.Bytes 32
abbrev Hash := SecretRelease.Hash
abbrev Label := SecretRelease.Label

def tableWidth : Nat := 254
def rowByteCount : Nat := 64
def tableByteCount : Nat := 16256

structure Params where
  coefficient : Word
  constant : Word

def bitWord (bit : Bool) : Word := if bit then 1 else 0

def weight (index : Fin 254) : Word := (2 : Word) ^ index.val

def share (params : Params) (mask : Word) (index : Fin 254) (bit : Bool) : Word :=
  weight index * params.coefficient * bitWord bit + mask

def MaskFiber (constant : Word) :=
  {masks : Fin 254 → Word // ∑ i, masks i = constant}

def canonicalMasks (constant : Word) : MaskFiber constant :=
  ⟨fun index => if index.val = 0 then constant else 0, by
    simp [Fin.sum_univ_succ]⟩

instance (constant : Word) : Nonempty (MaskFiber constant) :=
  ⟨canonicalMasks constant⟩

private theorem fq_lt_two_pow_256 (value : Word) : value.val < 2 ^ 256 :=
  lt_trans value.val_lt (by norm_num [baseFieldModulus])

/-- Canonical little-endian field bytes, processed one byte per step. -/
def encodeWord (value : Word) : WordBytes := BytePacking.encode 32 value.val

def decodeWord (bytes : WordBytes) : Option Word :=
  let n := FastRead.read (n := 4) bytes
  if n < baseFieldModulus then some (n : Word) else none

theorem decodeWord_encodeWord (value : Word) :
    decodeWord (encodeWord value) = some value := by
  unfold decodeWord encodeWord
  rw [FastRead.read_eq, BytePacking.read_encode, Nat.mod_eq_of_lt (fq_lt_two_pow_256 value)]
  simp only [value.val_lt, ↓reduceIte, ZMod.natCast_zmod_val]

def xorBytes (left right : WordBytes) : WordBytes := Bytes.xor left right

@[simp] theorem xorBytes_cancel (left right : WordBytes) :
    xorBytes (xorBytes left right) right = left :=
  Bytes.xor_cancel_right left right

def natLE8 (n : Nat) : Array UInt8 :=
  Array.ofFn fun i : Fin 8 => UInt8.ofNat (n >>> (8 * i.val))

def pad (hash : Hash) (label : Label) (purpose row : Nat) : WordBytes :=
  hash (ByteArray.mk (label.toArray ++ natLE8 purpose ++ natLE8 row))

def encrypt (payload : Word) (padValue : WordBytes) : WordBytes :=
  xorBytes (encodeWord payload) padValue

def openWord (ciphertext padValue : WordBytes) : Option Word :=
  decodeWord (xorBytes ciphertext padValue)

@[simp] theorem openWord_encrypt (payload : Word) (padValue : WordBytes) :
    openWord (encrypt payload padValue) padValue = some payload := by
  unfold openWord encrypt
  rw [xorBytes_cancel, decodeWord_encodeWord]

abbrev Table := GarblingPrize.Protected.Bytes 16256

def ciphertextAt (hash : Hash) (purpose : Nat)
    (pairs : Fin 254 → Bool → Label)
    (params : Params) (masks : MaskFiber params.constant)
    (index : Fin 254) (bit : Bool) : WordBytes :=
  encrypt (share params (masks.1 index) index bit)
    (pad hash (pairs index bit) purpose index.val)

def garble (hash : Hash) (purpose : Nat)
    (pairs : Fin 254 → Bool → Label)
    (params : Params) (masks : MaskFiber params.constant) : Table :=
  Bytes.ofFn fun k =>
    let index : Fin 254 := ⟨k.val / 64, by omega⟩
    let bit : Bool := decide (32 ≤ k.val % 64)
    let j : Fin 32 := ⟨k.val % 32, Nat.mod_lt _ (by decide)⟩
    (ciphertextAt hash purpose pairs params masks index bit).get j

private theorem half_index_lt (index : Fin 254) (bit : Bool) (j : Fin 32) :
    index.val * 64 + (if bit then 32 else 0) + j.val < 16256 := by
  cases bit <;> simp <;> omega

def getHalf (table : Table) (index : Fin 254) (bit : Bool) : WordBytes :=
  Bytes.ofFn fun j =>
    table.get ⟨index.val * 64 + (if bit then 32 else 0) + j.val, half_index_lt index bit j⟩

theorem getHalf_garble (hash : Hash) (purpose : Nat)
    (pairs : Fin 254 → Bool → Label)
    (params : Params) (masks : MaskFiber params.constant)
    (index : Fin 254) (bit : Bool) :
    getHalf (garble hash purpose pairs params masks) index bit =
      ciphertextAt hash purpose pairs params masks index bit := by
  apply Vector.ext
  intro j hj
  simp only [getHalf, garble, Bytes.ofFn, Vector.getElem_ofFn]
  cases bit with
  | false =>
      have hdiv : (index.val * 64 + j) / 64 = index.val := by omega
      have hmod32 : (index.val * 64 + j) % 32 = j := by omega
      have hlt : (index.val * 64 + j) / 64 < 254 := by rw [hdiv]; exact index.isLt
      have hidx : (⟨(index.val * 64 + j) / 64, hlt⟩ : Fin 254) = index := Fin.ext hdiv
      have hj64 : j % 64 = j := Nat.mod_eq_of_lt (Nat.lt_trans hj (by decide))
      simp [hidx, hmod32, hj64, Nat.not_le_of_gt hj, Vector.get_eq_getElem]
  | true =>
      have hdiv : (index.val * 64 + 32 + j) / 64 = index.val := by omega
      have hmod32 : (index.val * 64 + 32 + j) % 32 = j := by omega
      have hlt : (index.val * 64 + 32 + j) / 64 < 254 := by rw [hdiv]; exact index.isLt
      have hidx : (⟨(index.val * 64 + 32 + j) / 64, hlt⟩ : Fin 254) = index := Fin.ext hdiv
      have hmod64 : (index.val * 64 + 32 + j) % 64 = 32 + j := by omega
      simp [hidx, hmod32, hmod64, Vector.get_eq_getElem]

def encode (table : Table) : ByteArray := Bytes.toByteArray table

def decode (bytes : ByteArray) : Option Table :=
  Bytes.ofByteArray? 16256 bytes

@[simp] theorem decode_encode (table : Table) :
    decode (encode table) = some table :=
  Bytes.ofByteArray?_toByteArray table

theorem encode_decode {bytes : ByteArray} {table : Table}
    (h : decode bytes = some table) : encode table = bytes :=
  (Bytes.ofByteArray?_eq_some_iff.mp h).symm

@[simp] theorem encode_size (table : Table) : (encode table).size = 16256 :=
  Bytes.size_toByteArray table

theorem tableByteCount_eq : tableByteCount = 16256 := rfl

def openShare (hash : Hash) (purpose : Nat) (table : Table)
    (bits : Fin 254 → Bool) (labels : Fin 254 → Label) (index : Fin 254) :
    Option Word :=
  openWord (getHalf table index (bits index))
    (pad hash (labels index) purpose index.val)

def evaluateList (hash : Hash) (purpose : Nat) (table : Table)
    (bits : Fin 254 → Bool) (labels : Fin 254 → Label) :
    List (Fin 254) → Option Word
  | [] => some 0
  | index :: tail => do
      let value ← openShare hash purpose table bits labels index
      let rest ← evaluateList hash purpose table bits labels tail
      pure (value + rest)

def evaluate (hash : Hash) (purpose : Nat) (table : Table)
    (bits : Fin 254 → Bool) (labels : Fin 254 → Label) : Option Word :=
  evaluateList hash purpose table bits labels (List.finRange 254)

def decodeBits (bits : Fin 254 → Bool) : Word :=
  ∑ index, weight index * bitWord (bits index)

theorem share_eq_weight (params : Params) (mask : Word)
    (index : Fin 254) (bit : Bool) :
    share params mask index bit =
      weight index * params.coefficient * bitWord bit + mask := rfl

private theorem natCast_ofBits_eq_sum (bits : Fin width → Bool) :
    ((Nat.ofBits bits : Nat) : Word) =
      ∑ index : Fin width,
        (2 : Word) ^ index.val * bitWord (bits index) := by
  induction width with
  | zero => simp [bitWord]
  | succ width ih =>
      rw [Nat.ofBits_succ, Nat.cast_add, Nat.cast_mul, ih]
      rw [Fin.sum_univ_succ]
      simp only [Fin.val_zero, pow_zero, one_mul, Function.comp_apply,
        Fin.val_succ, pow_succ']
      have hbit : ((bits 0).toNat : Word) = bitWord (bits 0) := by
        cases bits 0 <;> rfl
      rw [hbit]
      rw [Finset.mul_sum]
      ring

theorem decodeBits_eq_natCast (bits : Fin 254 → Bool) :
    decodeBits bits = (Nat.ofBits bits : Word) := by
  unfold decodeBits weight
  exact (natCast_ofBits_eq_sum bits).symm

theorem decodeBits_testBit (value : Nat) (hvalue : value < 2 ^ 254) :
    decodeBits (fun index : Fin 254 => value.testBit index.val) =
      (value : Word) := by
  rw [decodeBits_eq_natCast, Nat.ofBits_testBit, Nat.mod_eq_of_lt hvalue]

private theorem foldr_finRange_eq_sum (values : Fin width → Word) :
    (List.finRange width).foldr (fun index rest => values index + rest) 0 =
      ∑ index, values index := by
  induction width with
  | zero => simp
  | succ width ih =>
      rw [List.finRange_succ, List.foldr_cons, List.foldr_map, Fin.sum_univ_succ]
      exact congrArg (values 0 + ·) (ih (fun index => values index.succ))

theorem openShare_garble (hash : Hash) (purpose : Nat)
    (pairs : Fin 254 → Bool → Label)
    (params : Params) (masks : MaskFiber params.constant)
    (bits : Fin 254 → Bool) (index : Fin 254) :
    openShare hash purpose (garble hash purpose pairs params masks) bits
        (fun i => pairs i (bits i)) index =
      some (share params (masks.1 index) index (bits index)) := by
  unfold openShare
  rw [getHalf_garble]
  exact openWord_encrypt _ _

theorem evaluateList_garble (hash : Hash) (purpose : Nat)
    (pairs : Fin 254 → Bool → Label)
    (params : Params) (masks : MaskFiber params.constant)
    (bits : Fin 254 → Bool) (indices : List (Fin 254)) :
    evaluateList hash purpose (garble hash purpose pairs params masks) bits
        (fun i => pairs i (bits i)) indices =
      some (indices.foldr
        (fun index rest => share params (masks.1 index) index (bits index) + rest)
        0) := by
  induction indices with
  | nil => rfl
  | cons index tail ih =>
      simp [evaluateList, openShare_garble, ih]

theorem evaluate_garble (hash : Hash) (purpose : Nat)
    (pairs : Fin 254 → Bool → Label)
    (params : Params) (masks : MaskFiber params.constant)
    (bits : Fin 254 → Bool) :
    evaluate hash purpose (garble hash purpose pairs params masks) bits
        (fun i => pairs i (bits i)) =
      some (params.coefficient * decodeBits bits + params.constant) := by
  rw [evaluate, evaluateList_garble, foldr_finRange_eq_sum]
  apply congrArg some
  simp only [share]
  rw [Finset.sum_add_distrib, masks.2]
  have hmul :
      (∑ index, weight index * params.coefficient * bitWord (bits index)) =
        params.coefficient * decodeBits bits := by
    unfold decodeBits
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro index _
    ring
  rw [hmul, add_comm]

end G1Release.Submission.AffineTable
