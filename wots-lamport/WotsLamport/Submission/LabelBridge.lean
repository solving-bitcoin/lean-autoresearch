import WotsLamport.Submission.ByteBridge
import Mathlib.Tactic.IntervalCases

namespace WotsLamport.Submission
open SecretRelease WotsLamport.Protected

theorem concatenate_append (a b : List ByteArray) :
    concatenate (a ++ b) = concatenate a ++ concatenate b := by
  induction a with
  | nil => simp [concatenate]
  | cons x xs ih => simp only [List.cons_append, concatenate_cons, ih, ByteArray.append_assoc]

theorem concatenate_extract_blocks (bytes : ByteArray) (width count : Nat) :
    concatenate ((List.range count).map fun i => bytes.extract (i*width) ((i+1)*width)) =
      bytes.extract 0 (count*width) := by
  induction count with
  | zero => simp [concatenate]
  | succ count ih =>
    rw [List.range_succ, List.map_append, concatenate_append, ih]
    simp only [List.map_singleton, concatenate_cons, concatenate, List.foldl_nil,
      ByteArray.append_empty]
    exact (ByteArray.extract_eq_extract_append_extract (count*width) (by omega)
      (Nat.mul_le_mul_right width (Nat.le_succ count))).symm

theorem write_readLE_two (bytes : ByteArray) (start : Nat) (fits : start+2 ≤ bytes.size) :
    writeLE 2 (readLE bytes start 2) = bytes.extract start (start+2) := by
  have hs : (bytes.extract start (start+2)).size = 2 := by
    rw [ByteArray.size_extract]
    omega
  apply ByteArray.ext_getElem (by simp [hs])
  intro j hj hj'
  have hj2 : j < 2 := by simpa using hj
  rw [← getElem!_pos (writeLE 2 (readLE bytes start 2)) j hj,
    writeLE_get _ _ j hj2, ByteArray.getElem_extract,
    ← getElem!_pos bytes (start+j) (by omega)]
  apply UInt8.toNat_inj.mp
  have h0 : bytes[start]!.toNat < 256 := UInt8.toNat_lt_size _
  have h1 : bytes[start+1]!.toNat < 256 := UInt8.toNat_lt_size _
  interval_cases j <;>
    simp [readLE, List.range_succ, UInt8.toNat_ofNat'] <;> omega

/-- Sixteen little-endian two-byte limbs reconstruct every original label
byte; no hash assumption or probabilistic statement is needed. -/
theorem serialize_label_limbs (label : Label) :
    concatenate ((List.range 16).map fun limb =>
      writeLE 2 (readLE (ByteArray.mk label.toArray) (2*limb) 2)) =
      ByteArray.mk label.toArray := by
  have hm : (List.range 16).map (fun limb =>
      writeLE 2 (readLE (ByteArray.mk label.toArray) (2*limb) 2)) =
      (List.range 16).map (fun limb =>
        (ByteArray.mk label.toArray).extract (limb*2) ((limb+1)*2)) := by
    apply List.map_congr_left
    intro limb hl
    have hlimb := List.mem_range.mp hl
    have hs : (ByteArray.mk label.toArray).size = 32 := label.size_toArray
    rw [write_readLE_two _ _ (by rw [hs]; omega)]
    congr 1 <;> omega
  rw [hm, concatenate_extract_blocks]
  have hs : (ByteArray.mk label.toArray).size = 16*2 := label.size_toArray
  rw [← hs, ByteArray.extract_zero_size]

theorem polynomial_eval_zero (coins : ByteArray) (label : Label) (wire limb : Nat)
    (value : Bool) : evaluatePolynomial (polynomial coins label wire limb value) 0 =
      readLE (ByteArray.mk label.toArray) (2*limb) 2 := by
  have ht : threshold value = (threshold value-1)+1 := by cases value <;> decide
  have hs : readLE (ByteArray.mk label.toArray) (2*limb) 2 < prime :=
    lt_trans (readLE_two_lt _ _) (by decide)
  unfold polynomial evaluatePolynomial
  rw [ht, List.range_succ_eq_map, List.map_cons, List.foldr_cons]
  simp [fadd, fmul, Nat.mod_eq_of_lt hs]

theorem byteVector_encode_raw {n : Nat} (bytes : Bytes n) :
    (Codec.byteVector n).bytes.encode bytes = ByteArray.mk bytes.toArray := by
  apply ByteArray.ext_getElem (by
    rw [codecBytes_size, vectorBytes_size]
    change (n*8+7)/8 = n
    omega)
  intro i hi hi'
  have hin : i < n := by simpa only [vectorBytes_size] using hi'
  change (packBits (Vector.ofFn (fun j : Fin (n*8) =>
    bytes[j.val/8].toNat.testBit (j.val%8))))[i] = bytes[i]'hin
  simp only [packBits, ByteArray.getElem_eq_getElem_data,
    Vector.toArray_ofFn, Array.getElem_ofFn, Vector.getElem_ofFn]
  have he : (fun j : Fin 8 => if h : 8*i+j.val < n*8 then
      bytes[(8*i+j.val)/8].toNat.testBit ((8*i+j.val)%8) else false) =
      (fun j : Fin 8 => bytes[i].toNat.testBit j.val) := by
    funext j
    have hj := j.isLt
    simp [show 8*i+j.val < n*8 by omega,
      show (8*i+j.val)/8 = i by omega, show (8*i+j.val)%8 = j.val by omega]
  rw [he, Nat.ofBits_testBit,
    Nat.mod_eq_of_lt (show bytes[i].toNat < 2^8 from bytes[i].toFin.isLt)]
  simp

theorem byteVector_decode_raw {n : Nat} (bytes : Bytes n) :
    (Codec.byteVector n).bytes.decode (ByteArray.mk bytes.toArray) = some bytes := by
  rw [← byteVector_encode_raw bytes]
  exact (Codec.byteVector n).bytes.decode_encode bytes

end WotsLamport.Submission
