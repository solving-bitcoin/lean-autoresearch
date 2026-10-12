import WotsLamport.Submission.CoinBlocks
import WotsLamport.Submission.MaskLaw
import WotsLamport.Submission.DomainSeparation

namespace WotsLamport.Submission
open SecretRelease MeasureTheory ProbabilityTheory

/-- Keep all 64 sampled bytes in the proof sample space, including the
16-byte tail that the executable mask does not expose. -/
def fullMaskPad (answers : Fin 2 → Label) : Bytes 64 :=
  (byteBlocksEquiv 2).symm answers

def maskPrefix (bytes : Bytes 64) : Bytes 48 :=
  Vector.ofFn fun i => bytes[i.val]'(by have hi := i.isLt; omega)

def extendMaskPlaintext (bytes : Bytes 48) : Bytes 64 :=
  Vector.ofFn fun i => if hi : i.val < 48 then bytes[i.val] else 0

theorem maskPrefix_bytes (bytes : Bytes 64) :
    ByteArray.mk (maskPrefix bytes).toArray = (ByteArray.mk bytes.toArray).extract 0 48 := by
  apply ByteArray.ext_getElem (by simp only [vectorBytes_size, ByteArray.size_extract]; decide)
  intro j hj hj'
  rw [ByteArray.getElem_extract]
  simp only [maskPrefix, ByteArray.getElem_eq_getElem_data,
    Vector.getElem_toArray, Vector.getElem_ofFn, Nat.zero_add]

theorem maskPrefix_extend (bytes : Bytes 48) : maskPrefix (extendMaskPlaintext bytes) = bytes := by
  apply Vector.ext
  intro j hj
  simp only [maskPrefix, extendMaskPlaintext, Vector.getElem_ofFn, dif_pos hj]

theorem maskPrefix_xor (a b : Bytes 64) :
    maskPrefix (xorVector a b) = xorVector (maskPrefix a) (maskPrefix b) := by
  apply Vector.ext
  intro j hj
  simp only [maskPrefix, xorVector, Vector.getElem_ofFn]

/-- Exact correspondence with the executable's first answer plus 16 bytes
of its second answer, without dropping the remaining randomness from the law. -/
theorem fullMaskPad_prefix (answers : Fin 2 → Label) :
    ByteArray.mk (maskPrefix (fullMaskPad answers)).toArray =
      ByteArray.mk (answers 0).toArray ++ (ByteArray.mk (answers 1).toArray).extract 0 16 := by
  let bytes := fullMaskPad answers
  have block (i : Fin 2) : (byteBlocksEquiv 2 bytes) i = answers i := by
    exact congrFun ((byteBlocksEquiv 2).apply_symm_apply answers) i
  have left := byteBlocks_extract 2 bytes 0
  have right := byteBlocks_extract 2 bytes 1
  rw [block] at left right
  rw [maskPrefix_bytes, left, right, ByteArray.extract_extract]
  change (ByteArray.mk bytes.toArray).extract 0 48 =
    (ByteArray.mk bytes.toArray).extract 0 32 ++ (ByteArray.mk bytes.toArray).extract 32 48
  rw [ByteArray.extract_append_extract]
  rfl

theorem mask_as_fullMaskPad (h : Hash) (pk nonce : ByteArray) (wire : Nat) (value : Bool)
    (point : Nat) (node : Label) :
    mask h pk nonce wire value point node =
      ByteArray.mk (maskPrefix (fullMaskPad
        (fun block => h (maskQuery pk nonce wire value point node block.val)))).toArray := by
  rw [fullMaskPad_prefix]
  rfl

theorem fullMaskPad_law :
    (uniformOn (Set.univ : Set (Fin 2 → Label))).map fullMaskPad =
      uniformOn (Set.univ : Set (Bytes 64)) :=
  uniform_map_equiv (byteBlocksEquiv 2).symm

end WotsLamport.Submission
