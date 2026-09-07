import G1Release.Submission.AffineTable

namespace G1Release.Submission.AffineTablePrivacy

open scoped BigOperators
open GarblingPrize.Protected
open G1Release.Submission.AffineTable

abbrev LocalPairs := Fin 254 → Bool → Label

def transformMask (source target : Params)
    (bits : Fin 254 → Bool)
    (masks : Fin 254 → Word) : Fin 254 → Word :=
  fun index => masks index + weight index *
    (source.coefficient - target.coefficient) * bitWord (bits index)

theorem transformMask_mem (source target : Params)
    (bits : Fin 254 → Bool)
    (houtput : source.coefficient * decodeBits bits + source.constant =
      target.coefficient * decodeBits bits + target.constant)
    (masks : MaskFiber source.constant) :
    ∑ index, transformMask source target bits masks.1 index = target.constant := by
  unfold transformMask
  rw [Finset.sum_add_distrib, masks.2]
  have hsum :
      (∑ index : Fin 254,
        weight index * (source.coefficient - target.coefficient) *
          bitWord (bits index)) =
        (source.coefficient - target.coefficient) * decodeBits bits := by
    unfold decodeBits
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro index _
    ring
  rw [hsum]
  linear_combination houtput

def maskEquiv (source target : Params)
    (bits : Fin 254 → Bool)
    (houtput : source.coefficient * decodeBits bits + source.constant =
      target.coefficient * decodeBits bits + target.constant) :
    MaskFiber source.constant ≃ MaskFiber target.constant where
  toFun masks :=
    ⟨transformMask source target bits masks.1,
      transformMask_mem source target bits houtput masks⟩
  invFun masks :=
    ⟨transformMask target source bits masks.1,
      transformMask_mem target source bits houtput.symm masks⟩
  left_inv masks := by
    apply Subtype.ext
    funext index
    simp [transformMask]
    ring
  right_inv masks := by
    apply Subtype.ext
    funext index
    simp [transformMask]
    ring

theorem share_transformMask (source target : Params)
    (bits : Fin 254 → Bool)
    (masks : Fin 254 → Word) (index : Fin 254) :
    share target (transformMask source target bits masks index) index
        (bits index) =
      share source (masks index) index (bits index) := by
  rw [share_eq_weight, share_eq_weight]
  cases hbit : bits index
  · simp [transformMask, bitWord, hbit]
  · simp [transformMask, bitWord, hbit]
    ring

theorem share_maskEquiv (source target : Params)
    (bits : Fin 254 → Bool)
    (houtput : source.coefficient * decodeBits bits + source.constant =
      target.coefficient * decodeBits bits + target.constant)
    (masks : MaskFiber source.constant) (index : Fin 254) :
    share target ((maskEquiv source target bits houtput masks).1 index) index
        (bits index) =
      share source (masks.1 index) index (bits index) := by
  exact share_transformMask source target bits masks.1 index

def translatePad (oldPayload newPayload pad : WordBytes) : WordBytes :=
  Bytes.xor newPayload (Bytes.xor oldPayload pad)

@[simp] theorem translatePad_source_target_source
    (oldPayload newPayload pad : WordBytes) :
    translatePad newPayload oldPayload
        (translatePad oldPayload newPayload pad) = pad := by
  unfold translatePad
  rw [Bytes.xor_cancel_left, Bytes.xor_cancel_left]

theorem payload_xor_translatePad
    (oldPayload newPayload pad : WordBytes) :
    Bytes.xor newPayload (translatePad oldPayload newPayload pad) =
      Bytes.xor oldPayload pad := by
  exact Bytes.xor_cancel_left newPayload (Bytes.xor oldPayload pad)

end G1Release.Submission.AffineTablePrivacy
