import GarblingPrize.Submission.IdealAffineTable

namespace GarblingPrize.Submission.IdealAffineTablePrivacy

open scoped BigOperators
open GarblingPrize.Protected
open GarblingPrize.Submission.IdealAffineTable

abbrev LocalPairs := Fin tableWidth → Bool → Label

def transformMask (source target : Params)
    (bits : Fin tableWidth → Bool)
    (masks : Fin tableWidth → Word) : Fin tableWidth → Word :=
  fun index => masks index + weight index *
    (source.coefficient - target.coefficient) * bitWord (bits index)

theorem transformMask_mem (source target : Params)
    (bits : Fin tableWidth → Bool)
    (houtput : source.coefficient * decodeBits bits + source.constant =
      target.coefficient * decodeBits bits + target.constant)
    (masks : MaskFiber source.constant) :
    ∑ index, transformMask source target bits masks.1 index = target.constant := by
  unfold transformMask
  rw [Finset.sum_add_distrib, masks.2]
  have hsum :
      (∑ index : Fin tableWidth,
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
    (bits : Fin tableWidth → Bool)
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
    (bits : Fin tableWidth → Bool)
    (masks : Fin tableWidth → Word) (index : Fin tableWidth) :
    share target (transformMask source target bits masks index) index
        (bits index) =
      share source (masks index) index (bits index) := by
  rw [share_eq_weight, share_eq_weight]
  cases hbit : bits index
  · simp [transformMask, bitWord, hbit]
  · simp [transformMask, bitWord, hbit]
    ring

theorem share_maskEquiv (source target : Params)
    (bits : Fin tableWidth → Bool)
    (houtput : source.coefficient * decodeBits bits + source.constant =
      target.coefficient * decodeBits bits + target.constant)
    (masks : MaskFiber source.constant) (index : Fin tableWidth) :
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

def updateAt (label : Label) (purpose : Purpose) (value : WordBytes) : Label :=
  fun other => if other = purpose then value else label other

@[simp] theorem updateAt_same (label : Label) (purpose : Purpose)
    (value : WordBytes) : updateAt label purpose value purpose = value := by
  simp [updateAt]

theorem updateAt_other (label : Label) (purpose other : Purpose)
    (value : WordBytes) (hne : other ≠ purpose) :
    updateAt label purpose value other = label other := by
  simp [updateAt, hne]

def payload (params : Params) (masks : Fin tableWidth → Word)
    (index : Fin tableWidth) (bit : Bool) : WordBytes :=
  encodeWord (share params (masks index) index bit)

def translatePairs (purpose : Purpose)
    (source target : Params) (bits : Fin tableWidth → Bool)
    (sourceMasks : MaskFiber source.constant)
    (targetMasks : MaskFiber target.constant)
    (pairs : LocalPairs) : LocalPairs :=
  fun index bit =>
    if bit = bits index then
      pairs index bit
    else
      updateAt (pairs index bit) purpose
        (translatePad
          (payload source sourceMasks.1 index bit)
          (payload target targetMasks.1 index bit)
          (pairs index bit purpose))

@[simp] theorem translatePairs_selected (purpose : Purpose)
    (source target : Params) (bits : Fin tableWidth → Bool)
    (sourceMasks : MaskFiber source.constant)
    (targetMasks : MaskFiber target.constant)
    (pairs : LocalPairs) (index : Fin tableWidth) :
    translatePairs purpose source target bits sourceMasks targetMasks pairs
        index (bits index) = pairs index (bits index) := by
  simp [translatePairs]

theorem translatePairs_pad (purpose : Purpose)
    (source target : Params) (bits : Fin tableWidth → Bool)
    (houtput : source.coefficient * decodeBits bits + source.constant =
      target.coefficient * decodeBits bits + target.constant)
    (sourceMasks : MaskFiber source.constant)
    (pairs : LocalPairs) (index : Fin tableWidth) (bit : Bool) :
    Bytes.xor
        (payload target
          (maskEquiv source target bits houtput sourceMasks).1 index bit)
        (translatePairs purpose source target bits sourceMasks
          (maskEquiv source target bits houtput sourceMasks) pairs index bit purpose) =
      Bytes.xor (payload source sourceMasks.1 index bit)
        (pairs index bit purpose) := by
  by_cases hselected : bit = bits index
  · subst bit
    rw [translatePairs_selected]
    rw [show payload target
          (maskEquiv source target bits houtput sourceMasks).1 index
            (bits index) =
        payload source sourceMasks.1 index (bits index) by
      unfold payload
      rw [share_maskEquiv source target bits houtput sourceMasks index]]
  · simp only [translatePairs, hselected, if_false, updateAt_same]
    exact payload_xor_translatePad _ _ _

theorem translatePairs_swapped (purpose : Purpose)
    (source target : Params) (bits : Fin tableWidth → Bool)
    (sourceMasks : MaskFiber source.constant)
    (targetMasks : MaskFiber target.constant)
    (pairs : LocalPairs) :
    translatePairs purpose target source bits targetMasks sourceMasks
        (translatePairs purpose source target bits sourceMasks targetMasks pairs) =
      pairs := by
  funext index bit otherPurpose
  by_cases hselected : bit = bits index
  · subst bit
    simp [translatePairs]
  · by_cases hpurpose : otherPurpose = purpose
    · subst otherPurpose
      simp only [translatePairs, hselected, if_false, updateAt_same]
      exact translatePad_source_target_source
        (payload source sourceMasks.1 index bit)
        (payload target targetMasks.1 index bit)
        (pairs index bit purpose)
    · simp only [translatePairs, hselected, if_false]
      rw [updateAt_other _ _ _ _ hpurpose, updateAt_other _ _ _ _ hpurpose]

@[ext] structure State (params : Params) where
  masks : MaskFiber params.constant
  pairs : LocalPairs

def forward (purpose : Purpose) (source target : Params)
    (bits : Fin tableWidth → Bool)
    (houtput : source.coefficient * decodeBits bits + source.constant =
      target.coefficient * decodeBits bits + target.constant)
    (state : State source) : State target :=
  let targetMasks := maskEquiv source target bits houtput state.masks
  { masks := targetMasks
    pairs := translatePairs purpose source target bits state.masks
      targetMasks state.pairs }

theorem forward_swapped_forward (purpose : Purpose) (source target : Params)
    (bits : Fin tableWidth → Bool)
    (houtput : source.coefficient * decodeBits bits + source.constant =
      target.coefficient * decodeBits bits + target.constant)
    (state : State source) :
    forward purpose target source bits houtput.symm
        (forward purpose source target bits houtput state) = state := by
  let targetMasks := maskEquiv source target bits houtput state.masks
  have hmasks : maskEquiv target source bits houtput.symm targetMasks =
      state.masks := (maskEquiv source target bits houtput).left_inv state.masks
  apply State.ext
  · exact hmasks
  · change translatePairs purpose target source bits targetMasks
        (maskEquiv target source bits houtput.symm targetMasks)
        (translatePairs purpose source target bits state.masks targetMasks
          state.pairs) = state.pairs
    rw [hmasks]
    exact translatePairs_swapped purpose source target bits state.masks
      targetMasks state.pairs

def stateEquiv (purpose : Purpose) (source target : Params)
    (bits : Fin tableWidth → Bool)
    (houtput : source.coefficient * decodeBits bits + source.constant =
      target.coefficient * decodeBits bits + target.constant) :
    State source ≃ State target where
  toFun := forward purpose source target bits houtput
  invFun := forward purpose target source bits houtput.symm
  left_inv := forward_swapped_forward purpose source target bits houtput
  right_inv := forward_swapped_forward purpose target source bits houtput.symm

theorem stateEquiv_selectedLabels (purpose : Purpose) (source target : Params)
    (bits : Fin tableWidth → Bool)
    (houtput : source.coefficient * decodeBits bits + source.constant =
      target.coefficient * decodeBits bits + target.constant)
    (state : State source) :
    (fun index =>
      (stateEquiv purpose source target bits houtput state).pairs index
        (bits index)) =
      fun index => state.pairs index (bits index) := by
  funext index
  simp [stateEquiv, forward, translatePairs]

theorem stateEquiv_garble (purpose : Purpose) (source target : Params)
    (bits : Fin tableWidth → Bool)
    (houtput : source.coefficient * decodeBits bits + source.constant =
      target.coefficient * decodeBits bits + target.constant)
    (state : State source) :
    garble purpose (stateEquiv purpose source target bits houtput state).pairs
        target (stateEquiv purpose source target bits houtput state).masks =
      garble purpose state.pairs source state.masks := by
  apply Table.ext
  funext pair
  apply congrArg packCiphertexts
  unfold materializeCiphertexts
  apply congrArg Vector.ofFn
  funext slot
  let index := slotRow pair slot
  let selected := slotSelected slot
  change Bytes.xor
        (payload target
          (maskEquiv source target bits houtput state.masks).1 index selected)
        ((translatePairs purpose source target bits state.masks
          (maskEquiv source target bits houtput state.masks) state.pairs)
            index selected purpose) =
    Bytes.xor (payload source state.masks.1 index selected)
      (state.pairs index selected purpose)
  exact translatePairs_pad purpose source target bits houtput state.masks
    state.pairs index selected

end GarblingPrize.Submission.IdealAffineTablePrivacy
