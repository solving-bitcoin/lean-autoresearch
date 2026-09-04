import GarblingPrize.Submission.TruthTable

namespace GarblingPrize.Submission.TruthTablePrivacy

open GarblingPrize.Protected
open GarblingPrize.Submission
open TruthTable

abbrev Owner := RowIndex × Bool

def ownerPurpose (owner : Owner) : Purpose :=
  purpose owner.1 owner.2

private theorem ofBits_injective :
    Function.Injective (@Nat.ofBits coordinateBitCount) := by
  intro left right hequal
  funext index
  rw [← Nat.testBit_ofBits_lt left index.val index.isLt,
    ← Nat.testBit_ofBits_lt right index.val index.isLt, hequal]

def rowCode (row : RowIndex) : Nat := Nat.ofBits row

private theorem rowCode_injective : Function.Injective rowCode :=
  ofBits_injective

set_option maxRecDepth 2048 in
theorem ownerPurpose_injective : Function.Injective ownerPurpose := by
  intro left right hequal
  have hunpair := congrArg Nat.unpair hequal
  simp only [ownerPurpose, purpose, Nat.unpair_pair] at hunpair
  have hrow : left.1 = right.1 :=
    ofBits_injective (congrArg Prod.fst hunpair)
  have hchunkCode := congrArg Prod.snd hunpair
  have hchunk : left.2 = right.2 := by
    cases hleft : left.2 <;> cases hright : right.2
    · rfl
    · simp [hleft, hright] at hchunkCode
    · simp [hleft, hright] at hchunkCode
    · rfl
  exact Prod.ext hrow hchunk

noncomputable def purposeOwner (value : Purpose) : Option Owner := by
  classical
  exact if h : ∃ owner, ownerPurpose owner = value then
    some (Classical.choose h)
  else
    none

@[simp] theorem purposeOwner_ownerPurpose (owner : Owner) :
    purposeOwner (ownerPurpose owner) = some owner := by
  unfold purposeOwner
  split
  · rename_i hexists
    congr 1
    apply ownerPurpose_injective
    exact Classical.choose_spec hexists
  · rename_i hnone
    exact False.elim (hnone ⟨owner, rfl⟩)

@[simp] theorem purposeOwner_purpose (row : RowIndex) (chunk : Bool) :
    purposeOwner (purpose row chunk) = some (row, chunk) :=
  purposeOwner_ownerPurpose (row, chunk)

private theorem exists_differing_index (left right : RowIndex)
    (hne : left ≠ right) : ∃ index, left index ≠ right index := by
  by_contra hnone
  apply hne
  funext index
  by_contra hindex
  exact hnone ⟨index, hindex⟩

noncomputable def pivot (row selected : RowIndex) (hne : row ≠ selected) :
    BitIndex :=
  Classical.choose (exists_differing_index row selected hne)

theorem pivot_diff (row selected : RowIndex) (hne : row ≠ selected) :
    row (pivot row selected hne) ≠ selected (pivot row selected hne) :=
  Classical.choose_spec (exists_differing_index row selected hne)

noncomputable def payload (hidden : Hidden) (row : RowIndex) (chunk : Bool) : Block :=
  if chunk then
    secondBlock (encodeOutput (outputForRow hidden row))
  else
    firstBlock (encodeOutput (outputForRow hidden row))

noncomputable def transformOwned (input : Input) (source target : Hidden)
    (pairs : LabelPairs) (owner : Owner) (index : BitIndex) (bit : Bool)
    (value : Purpose) : Block := by
  classical
  exact if hselectedCode : rowCode owner.1 = rowCode (rowIndex input) then
    pairs index bit value
  else
    let hselected : owner.1 ≠ rowIndex input :=
      fun hequal => hselectedCode (congrArg rowCode hequal)
    let selectedPivot := pivot owner.1 (rowIndex input) hselected
    if index = selectedPivot ∧ bit = owner.1 index then
      IdealAffineTablePrivacy.translatePad
        (payload source owner.1 owner.2)
        (payload target owner.1 owner.2)
        (pairs index bit value)
    else
      pairs index bit value

noncomputable def transformPairs (input : Input) (source target : Hidden)
    (pairs : LabelPairs) : LabelPairs :=
  fun index bit value =>
    (purposeOwner value).elim (pairs index bit value)
      (fun owner => transformOwned input source target pairs owner index bit value)

theorem transformPairs_of_owner_none (input : Input) (source target : Hidden)
    (pairs : LabelPairs) (index : BitIndex) (bit : Bool) (value : Purpose)
    (howner : purposeOwner value = none) :
    transformPairs input source target pairs index bit value =
      pairs index bit value := by
  unfold transformPairs
  rw [howner]
  rfl

set_option maxRecDepth 2048 in
theorem transformPairs_of_owner_some (input : Input) (source target : Hidden)
    (pairs : LabelPairs) (index : BitIndex) (bit : Bool) (value : Purpose)
    (owner : Owner) (howner : purposeOwner value = some owner) :
    transformPairs input source target pairs index bit value =
      transformOwned input source target pairs owner index bit value := by
  unfold transformPairs
  rw [howner]
  rfl

set_option maxRecDepth 2048 in
private theorem transformOwned_swapped (input : Input) (source target : Hidden)
    (pairs : LabelPairs) (owner : Owner) (index : BitIndex) (bit : Bool)
    (value : Purpose) (howner : purposeOwner value = some owner) :
    transformOwned input target source
        (transformPairs input source target pairs) owner index bit value =
      pairs index bit value := by
  unfold transformOwned
  split
  · rename_i hselected
    rw [transformPairs_of_owner_some input source target pairs index bit value
      owner howner]
    unfold transformOwned
    rw [dif_pos hselected]
  · rename_i hselected
    dsimp only
    split
    · rename_i hchanged
      rw [transformPairs_of_owner_some input source target pairs index bit value
        owner howner]
      unfold transformOwned
      rw [dif_neg hselected]
      dsimp only
      rw [if_pos hchanged]
      exact IdealAffineTablePrivacy.translatePad_source_target_source _ _ _
    · rename_i hunchanged
      rw [transformPairs_of_owner_some input source target pairs index bit value
        owner howner]
      unfold transformOwned
      rw [dif_neg hselected]
      dsimp only
      rw [if_neg hunchanged]

set_option maxRecDepth 2048 in
theorem transformPairs_at_other_row (input : Input) (source target : Hidden)
    (pairs : LabelPairs) (row : RowIndex) (chunk : Bool)
    (hrow : row ≠ rowIndex input) (index : BitIndex) (bit : Bool) :
    transformPairs input source target pairs index bit (purpose row chunk) =
      if index = pivot row (rowIndex input) hrow ∧ bit = row index then
        IdealAffineTablePrivacy.translatePad
          (payload source row chunk) (payload target row chunk)
          (pairs index bit (purpose row chunk))
      else
        pairs index bit (purpose row chunk) := by
  have hcode : rowCode row ≠ rowCode (rowIndex input) :=
    fun hequal => hrow (rowCode_injective hequal)
  rw [transformPairs_of_owner_some input source target pairs index bit
    (purpose row chunk) (row, chunk) (purposeOwner_purpose row chunk)]
  unfold transformOwned
  rw [dif_neg hcode]

set_option maxRecDepth 2048 in
theorem transformPairs_at_selected_row (input : Input)
    (source target : Hidden) (pairs : LabelPairs) (chunk : Bool)
    (index : BitIndex) (bit : Bool) :
    transformPairs input source target pairs index bit
        (purpose (rowIndex input) chunk) =
      pairs index bit (purpose (rowIndex input) chunk) := by
  rw [transformPairs_of_owner_some input source target pairs index bit
    (purpose (rowIndex input) chunk) (rowIndex input, chunk)
    (purposeOwner_purpose (rowIndex input) chunk)]
  unfold transformOwned
  rw [dif_pos rfl]

set_option maxRecDepth 2048 in
theorem transformPairs_swapped (input : Input) (source target : Hidden)
    (pairs : LabelPairs) :
    transformPairs input target source
        (transformPairs input source target pairs) = pairs := by
  funext index bit value
  cases howner : purposeOwner value with
  | none =>
      rw [transformPairs_of_owner_none input target source _ index bit value howner,
        transformPairs_of_owner_none input source target pairs index bit value howner]
  | some owner =>
      rw [transformPairs_of_owner_some input target source _ index bit value owner howner]
      exact transformOwned_swapped input source target pairs owner index bit value howner

noncomputable def pairsEquiv (input : Input) (source target : Hidden) :
    LabelPairs ≃ LabelPairs where
  toFun := transformPairs input source target
  invFun := transformPairs input target source
  left_inv := transformPairs_swapped input source target
  right_inv := transformPairs_swapped input target source

set_option maxRecDepth 2048 in
theorem transformPairs_activeLabels (input : Input) (source target : Hidden)
    (pairs : LabelPairs) :
    activeLabels (transformPairs input source target pairs) input =
      activeLabels pairs input := by
  funext index value
  unfold activeLabels
  cases howner : purposeOwner value with
  | none =>
      exact transformPairs_of_owner_none input source target pairs index
        (inputBit input index) value howner
  | some owner =>
      rw [transformPairs_of_owner_some input source target pairs index
        (inputBit input index) value owner howner]
      unfold transformOwned
      split
      · rfl
      · rename_i hrow
        have hrow' : owner.1 ≠ rowIndex input :=
          fun hequal => hrow (congrArg rowCode hequal)
        dsimp only
        split
        · rename_i hchanged
          rcases hchanged with ⟨hindex, hbit⟩
          subst index
          exact False.elim
            (pivot_diff owner.1 (rowIndex input) hrow' hbit.symm)
        · rfl

private theorem aggregate_cipher_other_row (input : Input)
    (source target : Hidden) (pairs : LabelPairs) (row : RowIndex)
    (chunk : Bool) (hrow : row ≠ rowIndex input) :
    Bytes.xor (payload target row chunk)
        (aggregatePad (transformPairs input source target pairs) row chunk) =
      Bytes.xor (payload source row chunk) (aggregatePad pairs row chunk) := by
  unfold aggregatePad rowBits
  apply xor_cipher_eq_of_single_translation
      (payload source row chunk) (payload target row chunk)
      (fun index => pairs index (row index) (purpose row chunk))
      (fun index => transformPairs input source target pairs index
        (row index) (purpose row chunk))
      (pivot row (rowIndex input) hrow)
  · rw [transformPairs_at_other_row input source target pairs row chunk hrow]
    simp
  · intro index hindex
    rw [transformPairs_at_other_row input source target pairs row chunk hrow]
    simp [hindex]

private theorem aggregate_selected_row (input : Input)
    (source target : Hidden) (pairs : LabelPairs) (chunk : Bool) :
    aggregatePad (transformPairs input source target pairs) (rowIndex input) chunk =
      aggregatePad pairs (rowIndex input) chunk := by
  unfold aggregatePad
  apply congrArg (xorAll coordinateBitCount)
  funext index
  exact transformPairs_at_selected_row input source target pairs chunk index
    (rowBits (rowIndex input) index)

private theorem selected_payload_eq (input : Input) (source target : Hidden)
    (hequal : reference Profile source input = reference Profile target input)
    (chunk : Bool) :
    payload source (rowIndex input) chunk =
      payload target (rowIndex input) chunk := by
  have houtput : outputForRow source (rowIndex input) =
      outputForRow target (rowIndex input) := by
    rw [outputForRow_selected, outputForRow_selected, hequal]
  simp [payload, houtput]

theorem garbleRow_transformPairs (input : Input) (source target : Hidden)
    (hequal : reference Profile source input = reference Profile target input)
    (pairs : LabelPairs) (row : RowIndex) :
    garbleRow target (transformPairs input source target pairs) row =
      garbleRow source pairs row := by
  by_cases hrow : row = rowIndex input
  · subst row
    have houtput : outputForRow target (rowIndex input) =
        outputForRow source (rowIndex input) := by
      rw [outputForRow_selected, outputForRow_selected, hequal]
    unfold garbleRow
    dsimp only
    rw [houtput, aggregate_selected_row, aggregate_selected_row]
  · unfold garbleRow
    dsimp only
    unfold IdealAffineTable.row
    apply congrArg₂ Bytes.append
    · change Bytes.xor (payload target row false)
          (aggregatePad (transformPairs input source target pairs) row false) = _
      exact aggregate_cipher_other_row input source target pairs row false hrow
    · change Bytes.xor (payload target row true)
          (aggregatePad (transformPairs input source target pairs) row true) = _
      exact aggregate_cipher_other_row input source target pairs row true hrow

theorem garble_transformPairs (input : Input) (source target : Hidden)
    (hequal : reference Profile source input = reference Profile target input)
    (pairs : LabelPairs) :
    garble target (transformPairs input source target pairs) = garble source pairs := by
  apply Artifact.ext
  funext row
  exact garbleRow_transformPairs input source target hequal pairs row

end GarblingPrize.Submission.TruthTablePrivacy
