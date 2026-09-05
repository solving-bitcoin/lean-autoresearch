import GarblingPrize.Submission.HintPadTransport

namespace GarblingPrize.Submission.HintAffineTablePrivacy

open GarblingPrize.Protected
open HintAffineTable HintPadTransport
open scoped BigOperators

/-- A row's two external pads and its independent private oracle coin. -/
abbrev RowState := (WordBytes × Coin) × WordBytes

def stateHint (state : RowState) : Bool := padHint state.1.1 state.1.2
def stateMask (state : RowState) : Word := maskFromPad state.1.1 (stateHint state)
def selectedPad (selected : Bool) (state : RowState) : WordBytes :=
  if selected then state.2 else state.1.1

def payload (params : Params) (index : RowIndex) (state : RowState) : WordBytes :=
  IdealAffineTable.encodeWord (IdealAffineTable.share params (stateMask state) index true)

def rowView (params : Params) (index : RowIndex) (state : RowState) : WordBytes :=
  pack (IdealAffineTable.encrypt (payload params index state) state.2) (stateHint state)

def translatePadEquiv (oldPayload newPayload : WordBytes) : Equiv.Perm WordBytes where
  toFun := IdealAffineTablePrivacy.translatePad oldPayload newPayload
  invFun := IdealAffineTablePrivacy.translatePad newPayload oldPayload
  left_inv := IdealAffineTablePrivacy.translatePad_source_target_source oldPayload newPayload
  right_inv := IdealAffineTablePrivacy.translatePad_source_target_source newPayload oldPayload

def falseTransport (source target : Params) (index : RowIndex) : Equiv.Perm RowState :=
  Equiv.prodCongrRight fun padCoin =>
    translatePadEquiv
      (IdealAffineTable.encodeWord (IdealAffineTable.share source
        (maskFromPad padCoin.1 (padHint padCoin.1 padCoin.2)) index true))
      (IdealAffineTable.encodeWord (IdealAffineTable.share target
        (maskFromPad padCoin.1 (padHint padCoin.1 padCoin.2)) index true))

noncomputable def rowTransport (source target : Params) (index : RowIndex)
    (selected : Bool) : Equiv.Perm RowState :=
  if selected then
    Equiv.prodCongr (padCoinTransport
      (IdealAffineTable.weight index * (source.coefficient - target.coefficient))) (Equiv.refl _)
  else falseTransport source target index

theorem rowTransport_false_apply (source target : Params) (index : RowIndex) (state : RowState) :
    rowTransport source target index false state =
      (state.1, IdealAffineTablePrivacy.translatePad (payload source index state)
        (payload target index state) state.2) := by
  rfl

theorem rowTransport_true_apply (source target : Params) (index : RowIndex) (state : RowState) :
    rowTransport source target index true state =
      (padCoinTransport (IdealAffineTable.weight index *
        (source.coefficient - target.coefficient)) state.1, state.2) := by
  rfl

theorem rowTransport_hint (source target : Params) (index : RowIndex)
    (selected : Bool) (state : RowState) :
    stateHint (rowTransport source target index selected state) = stateHint state := by
  cases selected
  · rw [rowTransport_false_apply]
    simp only [stateHint]
  · rw [rowTransport_true_apply]
    simp only [stateHint]
    exact padCoinTransport_hint _ state.1

theorem rowTransport_selectedPad (source target : Params) (index : RowIndex)
    (selected : Bool) (state : RowState) :
    selectedPad selected (rowTransport source target index selected state) =
      selectedPad selected state := by
  cases selected
  · rw [rowTransport_false_apply]
    simp only [selectedPad, Bool.false_eq_true, ↓reduceIte]
  · rw [rowTransport_true_apply]
    simp only [selectedPad, ↓reduceIte]

theorem rowTransport_mask (source target : Params) (index : RowIndex)
    (selected : Bool) (state : RowState) :
    stateMask (rowTransport source target index selected state) = stateMask state +
      IdealAffineTable.weight index * (source.coefficient - target.coefficient) *
        IdealAffineTable.bitWord selected := by
  cases selected
  · rw [rowTransport_false_apply]
    simp [stateMask, stateHint, IdealAffineTable.bitWord]
  · rw [rowTransport_true_apply]
    simpa only [stateMask, stateHint, IdealAffineTable.bitWord, ↓reduceIte, mul_one] using
      padCoinTransport_mask
        (IdealAffineTable.weight index * (source.coefficient - target.coefficient)) state.1

/-- Both the serialized row and the selected external pad are preserved. -/
theorem rowTransport_row (source target : Params) (index : RowIndex)
    (selected : Bool) (state : RowState) :
    rowView target index (rowTransport source target index selected state) =
      rowView source index state := by
  cases selected
  · unfold rowView
    rw [rowTransport_hint]
    rw [rowTransport_false_apply]
    apply congrArg (fun ciphertext => pack ciphertext (stateHint state))
    funext position
    simp only [payload, stateMask, stateHint, IdealAffineTable.encrypt]
    rw [IdealAffineTablePrivacy.payload_xor_translatePad]
  · have hpayload : payload target index (rowTransport source target index true state) =
        payload source index state := by
      unfold payload
      rw [IdealAffineTable.share_eq_weight, IdealAffineTable.share_eq_weight, rowTransport_mask]
      apply congrArg IdealAffineTable.encodeWord
      simp only [IdealAffineTable.bitWord, ↓reduceIte, mul_one]
      ring
    unfold rowView
    rw [hpayload, rowTransport_hint]
    rw [rowTransport_true_apply]

instance : Nonempty Coin := ⟨⟨0, by have := modulus_positive; omega⟩⟩

theorem rowTransport_preserves_uniform (source target : Params) (index : RowIndex)
    (selected : Bool) :
    MeasureTheory.MeasurePreserving (rowTransport source target index selected)
      (ProbabilityTheory.uniformOn Set.univ) (ProbabilityTheory.uniformOn Set.univ) := by
  exact measurePreserving_uniformOfFiniteEquiv _

def tableFromState (params : Params) (states : RowIndex → RowState) : Table :=
  Table.ofWords (Fin.cases
    (IdealAffineTable.encodeWord (params.constant - ∑ i, stateMask (states i)))
    (fun index => rowView params index (states index)))

theorem garble_eq_tableFromState (purpose : Purpose) (pairs : RowIndex → Bool → Label)
    (params : Params) (coins : RowIndex → Coin) :
    garble purpose pairs params coins = tableFromState params
      (fun index => ((pairs index false purpose, coins index), pairs index true purpose)) := by
  simp only [garble, prependWord_eq_cases]
  rfl

noncomputable def tableTransport (source target : Params) (bits : RowIndex → Bool) :
    Equiv.Perm (RowIndex → RowState) :=
  Equiv.piCongrRight fun index => rowTransport source target index (bits index)

/-- The leading correction word is invariant because the change in the mask
sum is exactly `(source.coefficient-target.coefficient)*input`. -/
theorem tableFromState_transport (source target : Params) (bits : RowIndex → Bool)
    (houtput : source.coefficient * IdealAffineTable.decodeBits bits + source.constant =
      target.coefficient * IdealAffineTable.decodeBits bits + target.constant)
    (states : RowIndex → RowState) :
    tableFromState target (tableTransport source target bits states) =
      tableFromState source states := by
  have hsum : (∑ i, stateMask (tableTransport source target bits states i)) =
      (∑ i, stateMask (states i)) + (source.coefficient - target.coefficient) *
        IdealAffineTable.decodeBits bits := by
    change (∑ i, stateMask (rowTransport source target i (bits i) (states i))) = _
    simp only [rowTransport_mask, Finset.sum_add_distrib]
    apply congrArg ((∑ i, stateMask (states i)) + ·)
    unfold IdealAffineTable.decodeBits
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  apply Table.ext
  simp only [tableFromState, Table.words_ofWords]
  funext word
  refine Fin.cases ?_ (fun index => ?_) word
  · change IdealAffineTable.encodeWord (target.constant - ∑ i, stateMask
      (tableTransport source target bits states i)) = _
    rw [hsum]
    apply congrArg IdealAffineTable.encodeWord
    change target.constant - ((∑ i, stateMask (states i)) +
      (source.coefficient - target.coefficient) * IdealAffineTable.decodeBits bits) =
        source.constant - ∑ i, stateMask (states i)
    linear_combination -houtput
  · exact rowTransport_row source target index (bits index) (states index)

theorem tableTransport_selectedPads (source target : Params) (bits : RowIndex → Bool)
    (states : RowIndex → RowState) (index : RowIndex) :
    selectedPad (bits index) (tableTransport source target bits states index) =
      selectedPad (bits index) (states index) :=
  rowTransport_selectedPad source target index (bits index) (states index)

theorem tableTransport_preserves_uniform (source target : Params) (bits : RowIndex → Bool) :
    MeasureTheory.MeasurePreserving (tableTransport source target bits)
      (ProbabilityTheory.uniformOn Set.univ) (ProbabilityTheory.uniformOn Set.univ) := by
  exact measurePreserving_uniformOfFiniteEquiv _

end GarblingPrize.Submission.HintAffineTablePrivacy
