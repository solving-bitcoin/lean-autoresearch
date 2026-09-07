import G1Release.Submission.HintAffineTablePrivacy

/-! Conditional row transport with the active oracle answer fixed.
Only the opposite answer and the private odd-modulus coin are permuted.
This is the finite-coordinate form needed by the ROM game coupling. -/
namespace G1Release.Submission.CosetRowCoupling
open SecretRelease HintAffineTable HintAffineTablePrivacy

abbrev InactiveState := Coin × WordBytes

def assemble (selected : Bool) (active : WordBytes) (state : InactiveState) : RowState :=
  if selected then ((state.2,state.1),active) else ((active,state.1),state.2)

def extract (selected : Bool) (state : RowState) : InactiveState :=
  (state.1.2,if selected then state.1.1 else state.2)

@[simp] theorem selected_assemble (selected : Bool) (active : WordBytes) (state : InactiveState) :
    selectedPad selected (assemble selected active state) = active := by
  cases selected <;> rfl

@[simp] theorem extract_assemble (selected : Bool) (active : WordBytes) (state : InactiveState) :
    extract selected (assemble selected active state) = state := by
  cases selected <;> rfl

theorem assemble_extract (selected : Bool) (active : WordBytes) (state : RowState)
    (h : selectedPad selected state = active) :
    assemble selected active (extract selected state) = state := by
  cases selected <;> rcases state with ⟨⟨pad,coin⟩,pad'⟩ <;>
    simp only [selectedPad, Bool.false_eq_true, ↓reduceIte] at h <;>
    subst active <;> rfl

def fiberEquiv (selected : Bool) (active : WordBytes) :
    InactiveState ≃ {state : RowState // selectedPad selected state = active} where
  toFun state := ⟨assemble selected active state,selected_assemble selected active state⟩
  invFun state := extract selected state.val
  left_inv := extract_assemble selected active
  right_inv state := Subtype.ext (assemble_extract selected active state.val state.property)

noncomputable def transport (source target : Params) (row : RowIndex)
    (selected : Bool) (active : WordBytes) : Equiv.Perm InactiveState :=
  (fiberEquiv selected active).trans
    (((rowTransport source target row selected).subtypeEquiv
      (fun state => by rw [rowTransport_selectedPad])).trans (fiberEquiv selected active).symm)

theorem assemble_transport (source target : Params) (row : RowIndex)
    (selected : Bool) (active : WordBytes) (state : InactiveState) :
    assemble selected active (transport source target row selected active state) =
      rowTransport source target row selected (assemble selected active state) := by
  apply assemble_extract
  change selectedPad selected (rowTransport source target row selected
    (assemble selected active state)) = active
  rw [rowTransport_selectedPad, selected_assemble]

theorem transport_row (source target : Params) (row : RowIndex)
    (selected : Bool) (active : WordBytes) (state : InactiveState) :
    rowView target row (assemble selected active (transport source target row selected active state)) =
      rowView source row (assemble selected active state) := by
  rw [assemble_transport, rowTransport_row]

theorem transport_preserving (source target : Params) (row : RowIndex)
    (selected : Bool) (active : WordBytes) :
    MeasureTheory.MeasurePreserving (transport source target row selected active)
      (ProbabilityTheory.uniformOn Set.univ) (ProbabilityTheory.uniformOn Set.univ) :=
  FiniteProbability.uniform_equiv _

end G1Release.Submission.CosetRowCoupling
