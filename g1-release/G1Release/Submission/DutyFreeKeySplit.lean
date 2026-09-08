import G1Release.Submission.DutyFreeIdeal
import G1Release.Submission.LamportLaw

/-! Exact disintegration of the bridge keys: one uniformly random hidden
label per nibble, independent of the other fifteen labels and every external
Lamport pair. No collision-free assumption on these internal keys is used. -/
namespace G1Release.Submission.DutyFreeKeySplit
open SecretRelease G1Release.Protected DutyFreeSlots
open MeasureTheory ProbabilityTheory

abbrev Hidden := Fin 128 → Label
abbrev Public (input : Input) := (id : Fin 128) → {cell : DutyFreeLayout.Cell //
  cell ≠ selectedCell input id} → Label

def split (input : Input) : HotKeys ≃ Hidden × Public input where
  toFun hot := (fun id => hot id (selectedCell input id), fun id cell => hot id cell.val)
  invFun keys := fun id cell => if h : cell = selectedCell input id then keys.1 id
    else keys.2 id ⟨cell,h⟩
  left_inv hot := by
    funext id cell
    dsimp only
    by_cases h : cell = selectedCell input id
    · simp [h]
    · simp [h]
  right_inv keys := by
    apply Prod.ext
    · funext id
      simp
    · funext id cell
      simp only [dif_neg cell.property]

theorem split_preserving (input : Input) :
    MeasurePreserving (split input) (uniformOn Set.univ)
      ((uniformOn (Set.univ : Set Hidden)).prod (uniformOn (Set.univ : Set (Public input)))) := by
  rw [LamportLaw.prod_uniform_univ]
  exact FiniteProbability.uniform_equiv (split input)

theorem selected (input : Input) (hidden : Hidden) (revealed : Public input) (id : Fin 128) :
    (split input).symm (hidden,revealed) id (selectedCell input id) = hidden id := by
  simp [split]

theorem unselected (input : Input) (hidden : Hidden) (revealed : Public input)
    (id : Fin 128) (cell : DutyFreeLayout.Cell) (h : cell ≠ selectedCell input id) :
    (split input).symm (hidden,revealed) id cell = revealed id ⟨cell,h⟩ := by
  simp only [split, Equiv.coe_fn_symm_mk, dif_neg h]

theorem garble_independent (hash : Hash) (input : Input) (privateValue : Private)
    (random : DutyFreeProgram.Randomness privateValue) (active : DutyFreeIdeal.Active)
    (source target : Hidden) (revealed : Public input)
    (bridgePads : DutyFreeIdeal.BridgePads) (plainPads : DutyFreeIdeal.PlainPads) :
    DutyFreeIdeal.garble hash input privateValue random active ((split input).symm (source,revealed))
        bridgePads plainPads =
      DutyFreeIdeal.garble hash input privateValue random active ((split input).symm (target,revealed))
        bridgePads plainPads := by
  apply DutyFreeIdeal.garble_independent
  intro id cell h
  rw [unselected input source revealed id cell h, unselected input target revealed id cell h]

end G1Release.Submission.DutyFreeKeySplit
