import G1Release.Submission.CosetSlots
import G1Release.Submission.CosetRowCoupling

/-! Oracle answers at unselected labels are replaced with independent finite
coordinates. This view uses the selected labels only. The real/ideal hop
must account for any adversarial query at an unselected-label address. -/
namespace G1Release.Submission.CosetIdealView
open SecretRelease G1Release.Protected
open CosetSlots CosetSampler

abbrev InactivePads := Slot → Label

def rowState {hidden : Private} (hash : Hash) (input : Input) (random : Randomness hidden)
    (active : Fin 512 → Label) (inactive : InactivePads) (slot : Slot) : HintAffineTablePrivacy.RowState :=
  CosetRowCoupling.assemble (bit input slot)
    (AffineTable.pad hash (active (wire slot)) (purpose slot) slot.2.2.val)
    (random.2 slot.1 slot.2.1 slot.2.2, inactive slot)

def maps (hash : Hash) (input : Input) (hidden : Private) (random : Randomness hidden)
    (active : Fin 512 → Label) (inactive : InactivePads) (index : Fin 91) : CosetHintMap.Artifact where
  tables := fun kind => HintAffineTablePrivacy.tableFromState
    (CosetScheme.mapParams hidden random.1 index kind)
    (fun row => rowState hash input random active inactive (index,kind,row))

def garble (hash : Hash) (input : Input) (hidden : Private) (random : Randomness hidden)
    (active : Fin 512 → Label) (inactive : InactivePads) : ByteArray :=
  CosetScheme.encode ⟨maps hash input hidden random active inactive⟩

end G1Release.Submission.CosetIdealView
