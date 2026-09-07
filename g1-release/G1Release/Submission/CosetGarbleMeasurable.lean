import G1Release.Submission.CosetRealIdeal
import G1Release.Submission.MeasurableModels

namespace G1Release.Submission.CosetGarbleMeasurable
open SecretRelease G1Release.Protected
open CosetSampler CosetSlots CosetRealIdeal MeasureTheory

abbrev Pads := Slot × Bool → Label

def fromPads (hidden : Hidden) (random : Randomness hidden) (pads : Pads) : ByteArray :=
  CosetScheme.encode ⟨fun index => ⟨fun kind =>
    HintAffineTablePrivacy.tableFromState (CosetScheme.mapParams hidden random.1 index kind)
      (fun row => ((pads ((index,kind,row),false), random.2 index kind row),
        pads ((index,kind,row),true)))⟩⟩

def realPads (hash : Hash) (keys : Fin 512 → Pair) : Pads := fun coordinate =>
  AffineTable.pad hash ((keys (wire coordinate.1)).get coordinate.2)
    (purpose coordinate.1) coordinate.1.2.2.val

def idealPads (hash : Hash) (input : Input) (active : Fin 512 → Label)
    (inactive : CosetIdealView.InactivePads) : Pads := fun coordinate =>
  if coordinate.2 = bit input coordinate.1 then
    AffineTable.pad hash (active (wire coordinate.1))
      (purpose coordinate.1) coordinate.1.2.2.val
  else inactive coordinate.1

theorem real_eq (hash : Hash) (hidden : Hidden) (random : Randomness hidden) (keys : Fin 512 → Pair) :
    CosetScheme.encode (CosetScheme.garble hash hidden random.1 random.2 keys) =
      fromPads hidden random (realPads hash keys) := by
  apply congrArg CosetScheme.encode
  apply CosetFamilyArtifact.Artifact.ext
  funext index
  apply CosetHintMap.Artifact.ext
  funext kind
  change HintAffineTable.garble _ _ _ _ = _
  rw [HintAffineTablePrivacy.garble_eq_tableFromState]
  apply congrArg (HintAffineTablePrivacy.tableFromState _)
  funext row
  rw [pairsFor_tableWire, pairsFor_tableWire]
  rfl

theorem ideal_eq (hash : Hash) (hidden : Hidden) (random : Randomness hidden) (input : Input)
    (active : Fin 512 → Label) (inactive : CosetIdealView.InactivePads) :
    CosetIdealView.garble hash input hidden random active inactive =
      fromPads hidden random (idealPads hash input active inactive) := by
  apply congrArg CosetScheme.encode
  apply CosetFamilyArtifact.Artifact.ext
  funext index
  apply CosetHintMap.Artifact.ext
  funext kind
  apply congrArg (HintAffineTablePrivacy.tableFromState _)
  funext row
  unfold CosetIdealView.rowState CosetRowCoupling.assemble idealPads
  cases bit input (index,kind,row) <;> rfl

theorem garble_measurable {Ω : Type*} [MeasurableSpace Ω]
    (hash : Ω → Hash) (hh : ∀ query, Measurable (fun ω => hash ω query))
    (hidden : Hidden) (random : Randomness hidden) (keys : Fin 512 → Pair) :
    Measurable (fun ω => CosetScheme.encode (CosetScheme.garble (hash ω) hidden random.1 random.2 keys)) := by
  simp_rw [real_eq]
  apply (Measurable.of_discrete : Measurable (fromPads hidden random)).comp
  apply measurable_pi_lambda
  intro coordinate
  exact hh _

theorem ideal_measurable {Ω : Type*} [MeasurableSpace Ω]
    (hash : Ω → Hash) (hh : ∀ query, Measurable (fun ω => hash ω query))
    (hidden : Hidden) (random : Randomness hidden) (input : Input) (active : Fin 512 → Label)
    (inactive : Ω → CosetIdealView.InactivePads) (hi : Measurable inactive) :
    Measurable (fun ω => CosetIdealView.garble (hash ω) input hidden random active (inactive ω)) := by
  simp_rw [ideal_eq]
  apply (Measurable.of_discrete : Measurable (fromPads hidden random)).comp
  apply measurable_pi_lambda
  intro coordinate
  unfold idealPads
  split
  · exact hh _
  · exact (measurable_pi_apply coordinate.1).comp hi

end G1Release.Submission.CosetGarbleMeasurable
