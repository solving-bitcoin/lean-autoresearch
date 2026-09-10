import G1Release.Submission.DutyFreeIdeal
import G1Release.Submission.CosetCorePrivacy

/-! Translate only the unreleased plain pads. The complete 91-map core
coupling preserves every selected affine value. Hence its coefficient change
is absorbed by the selected pads without changing any serialized join or
decoder. The map on finite raw pads is a bijection, including its small tail. -/
namespace G1Release.Submission.DutyFreeViewCoupling
open SecretRelease G1Release.Protected G1Release.Math
open DutyFreeLayout DutyFreeSlots DutyFreeIdeal
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

abbrev RandomPads (hidden : Private) := DutyFreeProgram.Randomness hidden × PlainPads

def padChange (differences : Table → DutyFreeTables.Word) : Equiv.Perm PlainPads :=
  Equiv.piCongrRight fun table => Equiv.piCongrRight fun chunk =>
    DutyFreeFieldPad.transport (DutyFreeChunks.weight chunk * differences table)

def good (pads : PlainPads) : Prop := ∀ table chunk, pads table chunk ∉ DutyFreeFieldPad.bad

theorem masks_changed (hash : Hash) (input : Input) (hot : HotKeys)
    (pads : PlainPads) (differences : Table → DutyFreeTables.Word) (hg : good pads)
    (table : Table) (source target : DutyFreeTables.Word)
    (hd : differences table = source-target) :
    masks hash input hot (padChange differences pads) table =
      DutyFreeChunkAffine.transport DutyFreeChunks.weight (inputCell input (sideFor table))
        source target (masks hash input hot pads table) := by
  funext chunk cell
  rw [DutyFreeChunkAffine.transport_apply]
  simp only [masks, DutyFreeOneHot.selected]
  split
  · change DutyFreeFieldPad.sample
        (DutyFreeFieldPad.transport (DutyFreeChunks.weight chunk * differences table) (pads table chunk)) = _
    rw [DutyFreeFieldPad.transport_sample _ _ (hg table chunk), hd]
  · exact (add_zero _).symm

noncomputable def differences (input : Input) (source target : Private)
    (hequal : GLVOffsetFamily.mapAt source input = GLVOffsetFamily.mapAt target input)
    (random : DutyFreeProgram.Randomness source) (table : Table) : DutyFreeTables.Word :=
  (CosetScheme.mapParams source random (mapOf table) (kindOf table)).coefficient -
    (CosetScheme.mapParams target
      (CosetCorePrivacy.targetRandomness input source target hequal random)
      (mapOf table) (kindOf table)).coefficient

noncomputable def transport (input : Input) (source target : Private)
    (hequal : GLVOffsetFamily.mapAt source input = GLVOffsetFamily.mapAt target input) :
    RandomPads source ≃ RandomPads target :=
  (Equiv.prodCongrRight fun random => padChange (differences input source target hequal random)).trans
    (Equiv.prodCongr (CosetCorePrivacy.randomnessEquiv input source target hequal) (Equiv.refl _))

theorem tableId_map_kind (table : Table) : tableId (mapOf table) (kindOf table) = table := by
  apply Fin.ext
  simp only [tableId, mapOf, kindOf]
  omega

theorem decoded_coordinate (input : Input) (table : Table) :
    DutyFreeChunkAffine.decodeInput DutyFreeChunks.weight (inputCell input (sideFor table)) =
      AffineTable.decodeBits (CosetSlots.bitsFor (kindOf table) input) := by
  have hc : (((coordinate input (sideFor table)).val : BN254.Fq)).val =
      (coordinate input (sideFor table)).val := ZMod.val_cast_of_lt (coordinate input (sideFor table)).isLt
  have hv := DutyFreeChunks.reconstruct (((coordinate input (sideFor table)).val : BN254.Fq))
  rw [hc] at hv
  change DutyFreeChunkAffine.decodeInput _ _ = _ at hv
  change DutyFreeChunkAffine.decodeInput DutyFreeChunks.weight
    (DutyFreeChunks.value (coordinate input (sideFor table)).val) = _
  rw [hv]
  have hb : AffineTable.decodeBits (CosetSlots.bitsFor (kindOf table) input) =
      CosetHintMap.inputFor (kindOf table) (input.val.1.val : BN254.Fq) (input.val.2.val : BN254.Fq) := by
    generalize hk : kindOf table = kind
    fin_cases kind <;> simp [CosetSlots.bitsFor, CosetHintMap.inputFor,
      Scheme.decodeBits_xBits, Scheme.decodeBits_yBits]
  rw [hb]
  simpa only [tableId_map_kind] using field_coordinate input (mapOf table) (kindOf table)

theorem table_preserved (hash : Hash) (input : Input) (source target : Private)
    (hequal : GLVOffsetFamily.mapAt source input = GLVOffsetFamily.mapAt target input)
    (hot : HotKeys) (state : RandomPads source) (hg : good state.2) (index : Table) :
    table hash input target (transport input source target hequal state).1 hot
        (transport input source target hequal state).2 index =
      table hash input source state.1 hot state.2 index := by
  unfold table
  simp only [DutyFreeTables.garble_eq]
  apply congrArg DutyFreeTables.pack
  change DutyFreeChunkAffine.garble _
    (masks hash input hot (padChange (differences input source target hequal state.1) state.2) index)
    _ _ = _
  rw [masks_changed hash input hot state.2 _ hg index _ _ rfl]
  apply DutyFreeChunkAffine.artifact_preserved
  rw [decoded_coordinate]
  exact CosetCorePrivacy.params_preserved input source target hequal state.1 (mapOf index) (kindOf index)

theorem artifact_preserved (hash : Hash) (input : Input) (source target : Private)
    (hequal : GLVOffsetFamily.mapAt source input = GLVOffsetFamily.mapAt target input)
    (active : Active) (hot : HotKeys) (bridgePads : BridgePads)
    (state : RandomPads source) (hg : good state.2) :
    garble hash input target (transport input source target hequal state).1 active hot bridgePads
        (transport input source target hequal state).2 =
      garble hash input source state.1 active hot bridgePads state.2 := by
  unfold garble
  apply congrArg₂ DutyFreeArtifact.ofParts
  · rfl
  · funext index
    exact table_preserved hash input source target hequal hot state hg index

theorem transport_preserving (input : Input) (source target : Private)
    (hequal : GLVOffsetFamily.mapAt source input = GLVOffsetFamily.mapAt target input) :
    MeasureTheory.MeasurePreserving (transport input source target hequal)
      (ProbabilityTheory.uniformOn Set.univ) (ProbabilityTheory.uniformOn Set.univ) :=
  FiniteProbability.uniform_equiv (transport input source target hequal)

end G1Release.Submission.DutyFreeViewCoupling
