import G1Release.Submission.DutyFreeRealIdeal
import G1Release.Submission.MeasurableModels

/-! Each artifact depends on finitely many fixed oracle coordinates once
keys and coins are fixed. Factor it through those finite material values to
establish measurability of the actual serialized experiments. -/
namespace G1Release.Submission.DutyFreeGarbleMeasurable
open SecretRelease G1Release.Protected GarblingPrize.Protected
open DutyFreeLayout DutyFreeSlots DutyFreeRealIdeal MeasureTheory
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

abbrev Material := (Fin 128 → DutyFreeBridge.Artifact) ×
  (Table → Chunk → Cell → DutyFreeFieldPad.Raw)

local instance : DiscreteMeasurableSpace Material :=
  MeasurableSingletonClass.toDiscreteMeasurableSpace

def fromMaterial (hidden : Private) (random : DutyFreeProgram.Randomness hidden)
    (material : Material) : ByteArray :=
  DutyFreeArtifact.encode (DutyFreeArtifact.ofParts
    (fun id => DutyFreeProgram.packBridge (material.1 id))
    (fun table =>
      let params := CosetScheme.mapParams hidden random (mapOf table) (kindOf table)
      DutyFreeTables.garble (fun chunk cell => DutyFreeFieldPad.sample (material.2 table chunk cell))
        params.coefficient params.constant))

def realMaterial (hash : Hash) (keys : Keys) (hot : HotKeys) : Material :=
  ((fun id => DutyFreeBridge.garble (DutyFreeProgram.bridgeHash hash (bridgeSide id) (bridgeChunk id))
      (DutyFreeProgram.bridgeKeys keys (bridgeSide id) (bridgeChunk id)) (hot id)),
    fun table chunk cell =>
      (AffineTable.pad hash (hot (bridgeId (sideFor table) chunk) cell)
        (plainPurpose table chunk) (plainRow cell 0),
       AffineTable.pad hash (hot (bridgeId (sideFor table) chunk) cell)
        (plainPurpose table chunk) (plainRow cell 1)))

theorem real_eq (hash : Hash) (hidden : Private) (random : DutyFreeProgram.Randomness hidden)
    (keys : Keys) (hot : HotKeys) :
    DutyFreeArtifact.encode (DutyFreeProgram.garble hash hidden random keys hot) =
      fromMaterial hidden random (realMaterial hash keys hot) := by
  unfold fromMaterial
  apply congrArg DutyFreeArtifact.encode
  unfold DutyFreeProgram.garble
  apply congrArg₂ DutyFreeArtifact.ofParts
  · funext id
    rw [Vector.get_ofFn]
    rfl
  · funext table
    rw [Vector.get_ofFn]
    rfl

def idealMaterial (hash : Hash) (input : Input) (active : DutyFreeIdeal.Active) (hot : HotKeys)
    (bridgePads : DutyFreeIdeal.BridgePads) (plainPads : DutyFreeIdeal.PlainPads) : Material :=
  ((fun id cell bit => if (!DutyFreeBridge.bit cell bit) = externalBit input (id,cell,bit) then
      Bytes.xor (hot id cell) (AffineTable.pad hash (active (externalWire (id,cell,bit)))
        id.val (bridgeRow cell bit)) else bridgePads (id,cell,bit)),
   fun table chunk cell => if cell = inputCell input (sideFor table) chunk then plainPads table chunk
     else (AffineTable.pad hash (hot (bridgeId (sideFor table) chunk) cell)
        (plainPurpose table chunk) (plainRow cell 0),
       AffineTable.pad hash (hot (bridgeId (sideFor table) chunk) cell)
        (plainPurpose table chunk) (plainRow cell 1)))

theorem ideal_eq (hash : Hash) (input : Input) (hidden : Private)
    (random : DutyFreeProgram.Randomness hidden) (active : DutyFreeIdeal.Active) (hot : HotKeys)
    (bridgePads : DutyFreeIdeal.BridgePads) (plainPads : DutyFreeIdeal.PlainPads) :
    DutyFreeArtifact.encode (DutyFreeIdeal.garble hash input hidden random active hot bridgePads plainPads) =
      fromMaterial hidden random (idealMaterial hash input active hot bridgePads plainPads) := by
  unfold fromMaterial
  apply congrArg DutyFreeArtifact.encode
  apply congrArg₂ DutyFreeArtifact.ofParts
  · rfl
  · funext table
    unfold DutyFreeIdeal.table
    apply congrArg₂ (fun masks (params : AffineTable.Params) => DutyFreeTables.garble masks params.coefficient params.constant)
    · funext chunk cell
      simp only [DutyFreeIdeal.masks, idealMaterial]
      split <;> rfl
    · rfl

theorem real_measurable {Ω : Type*} [MeasurableSpace Ω] (hash : Ω → Hash)
    (hh : ∀ query, Measurable (fun ω => hash ω query))
    (hidden : Private) (random : DutyFreeProgram.Randomness hidden) (keys : Keys) (hot : HotKeys) :
    Measurable (fun ω => DutyFreeArtifact.encode (DutyFreeProgram.garble (hash ω) hidden random keys hot)) := by
  simp_rw [real_eq]
  apply (Measurable.of_discrete : Measurable (fromMaterial hidden random)).comp
  apply Measurable.prodMk
  · apply measurable_pi_lambda
    intro id
    apply measurable_pi_lambda
    intro cell
    apply measurable_pi_lambda
    intro bit
    exact (Measurable.of_discrete : Measurable (Bytes.xor (hot id cell))).comp (hh _)
  · apply measurable_pi_lambda
    intro table
    apply measurable_pi_lambda
    intro chunk
    apply measurable_pi_lambda
    intro cell
    exact (hh _).prodMk (hh _)

theorem ideal_measurable {Ω : Type*} [MeasurableSpace Ω] (hash : Ω → Hash)
    (hh : ∀ query, Measurable (fun ω => hash ω query))
    (hidden : Private) (random : DutyFreeProgram.Randomness hidden) (input : Input)
    (active : DutyFreeIdeal.Active) (hot : HotKeys)
    (bridgePads : Ω → DutyFreeIdeal.BridgePads) (hb : Measurable bridgePads)
    (plainPads : Ω → DutyFreeIdeal.PlainPads) (hp : Measurable plainPads) :
    Measurable (fun ω => DutyFreeArtifact.encode
      (DutyFreeIdeal.garble (hash ω) input hidden random active hot (bridgePads ω) (plainPads ω))) := by
  simp_rw [ideal_eq]
  apply (Measurable.of_discrete : Measurable (fromMaterial hidden random)).comp
  apply Measurable.prodMk
  · apply measurable_pi_lambda
    intro id
    apply measurable_pi_lambda
    intro cell
    apply measurable_pi_lambda
    intro bit
    by_cases h : (!DutyFreeBridge.bit cell bit) = externalBit input (id,cell,bit)
    · simp only [if_pos h]
      exact (Measurable.of_discrete : Measurable (Bytes.xor (hot id cell))).comp (hh _)
    · simp only [if_neg h]
      exact (measurable_pi_apply (id,cell,bit)).comp hb
  · apply measurable_pi_lambda
    intro table
    apply measurable_pi_lambda
    intro chunk
    apply measurable_pi_lambda
    intro cell
    by_cases h : cell = inputCell input (sideFor table) chunk
    · simp only [if_pos h]
      exact (measurable_pi_apply chunk).comp ((measurable_pi_apply table).comp hp)
    · simp only [if_neg h]
      exact (hh _).prodMk (hh _)

end G1Release.Submission.DutyFreeGarbleMeasurable
