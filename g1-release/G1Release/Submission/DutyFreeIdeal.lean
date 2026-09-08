import G1Release.Submission.DutyFreeSlots

/-! An explicit simulated artifact. It uses selected external labels, all
unselected bridge keys, and independent fake ciphertext/pad coordinates.
In particular the unreleased bridge key is absent from its selected row. -/
namespace G1Release.Submission.DutyFreeIdeal
open SecretRelease G1Release.Protected
open DutyFreeLayout DutyFreeSlots

abbrev Active := Fin 512 → Label
abbrev BridgePads := BridgeSlot → Label
abbrev PlainPads := Table → Chunk → DutyFreeFieldPad.Raw

def bridge (hash : Hash) (input : Input) (active : Active) (hot : HotKeys)
    (fake : BridgePads) (id : Fin 128) : DutyFreeWords.Block 64 :=
  DutyFreeProgram.packBridge fun cell bit =>
    if (!DutyFreeBridge.bit cell bit) = externalBit input (id,cell,bit) then
      GarblingPrize.Protected.Bytes.xor (hot id cell)
        (AffineTable.pad hash (active (externalWire (id,cell,bit))) id.val (bridgeRow cell bit))
    else fake (id,cell,bit)

def masks (hash : Hash) (input : Input) (hot : HotKeys) (fake : PlainPads)
    (table : Table) : DutyFreeTables.Masks :=
  fun chunk cell => if cell = inputCell input (sideFor table) chunk then
    DutyFreeFieldPad.sample (fake table chunk)
  else DutyFreeProgram.fieldPad hash table chunk cell (hot (bridgeId (sideFor table) chunk) cell)

def table (hash : Hash) (input : Input) (hidden : Private) (random : DutyFreeProgram.Randomness hidden)
    (hot : HotKeys) (fake : PlainPads) (index : Table) : DutyFreeTables.Table :=
  let params := CosetScheme.mapParams hidden random (mapOf index) (kindOf index)
  DutyFreeTables.garble (masks hash input hot fake index) params.coefficient params.constant

def garble (hash : Hash) (input : Input) (hidden : Private) (random : DutyFreeProgram.Randomness hidden)
    (active : Active) (hot : HotKeys) (bridgePads : BridgePads) (plainPads : PlainPads) :
    DutyFreeProgram.Artifact :=
  DutyFreeArtifact.ofParts (bridge hash input active hot bridgePads)
    (table hash input hidden random hot plainPads)

theorem externalBit_selected (input : Input) (id : Fin 128) (bit : Bit) (cell : Cell) :
    externalBit input (id,cell,bit) = DutyFreeBridge.bit (selectedCell input id) bit :=
  (bit_wire input (bridgeSide id) (bridgeChunk id) bit).symm

theorem bridge_independent (hash : Hash) (input : Input) (active : Active)
    (source target : HotKeys) (fake : BridgePads)
    (he : ∀ id cell, cell ≠ selectedCell input id → source id cell = target id cell) :
    bridge hash input active source fake = bridge hash input active target fake := by
  funext id
  apply congrArg DutyFreeProgram.packBridge
  funext cell bit
  split
  · rename_i hb
    have hc : cell ≠ selectedCell input id := by
      intro hc
      subst cell
      rw [externalBit_selected] at hb
      exact (Bool.not_eq_self _).mp hb
    rw [he id cell hc]
  · rfl

theorem masks_independent (hash : Hash) (input : Input) (source target : HotKeys)
    (fake : PlainPads)
    (he : ∀ id cell, cell ≠ selectedCell input id → source id cell = target id cell) :
    masks hash input source fake = masks hash input target fake := by
  funext table chunk cell
  unfold masks
  split
  · rfl
  · rename_i hc
    rw [he (bridgeId (sideFor table) chunk) cell (by
      simpa only [selectedCell, bridgeSide_id, bridgeChunk_id] using hc)]

theorem garble_independent (hash : Hash) (input : Input) (hidden : Private)
    (random : DutyFreeProgram.Randomness hidden) (active : Active) (source target : HotKeys)
    (bridgePads : BridgePads) (plainPads : PlainPads)
    (he : ∀ id cell, cell ≠ selectedCell input id → source id cell = target id cell) :
    garble hash input hidden random active source bridgePads plainPads =
      garble hash input hidden random active target bridgePads plainPads := by
  unfold garble
  apply congrArg₂ DutyFreeArtifact.ofParts
  · exact bridge_independent hash input active source target bridgePads he
  · funext index
    unfold table
    rw [masks_independent hash input source target plainPads he]

end G1Release.Submission.DutyFreeIdeal
