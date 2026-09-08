import G1Release.Submission.DutyFreeIdeal

/-! A single fixed-address programming experiment covers both bridge pads
and the selected plain pads. Its oracle marginal is exactly the protected
random-function law. The separate query argument must account for observing
one of these programmed addresses. -/
namespace G1Release.Submission.DutyFreeRealIdeal
open SecretRelease G1Release.Protected GarblingPrize.Protected
open DutyFreeLayout DutyFreeSlots
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

abbrev ExtendedOracle := List (Fin 256) ⊕ Slot → Label

def payload (hot : HotKeys) : Slot → Label
  | .inl slot => hot slot.1 slot.2.1
  | .inr _ => Bytes.zero 32

noncomputable def programmed (keys : Keys) (hot : HotKeys) (input : Input)
    (oracle : ExtendedOracle) : ROM.Oracle :=
  OracleLaw.program (address keys hot input) (payload hot) oracle

def base (oracle : ExtendedOracle) : ROM.Oracle := fun q => oracle (.inl q)
def bridgePads (oracle : ExtendedOracle) : DutyFreeIdeal.BridgePads :=
  fun slot => oracle (.inr (.inl slot))
def plainPads (oracle : ExtendedOracle) : DutyFreeIdeal.PlainPads :=
  fun table chunk => (oracle (.inr (.inr (table,chunk,0))), oracle (.inr (.inr (table,chunk,1))))
def active (keys : Keys) (input : Input) : DutyFreeIdeal.Active :=
  fun wire => (keys wire).get (inputCodec.encode input)[wire.val]

theorem oracle_preserving (keys : Keys) (hot : HotKeys) (input : Input) :
    MeasureTheory.MeasurePreserving (programmed keys hot input)
      (OracleLaw.law (List (Fin 256) ⊕ Slot)) (OracleLaw.law (List (Fin 256))) :=
  OracleLaw.program_preserving _ _

theorem bridge_pad (keys : Keys) (hot : HotKeys) (input : Input) (oracle : ExtendedOracle)
    (slot : BridgeSlot) (branch : Bool) :
    AffineTable.pad (ROM.hash (programmed keys hot input oracle))
        ((keys (externalWire slot)).get branch) slot.1.val (bridgeRow slot.2.1 slot.2.2) =
      if branch = externalBit input slot then
        AffineTable.pad (ROM.hash (base oracle)) (active keys input (externalWire slot))
          slot.1.val (bridgeRow slot.2.1 slot.2.2)
      else Bytes.xor (hot slot.1 slot.2.1) (bridgePads oracle slot) := by
  by_cases hb : branch = externalBit input slot
  · rw [if_pos hb, hb]
    exact OracleLaw.program_outside _ _ _ _ (active_bridge_outside keys hot input slot)
  · rw [if_neg hb]
    have hn : branch = !(externalBit input slot) := by
      cases branch <;> cases hbit : externalBit input slot <;> simp_all
    rw [hn]
    exact OracleLaw.program_at _ (address_injective keys hot input) _ oracle (.inl slot)

theorem plain_pad (keys : Keys) (hot : HotKeys) (input : Input) (oracle : ExtendedOracle)
    (table : Table) (chunk : Chunk) (cell : Cell) (half : Fin 2) :
    AffineTable.pad (ROM.hash (programmed keys hot input oracle))
        (hot (bridgeId (sideFor table) chunk) cell) (plainPurpose table chunk) (plainRow cell half) =
      if cell = inputCell input (sideFor table) chunk then oracle (.inr (.inr (table,chunk,half)))
      else AffineTable.pad (ROM.hash (base oracle))
        (hot (bridgeId (sideFor table) chunk) cell) (plainPurpose table chunk) (plainRow cell half) := by
  by_cases hc : cell = inputCell input (sideFor table) chunk
  · rw [if_pos hc, hc]
    change OracleLaw.program (address keys hot input) (payload hot) oracle
      (plainQuery (hot (bridgeId (sideFor table) chunk) (inputCell input (sideFor table) chunk))
        table chunk (inputCell input (sideFor table) chunk) half) = _
    rw [← address_plain, OracleLaw.program_at _ (address_injective keys hot input)]
    exact Bytes.zero_xor _
  · rw [if_neg hc]
    change OracleLaw.program (address keys hot input) (payload hot) oracle
      (plainQuery (hot (bridgeId (sideFor table) chunk) cell) table chunk cell half) =
        oracle (.inl (plainQuery (hot (bridgeId (sideFor table) chunk) cell) table chunk cell half))
    exact OracleLaw.program_outside (address keys hot input) (payload hot) oracle
      (plainQuery (hot (bridgeId (sideFor table) chunk) cell) table chunk cell half)
      (unselected_plain_outside keys hot input table chunk cell half
        (hot (bridgeId (sideFor table) chunk) cell) hc)

theorem masks_programmed (keys : Keys) (hot : HotKeys) (input : Input) (oracle : ExtendedOracle) :
    DutyFreeProgram.masks (ROM.hash (programmed keys hot input oracle)) hot =
      DutyFreeIdeal.masks (ROM.hash (base oracle)) input hot (plainPads oracle) := by
  funext table chunk cell
  simp only [DutyFreeProgram.masks, DutyFreeProgram.fieldPad, plain_pad, DutyFreeIdeal.masks]
  split <;> rfl

theorem bridge_programmed (keys : Keys) (hot : HotKeys) (input : Input) (oracle : ExtendedOracle) :
    DutyFreeProgram.garbleBridge (ROM.hash (programmed keys hot input oracle)) keys hot =
      DutyFreeIdeal.bridge (ROM.hash (base oracle)) input (active keys input) hot (bridgePads oracle) := by
  funext id
  unfold DutyFreeProgram.garbleBridge DutyFreeIdeal.bridge
  apply congrArg DutyFreeProgram.packBridge
  funext cell bit
  simp only [DutyFreeBridge.garble, DutyFreeProgram.bridgeHash, DutyFreeProgram.bridgeKeys,
    bridgePurpose, bridgeId_side_chunk]
  have hp := bridge_pad keys hot input oracle (id,cell,bit) (!DutyFreeBridge.bit cell bit)
  dsimp only [externalWire] at hp
  rw [hp]
  split
  · rfl
  · exact Bytes.xor_cancel_left _ _

theorem garble_programmed (keys : Keys) (hot : HotKeys) (input : Input) (oracle : ExtendedOracle)
    (hidden : Private) (random : DutyFreeProgram.Randomness hidden) :
    DutyFreeProgram.garble (ROM.hash (programmed keys hot input oracle)) hidden random keys hot =
      DutyFreeIdeal.garble (ROM.hash (base oracle)) input hidden random
        (active keys input) hot (bridgePads oracle) (plainPads oracle) := by
  unfold DutyFreeProgram.garble DutyFreeIdeal.garble
  apply congrArg₂ DutyFreeArtifact.ofParts
  · funext id
    rw [Vector.get_ofFn]
    exact congrFun (bridge_programmed keys hot input oracle) id
  · funext table
    rw [Vector.get_ofFn]
    unfold DutyFreeProgram.garbleTable DutyFreeIdeal.table
    rw [masks_programmed]

end G1Release.Submission.DutyFreeRealIdeal
