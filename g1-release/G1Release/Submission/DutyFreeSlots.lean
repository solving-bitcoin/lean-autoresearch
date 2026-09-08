import G1Release.Submission.DutyFreeProgram
import G1Release.Submission.OracleLaw

/-! Every programmed oracle coordinate has a fixed, injective public frame.
The hidden key in a frame is either an opposite Lamport label or the one
unreleased bridge key. Equal labels on different wires cannot alias frames. -/
namespace G1Release.Submission.DutyFreeSlots
open SecretRelease G1Release.Protected
open DutyFreeLayout

abbrev BridgeSlot := Fin 128 × Cell × Bit
abbrev PlainSlot := Table × Chunk × Fin 2
abbrev Slot := BridgeSlot ⊕ PlainSlot
abbrev Keys := DutyFreeProgram.Keys
abbrev HotKeys := DutyFreeProgram.HotKeys

def selectedCell (input : Input) (id : Fin 128) : Cell :=
  inputCell input (bridgeSide id) (bridgeChunk id)

def externalWire (slot : BridgeSlot) : Fin 512 :=
  wire (bridgeSide slot.1) (bridgeChunk slot.1) slot.2.2

def externalBit (input : Input) (slot : BridgeSlot) : Bool :=
  (inputCodec.encode input)[(externalWire slot).val]

def hotId (slot : PlainSlot) : Fin 128 := bridgeId (sideFor slot.1) slot.2.1

def purpose : Slot → Nat
  | .inl slot => slot.1.val
  | .inr slot => plainPurpose slot.1 slot.2.1

def row (input : Input) : Slot → Nat
  | .inl slot => bridgeRow slot.2.1 slot.2.2
  | .inr slot => plainRow (selectedCell input (hotId slot)) slot.2.2

def secret (keys : Keys) (hot : HotKeys) (input : Input) : Slot → Label
  | .inl slot => (keys (externalWire slot)).get (!(externalBit input slot))
  | .inr slot => hot (hotId slot) (selectedCell input (hotId slot))

def address (keys : Keys) (hot : HotKeys) (input : Input) (slot : Slot) : List (Fin 256) :=
  OracleAddress.query (secret keys hot input slot) (purpose slot) (row input slot)

theorem bridgeId_side_chunk (id : Fin 128) : bridgeId (bridgeSide id) (bridgeChunk id) = id := by
  apply Fin.ext
  simp only [bridgeId, bridgeSide, bridgeChunk]
  omega

@[simp] theorem selectedCell_hotId (input : Input) (slot : PlainSlot) :
    selectedCell input (hotId slot) = inputCell input (sideFor slot.1) slot.2.1 := by
  simp only [selectedCell, hotId, bridgeSide_id, bridgeChunk_id]

theorem purpose_lt (slot : Slot) : purpose slot < 65536 := by
  rcases slot with slot | slot
  · have := slot.1.isLt
    dsimp [purpose]
    omega
  · exact plainPurpose_lt _ _

theorem row_lt (input : Input) (slot : Slot) : row input slot < 65536 := by
  rcases slot with slot | slot
  · exact bridgeRow_lt _ _
  · exact plainRow_lt _ _

theorem frame_injective (input : Input) {a b : Slot}
    (hp : purpose a = purpose b) (hr : row input a = row input b) : a = b := by
  rcases a with ⟨id,cell,bit⟩ | ⟨table,chunk,half⟩ <;>
    rcases b with ⟨id',cell',bit'⟩ | ⟨table',chunk',half'⟩
  all_goals dsimp [purpose, row, bridgeRow, plainPurpose, plainRow] at hp hr
  · apply congrArg Sum.inl
    exact Prod.ext (Fin.ext hp) (Prod.ext (Fin.ext (by dsimp; omega)) (Fin.ext (by dsimp; omega)))
  · have := id.isLt
    omega
  · have := id'.isLt
    omega
  · apply congrArg Sum.inr
    exact Prod.ext (Fin.ext (by dsimp; omega))
      (Prod.ext (Fin.ext (by dsimp; omega)) (Fin.ext (by dsimp; omega)))

theorem address_injective (keys : Keys) (hot : HotKeys) (input : Input) :
    Function.Injective (address keys hot input) := by
  intro a b h
  have hh := OracleAddress.query_injective (purpose_lt a) (purpose_lt b)
    (row_lt input a) (row_lt input b) h
  exact frame_injective input hh.2.1 hh.2.2

def bridgeQuery (key : Label) (slot : BridgeSlot) : List (Fin 256) :=
  OracleAddress.query key slot.1.val (bridgeRow slot.2.1 slot.2.2)

def plainQuery (key : Label) (table : Table) (chunk : Chunk) (cell : Cell)
    (half : Fin 2) : List (Fin 256) :=
  OracleAddress.query key (plainPurpose table chunk) (plainRow cell half)

theorem address_plain (keys : Keys) (hot : HotKeys) (input : Input)
    (table : Table) (chunk : Chunk) (half : Fin 2) :
    address keys hot input (.inr (table,chunk,half)) =
      plainQuery (hot (bridgeId (sideFor table) chunk) (inputCell input (sideFor table) chunk))
        table chunk (inputCell input (sideFor table) chunk) half := by
  unfold address
  simp only [secret, purpose, row, hotId, selectedCell, bridgeSide_id, bridgeChunk_id]
  rfl

theorem active_bridge_outside (keys : Keys) (hot : HotKeys) (input : Input) (slot : BridgeSlot) :
    ¬∃ other, address keys hot input other =
      bridgeQuery ((keys (externalWire slot)).get (externalBit input slot)) slot := by
  rintro ⟨other,h⟩
  have hh := OracleAddress.query_injective (purpose_lt other) (purpose_lt (.inl slot))
    (row_lt input other) (row_lt input (.inl slot)) h
  have he := frame_injective input hh.2.1 hh.2.2
  subst other
  have hn := hh.1
  dsimp only [secret] at hn
  cases hb : externalBit input slot <;>
    simp_all [BoundaryFacts.get_false, BoundaryFacts.get_true, (keys (externalWire slot)).property,
      (keys (externalWire slot)).property.symm]

theorem unselected_plain_outside (keys : Keys) (hot : HotKeys) (input : Input)
    (table : Table) (chunk : Chunk) (cell : Cell) (half : Fin 2) (key : Label)
    (hc : cell ≠ inputCell input (sideFor table) chunk) :
    ¬∃ other, address keys hot input other = plainQuery key table chunk cell half := by
  rintro ⟨other,h⟩
  have hh := OracleAddress.query_injective (purpose_lt other) (plainPurpose_lt table chunk)
    (row_lt input other) (plainRow_lt cell half) h
  rcases other with ⟨id,cell',bit⟩ | ⟨table',chunk',half'⟩
  · have := id.isLt
    have hp := hh.2.1
    dsimp [purpose, plainPurpose] at hp
    omega
  · have hp := hh.2.1
    dsimp [purpose, plainPurpose] at hp
    have ht : table' = table := Fin.ext (by omega)
    have hk : chunk' = chunk := Fin.ext (by omega)
    subst table'; subst chunk'
    have hr := hh.2.2
    simp only [row, selectedCell_hotId, plainRow] at hr
    apply hc
    exact Fin.ext (by omega)

end G1Release.Submission.DutyFreeSlots
