import G1Release.Submission.DutyFreeArtifact
import G1Release.Submission.DutyFreeLayout
import G1Release.Submission.DutyFreeFieldPad
import G1Release.Submission.DutyFreeTables
import G1Release.Submission.CosetCorrect

/-! The concrete direct-field duty-free garbler and evaluator. One bridge
per coordinate nibble serves every affine opening. The existing complete
91-map G1 construction supplies the private coefficients and recomposition. -/
namespace G1Release.Submission.DutyFreeProgram
open SecretRelease G1Release.Protected GarblingPrize.Protected
open DutyFreeLayout

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

abbrev Word := BN254.Fq
abbrev Keys := Fin 512 → Pair
abbrev HotKeys := Fin 128 → Cell → Label
abbrev Artifact := DutyFreeArtifact.Artifact
abbrev Randomness (hidden : Private) := CosetRandomness.Randomness hidden

def bridgeHash (hash : Hash) (side : Side) (chunk : Chunk) : DutyFreeBridge.Hash :=
  fun cell bit key => AffineTable.pad hash key (bridgePurpose side chunk) (bridgeRow cell bit)

def fieldPad (hash : Hash) (table : Table) (chunk : Chunk) (cell : Cell) (key : Label) : Word :=
  DutyFreeFieldPad.sample
    (AffineTable.pad hash key (plainPurpose table chunk) (plainRow cell 0),
      AffineTable.pad hash key (plainPurpose table chunk) (plainRow cell 1))

def packBridge (bridge : DutyFreeBridge.Artifact) : DutyFreeWords.Block 64 :=
  Vector.ofFn fun i => bridge ⟨i.val/4, by have := i.isLt; omega⟩
    ⟨i.val%4, Nat.mod_lt _ (by decide)⟩

def unpackBridge (words : DutyFreeWords.Block 64) : DutyFreeBridge.Artifact :=
  fun cell bit => words.get ⟨cell.val*4+bit.val, by have := cell.isLt; have := bit.isLt; omega⟩

theorem unpack_pack_bridge (bridge : DutyFreeBridge.Artifact) :
    unpackBridge (packBridge bridge) = bridge := by
  funext cell bit
  simp only [unpackBridge, packBridge, Vector.get_ofFn]
  congr 1 <;> apply Fin.ext <;> dsimp <;> omega

def bridgeKeys (keys : Keys) (side : Side) (chunk : Chunk) : DutyFreeBridge.Keys :=
  fun bit branch => (keys (wire side chunk bit)).get branch

def garbleBridge (hash : Hash) (keys : Keys) (hot : HotKeys) (id : Fin 128) :
    DutyFreeWords.Block 64 :=
  packBridge (DutyFreeBridge.garble (bridgeHash hash (bridgeSide id) (bridgeChunk id))
    (bridgeKeys keys (bridgeSide id) (bridgeChunk id)) (hot id))

def masks (hash : Hash) (hot : HotKeys) (table : Table) : DutyFreeTables.Masks :=
  fun chunk cell => fieldPad hash table chunk cell (hot (bridgeId (sideFor table) chunk) cell)

def garbleTable (hash : Hash) (hidden : Private) (random : Randomness hidden)
    (hot : HotKeys) (table : Table) : DutyFreeTables.Table :=
  let params := CosetScheme.mapParams hidden random (mapOf table) (kindOf table)
  DutyFreeTables.garble (masks hash hot table) params.coefficient params.constant

def garble (hash : Hash) (hidden : Private) (random : Randomness hidden)
    (keys : Keys) (hot : HotKeys) : Artifact :=
  let bridges := Vector.ofFn (garbleBridge hash keys hot)
  let tables := Vector.ofFn (garbleTable hash hidden random hot)
  DutyFreeArtifact.ofParts bridges.get tables.get

theorem garble_bridge (hash : Hash) (hidden : Private) (random : Randomness hidden)
    (keys : Keys) (hot : HotKeys) (id : Fin 128) :
    DutyFreeArtifact.bridge (garble hash hidden random keys hot) id =
      garbleBridge hash keys hot id := by
  simp only [garble, DutyFreeArtifact.bridge_ofParts, Vector.get_ofFn]

theorem garble_table (hash : Hash) (hidden : Private) (random : Randomness hidden)
    (keys : Keys) (hot : HotKeys) (table : Table) :
    DutyFreeArtifact.table (garble hash hidden random keys hot) table =
      garbleTable hash hidden random hot table := by
  simp only [garble, DutyFreeArtifact.table_ofParts, Vector.get_ofFn]

def activeHotStorage (hash : Hash) (artifact : Artifact) (input : Input) (active : ByteArray) :
    Vector (Vector Label 16) 128 :=
  Vector.ofFn fun id : Fin 128 =>
    let side := bridgeSide id
    let chunk := bridgeChunk id
    let selected := inputCell input side chunk
    let bridge := unpackBridge (DutyFreeArtifact.bridge artifact id)
    Vector.ofFn fun cell : Cell => if cell = selected then Bytes.zero 32 else
      DutyFreeBridge.reveal (bridgeHash hash side chunk) bridge selected
        (fun bit => Scheme.readLabel active (wire side chunk bit)) cell

def activeHot (hash : Hash) (artifact : Artifact) (input : Input) (active : ByteArray) : HotKeys :=
  fun id cell => ((activeHotStorage hash artifact input active).get id).get cell

def available (hash : Hash) (input : Input) (hot : HotKeys) (table : Table) : DutyFreeTables.Masks :=
  fun chunk cell => if cell = inputCell input (sideFor table) chunk then 0 else
    fieldPad hash table chunk cell (hot (bridgeId (sideFor table) chunk) cell)

def evaluateTable (hash : Hash) (artifact : Artifact) (input : Input) (hot : HotKeys)
    (table : Table) : Option Word :=
  let cells := Vector.ofFn (inputCell input (sideFor table))
  DutyFreeTables.evaluate (DutyFreeArtifact.table artifact table)
    cells.get (fun chunk cell => if cell = cells.get chunk then 0 else
      fieldPad hash table chunk cell (hot (bridgeId (sideFor table) chunk) cell))

theorem evaluateTable_eq (hash : Hash) (artifact : Artifact) (input : Input) (hot : HotKeys)
    (table : Table) : evaluateTable hash artifact input hot table =
      DutyFreeTables.evaluate (DutyFreeArtifact.table artifact table)
        (inputCell input (sideFor table)) (available hash input hot table) := by
  have hc : (Vector.ofFn (inputCell input (sideFor table))).get = inputCell input (sideFor table) := by
    funext chunk
    exact Vector.get_ofFn (inputCell input (sideFor table)) chunk
  simp only [evaluateTable, hc]
  rfl

def openings (hash : Hash) (artifact : Artifact) (input : Input) (hot : HotKeys)
    (map : Fin 91) : Option (FourAffineQuotient.Opened CosetCoordinates.K) := do
  let q0 ← evaluateTable hash artifact input hot (tableId map 0)
  let q1 ← evaluateTable hash artifact input hot (tableId map 1)
  let l0 ← evaluateTable hash artifact input hot (tableId map 2)
  let l1 ← evaluateTable hash artifact input hot (tableId map 3)
  let y0 ← evaluateTable hash artifact input hot (tableId map 4)
  let y1 ← evaluateTable hash artifact input hot (tableId map 5)
  let d0 ← evaluateTable hash artifact input hot (tableId map 6)
  let d1 ← evaluateTable hash artifact input hot (tableId map 7)
  pure ⟨⟨q0,q1⟩,⟨l0,l1⟩,⟨y0,y1⟩,⟨d0,d1⟩⟩

def evaluateMap (hash : Hash) (artifact : Artifact) (input : Input) (hot : HotKeys)
    (map : Fin 91) : Option RuntimeG1.Point :=
  CosetScheme.finish (input.val.1.val : Word) (openings hash artifact input hot map)

def evaluateMaps (hash : Hash) (artifact : Artifact) (input : Input) (hot : HotKeys) :
    List (Fin 91) → Option (List RuntimeG1.Point)
  | [] => some []
  | map :: rest => do
    let point ← evaluateMap hash artifact input hot map
    let tail ← evaluateMaps hash artifact input hot rest
    pure (point :: tail)

def evaluate (hash : Hash) (artifact : Artifact) (input : Input) (active : ByteArray) :
    Option ByteArray := do
  if active.size != 16384 then none else do
    let labels := activeHotStorage hash artifact input active
    let hot := fun id cell => (labels.get id).get cell
    let points ← evaluateMaps hash artifact input hot (List.finRange 91)
    match RuntimeG1.recomposeAlpha points with
    | .error _ => none
    | .ok result => some (encodeOutput (RuntimeG1.toOutput result))

end G1Release.Submission.DutyFreeProgram
