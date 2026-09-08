import G1Release.Submission.DutyFreeChunks
import G1Release.Submission.OracleAddress
import G1Release.Submission.CosetHintMap

/-! Public indices and fixed oracle frames. Bridge purposes are below 128;
plain-field purposes start at 8,192. Both integer fields fit the already
proved 16-bit injectivity bounds of the existing 48-byte oracle address. -/
namespace G1Release.Submission.DutyFreeLayout
open GarblingPrize.Protected G1Release.Protected

abbrev Side := Fin 2
abbrev Chunk := Fin 64
abbrev Cell := Fin 16
abbrev Bit := Fin 4
abbrev Table := Fin 728

def bridgeId (side : Side) (chunk : Chunk) : Fin 128 :=
  ⟨side.val*64+chunk.val, by have := side.isLt; have := chunk.isLt; omega⟩

def bridgeSide (id : Fin 128) : Side := ⟨id.val/64, by have := id.isLt; omega⟩
def bridgeChunk (id : Fin 128) : Chunk := ⟨id.val%64, Nat.mod_lt _ (by decide)⟩

@[simp] theorem bridgeSide_id (side : Side) (chunk : Chunk) :
    bridgeSide (bridgeId side chunk) = side := by
  apply Fin.ext
  dsimp [bridgeSide, bridgeId]
  omega

@[simp] theorem bridgeChunk_id (side : Side) (chunk : Chunk) :
    bridgeChunk (bridgeId side chunk) = chunk := by
  apply Fin.ext
  dsimp [bridgeChunk, bridgeId]
  omega

def wire (side : Side) (chunk : Chunk) (bit : Bit) : Fin 512 :=
  ⟨side.val*256+chunk.val*4+bit.val,
    by have := side.isLt; have := chunk.isLt; have := bit.isLt; omega⟩

def tableId (map : Fin 91) (kind : Fin 8) : Table :=
  ⟨map.val*8+kind.val, by have := map.isLt; have := kind.isLt; omega⟩

def mapOf (table : Table) : Fin 91 := ⟨table.val/8, by have := table.isLt; omega⟩
def kindOf (table : Table) : Fin 8 := ⟨table.val%8, Nat.mod_lt _ (by decide)⟩

@[simp] theorem mapOf_tableId (map : Fin 91) (kind : Fin 8) : mapOf (tableId map kind) = map := by
  apply Fin.ext
  dsimp [mapOf, tableId]
  omega

@[simp] theorem kindOf_tableId (map : Fin 91) (kind : Fin 8) : kindOf (tableId map kind) = kind := by
  apply Fin.ext
  dsimp [kindOf, tableId]
  omega

def sideFor (table : Table) : Side :=
  if (kindOf table).val = 4 ∨ (kindOf table).val = 5 then 1 else 0

def coordinate (input : Input) (side : Side) : CanonicalFq :=
  if side = 0 then input.val.1 else input.val.2

def inputCell (input : Input) (side : Side) (chunk : Chunk) : Cell :=
  DutyFreeChunks.value (coordinate input side).val chunk

theorem bit_wire (input : Input) (side : Side) (chunk : Chunk) (bit : Bit) :
    DutyFreeBridge.bit (inputCell input side chunk) bit =
      (inputCodec.encode input)[(wire side chunk bit).val] := by
  rw [BoundaryFacts.input_encode]
  unfold inputCell
  rw [DutyFreeChunks.bit_order]
  have h : chunk.val*4+bit.val < 256 := by have := chunk.isLt; have := bit.isLt; omega
  have hn : ¬256+chunk.val*4+bit.val < 256 := by omega
  fin_cases side <;>
    simp [coordinate, wire, encodeInput, h, hn, Nat.mul_comm, Nat.add_assoc]

theorem field_coordinate (input : Input) (map : Fin 91) (kind : Fin 8) :
    ((coordinate input (sideFor (tableId map kind))).val : BN254.Fq) =
      CosetHintMap.inputFor kind (input.val.1.val : BN254.Fq) (input.val.2.val : BN254.Fq) := by
  simp only [sideFor, kindOf_tableId, coordinate, CosetHintMap.inputFor]
  split <;> simp_all

def bridgePurpose (side : Side) (chunk : Chunk) : Nat := (bridgeId side chunk).val
def bridgeRow (cell : Cell) (bit : Bit) : Nat := cell.val*4+bit.val
def plainPurpose (table : Table) (chunk : Chunk) : Nat := 8192+table.val*64+chunk.val
def plainRow (cell : Cell) (half : Fin 2) : Nat := cell.val*2+half.val

theorem bridgePurpose_lt (side : Side) (chunk : Chunk) : bridgePurpose side chunk < 65536 := by
  have := (bridgeId side chunk).isLt
  dsimp [bridgePurpose]
  omega

theorem bridgeRow_lt (cell : Cell) (bit : Bit) : bridgeRow cell bit < 65536 := by
  have := cell.isLt; have := bit.isLt
  dsimp [bridgeRow]
  omega

theorem plainPurpose_lt (table : Table) (chunk : Chunk) : plainPurpose table chunk < 65536 := by
  have := table.isLt; have := chunk.isLt
  dsimp [plainPurpose]
  omega

theorem plainRow_lt (cell : Cell) (half : Fin 2) : plainRow cell half < 65536 := by
  have := cell.isLt; have := half.isLt
  dsimp [plainRow]
  omega

end G1Release.Submission.DutyFreeLayout
