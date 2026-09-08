import G1Release.Submission.DutyFreeWords
import G1Release.Submission.DutyFreeChunks
import G1Release.Submission.DutyFreeNaturalSums
import G1Release.Submission.AffineTable

/-! Sixty-four plain joins plus one decoding field word. Both garbling and
evaluation cache each row's pad values so hashing is not repeated by sums. -/
namespace G1Release.Submission.DutyFreeTables
open scoped BigOperators
open DutyFreeOneHot
open GarblingPrize.Protected
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

abbrev Word := BN254.Fq
abbrev Chunk := Fin 64
abbrev Cell := Fin 16
abbrev Masks := Chunk → Cell → Word
abbrev Table := DutyFreeWords.Block 65

def pack (artifact : DutyFreeChunkAffine.Artifact Word 64) : Table :=
  Vector.ofFn fun i => if h : i.val = 0 then AffineTable.encodeWord artifact.decoding
    else AffineTable.encodeWord (artifact.joins ⟨i.val-1, by have := i.isLt; omega⟩)

@[simp] theorem pack_first (artifact : DutyFreeChunkAffine.Artifact Word 64) :
    (pack artifact).get 0 = AffineTable.encodeWord artifact.decoding := by simp [pack]

@[simp] theorem pack_join (artifact : DutyFreeChunkAffine.Artifact Word 64) (i : Chunk) :
    (pack artifact).get i.succ = AffineTable.encodeWord (artifact.joins i) := by
  simp [pack]

/-- Accumulate canonical representatives as arbitrary-precision integers,
then reduce once, instead of reducing every addition and multiplication. -/
def fieldWeighted (values : Cell → Word) : Word := DutyFreeNaturalSums.weighted values

theorem fieldWeighted_eq (values : Cell → Word) :
    fieldWeighted values = weighted Fin.val values := by
  exact DutyFreeNaturalSums.weighted_eq values

/-- These public powers are shared by every one of the 728 tables. -/
def weights : Vector Word 64 := Vector.ofFn DutyFreeChunks.weight

@[simp] theorem weights_get (chunk : Chunk) : weights.get chunk = DutyFreeChunks.weight chunk :=
  Vector.get_ofFn DutyFreeChunks.weight chunk

def garble (masks : Masks) (coefficient constant : Word) : Table :=
  let rows := Vector.ofFn fun c => Vector.ofFn (masks c)
  pack ⟨fun c => DutyFreeNaturalSums.sum (rows.get c).get + weights.get c * coefficient,
    (∑ c, fieldWeighted (rows.get c).get) - constant⟩

theorem garble_eq (masks : Masks) (coefficient constant : Word) :
    garble masks coefficient constant =
      pack (DutyFreeChunkAffine.garble DutyFreeChunks.weight masks coefficient constant) := by
  have h (c : Chunk) : (Vector.ofFn (masks c)).get = masks c := by
    funext i
    exact Vector.get_ofFn (masks c) i
  simp only [garble, fieldWeighted_eq, DutyFreeNaturalSums.sum_eq,
    DutyFreeChunkAffine.garble, join, Vector.get_ofFn, h, weights_get]

def evaluateChunk (input : Cell) (available : Cell → Word) (material : Word) : Word :=
  let row := Vector.ofFn available
  let total := DutyFreeNaturalSums.sum row.get
  fieldWeighted (fun cell => if cell = input then material - (total - row.get input)
    else row.get cell)

theorem evaluateChunk_eq (input : Cell) (available : Cell → Word) (material : Word) :
    evaluateChunk input available material = weighted Fin.val (recover available input material) := by
  have h : (Vector.ofFn available).get = available := by funext i; simp
  simp only [evaluateChunk, fieldWeighted_eq, h, DutyFreeNaturalSums.without_eq]
  rfl

def evaluateList (table : Table) (input : Chunk → Cell) (available : Masks) :
    List Chunk → Option Word
  | [] => some 0
  | chunk :: rest => do
    let material ← AffineTable.decodeWord (table.get chunk.succ)
    let tail ← evaluateList table input available rest
    pure (evaluateChunk (input chunk) (available chunk) material + tail)

def evaluate (table : Table) (input : Chunk → Cell) (available : Masks) : Option Word := do
  let decoding ← AffineTable.decodeWord (table.get 0)
  let value ← evaluateList table input available (List.finRange 64)
  pure (value-decoding)

theorem evaluateList_pack (artifact : DutyFreeChunkAffine.Artifact Word 64)
    (input : Chunk → Cell) (available : Masks) (chunks : List Chunk) :
    evaluateList (pack artifact) input available chunks =
      some (chunks.foldr (fun c rest =>
        weighted Fin.val (recover (available c) (input c) (artifact.joins c)) + rest) 0) := by
  induction chunks with
  | nil => rfl
  | cons chunk rest ih =>
    rw [evaluateList, pack_join, AffineTable.decodeWord_encodeWord, ih]
    simp only [Option.bind, bind, Option.pure_def, evaluateChunk_eq, List.foldr_cons]

theorem fold_finRange {count : Nat} (values : Fin count → Word) :
    (List.finRange count).foldr (fun i rest => values i + rest) 0 = ∑ i, values i := by
  induction count with
  | zero => simp
  | succ count ih =>
    rw [List.finRange_succ, List.foldr_cons, List.foldr_map, Fin.sum_univ_succ]
    exact congrArg (values 0 + ·) (ih (values := fun i => values i.succ))

theorem evaluate_pack (artifact : DutyFreeChunkAffine.Artifact Word 64)
    (input : Chunk → Cell) (available : Masks) :
    evaluate (pack artifact) input available =
      some (DutyFreeChunkAffine.evaluate artifact input available) := by
  rw [evaluate, pack_first, AffineTable.decodeWord_encodeWord, evaluateList_pack]
  simp only [Option.bind, bind, Option.pure_def, fold_finRange, DutyFreeChunkAffine.evaluate]

theorem correct (masks available : Masks) (coefficient constant coordinate : Word)
    (h : ∀ chunk cell, cell ≠ DutyFreeChunks.value coordinate.val chunk →
      available chunk cell = masks chunk cell) :
    evaluate (garble masks coefficient constant) (DutyFreeChunks.value coordinate.val) available =
      some (coefficient*coordinate+constant) := by
  rw [garble_eq, evaluate_pack, DutyFreeChunkAffine.correct _ _ _ _ _ _ h,
    DutyFreeChunks.reconstruct]

end G1Release.Submission.DutyFreeTables
