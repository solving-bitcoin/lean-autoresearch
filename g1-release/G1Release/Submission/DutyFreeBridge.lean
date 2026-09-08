import GarblingPrize.Protected.Bytes
import G1Release.Submission.DutyFreeOneHot

/-! Four known bits are converted to a one-hot disclosure pattern. A fresh
32-byte key belongs to each of the 16 cells. Cell j is encrypted once under
each input label for a bit that differs from j. Thus every cell except the
selected one can be opened. This bridge uses independent keys and fixed
oracle addresses; it does not need a global Free-XOR correlation. -/
namespace G1Release.Submission.DutyFreeBridge
open GarblingPrize.Protected

abbrev Label := Bytes 32
abbrev Cell := Fin 16
abbrev Bit := Fin 4
abbrev Keys := Bit → Bool → Label
abbrev HotKeys := Cell → Label
abbrev Hash := Cell → Bit → Label → Label
abbrev Artifact := Cell → Bit → Label

def bit (value : Cell) (i : Bit) : Bool := value.val.testBit i.val

def mismatch (input cell : Cell) : Bit :=
  if bit input 0 != bit cell 0 then 0
  else if bit input 1 != bit cell 1 then 1
  else if bit input 2 != bit cell 2 then 2
  else 3

theorem mismatch_correct : ∀ input cell : Cell, input ≠ cell →
    bit input (mismatch input cell) = !bit cell (mismatch input cell) := by decide

def garble (hash : Hash) (keys : Keys) (hot : HotKeys) : Artifact :=
  fun cell i => Bytes.xor (hot cell) (hash cell i (keys i (!bit cell i)))

def reveal (hash : Hash) (artifact : Artifact) (input : Cell)
    (active : Bit → Label) (cell : Cell) : Label :=
  let i := mismatch input cell
  Bytes.xor (artifact cell i) (hash cell i (active i))

/-- The selected cell is deliberately excluded from this theorem. -/
theorem reveal_correct (hash : Hash) (keys : Keys) (hot : HotKeys) (input cell : Cell)
    (h : cell ≠ input) :
    reveal hash (garble hash keys hot) input (fun i => keys i (bit input i)) cell = hot cell := by
  dsimp only [reveal, garble]
  rw [mismatch_correct input cell (Ne.symm h), Bytes.xor_cancel_right]

def available {G : Type*} [Zero G] (hash : Hash) (artifact : Artifact) (input : Cell)
    (active : Bit → Label) (pad : Cell → Label → G) : Cell → G :=
  fun cell => if cell = input then 0 else pad cell (reveal hash artifact input active cell)

theorem available_correct {G : Type*} [Zero G] (hash : Hash) (keys : Keys) (hot : HotKeys)
    (input : Cell) (pad : Cell → Label → G) (cell : Cell) (h : cell ≠ input) :
    available hash (garble hash keys hot) input (fun i => keys i (bit input i)) pad cell =
      pad cell (hot cell) := by
  simp only [available, if_neg h, reveal_correct hash keys hot input cell h]

def byteCount : Nat := 16*4*32
theorem byteCount_eq : byteCount = 2048 := by decide

end G1Release.Submission.DutyFreeBridge
