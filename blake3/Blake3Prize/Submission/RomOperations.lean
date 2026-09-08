import Blake3Prize.Submission.RomRegisters
import Blake3Prize.Submission.RomCounts

namespace Blake3Prize.Submission.RomOperations
open RomRegisters RomProgram RomCounts

/-- A state operation carries its semantic function and exact circuit cost.
Composition combines the checked operations without re-proving gate facts. -/
structure Operation where
  run : State → State
  program : StateProgram
  correct : ∀ state, program.eval (encoding state) = encoding (run state)
  cost : Nat
  count : nodes program = cost

def identity : Operation where
  run := id
  program := RomProgram.identity 1025
  correct state := eval_identity (encoding state)
  cost := 0
  count := rfl

def Operation.then (left right : Operation) : Operation where
  run state := right.run (left.run state)
  program := left.program.comp right.program
  correct state := by rw [eval_comp,left.correct,right.correct]
  cost := left.cost+right.cost
  count := by rw [nodes_comp,left.count,right.count]

def add (target left right : Fin 32) : Operation where
  run state := state.set target (state.get left + state.get right)
  program := RomRegisters.add target left right
  correct state := eval_add state target left right
  cost := 160
  count := by simp [RomRegisters.add,write,nodes,nodes_ripple]

def xor (target left right : Fin 32) : Operation where
  run state := state.set target (state.get left ^^^ state.get right)
  program := RomRegisters.xor target left right
  correct state := eval_xor state target left right
  cost := 32
  count := by simp [RomRegisters.xor,write,nodes,nodes_xorWords]

def rotate (target source : Fin 32) (offset : Nat) : Operation where
  run state := state.set target ((state.get source).rotateRight offset)
  program := RomRegisters.rotate target source offset
  correct state := eval_rotate state target source offset
  cost := 0
  count := by simp [RomRegisters.rotate,write,nodes]

def sequence (operations : List Operation) : Operation :=
  operations.foldr Operation.then identity

theorem run_sequence (operations : List Operation) (state : State) :
    (sequence operations).run state = operations.foldl (fun s op => op.run s) state := by
  induction operations generalizing state with
  | nil => rfl
  | cons op tail ih =>
    change (sequence tail).run (op.run state) = _
    exact ih _

end Blake3Prize.Submission.RomOperations
