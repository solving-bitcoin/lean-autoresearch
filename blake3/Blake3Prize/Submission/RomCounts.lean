import Blake3Prize.Submission.RomAdder
import Blake3Prize.Submission.RomParallel

namespace Blake3Prize.Submission.RomCounts
open RomProgram

def nodes : RomProgram.Program n m → Nat
  | .done _ => 0
  | .step _ tail => 1+nodes tail

@[simp] theorem nodes_rewire (program : RomProgram.Program n k) (wires : Fin n → Fin m) :
    nodes (program.rewire wires) = nodes program := by
  induction program generalizing m with
  | done _ => rfl
  | step _ tail ih => simp [RomProgram.Program.rewire,nodes,ih]

@[simp] theorem nodes_comp (left : RomProgram.Program n m) (right : RomProgram.Program m k) :
    nodes (left.comp right) = nodes left+nodes right := by
  induction left with
  | done output => simp [RomProgram.Program.comp,nodes]
  | step gate tail ih => simp [RomProgram.Program.comp,nodes,ih,Nat.add_assoc]

@[simp] theorem nodes_keepOne (program : RomProgram.Program n m) (wire : Fin n) :
    nodes (program.keepOne wire) = nodes program := by
  induction program with
  | done _ => rfl
  | step _ tail ih => simp [RomProgram.Program.keepOne,nodes,ih]

@[simp] theorem nodes_keep (program : RomProgram.Program n m) (wires : Vector (Fin n) k) :
    nodes (program.keep wires) = nodes program := by
  induction program with
  | done _ => rfl
  | step _ tail ih => simp [RomProgram.Program.keep,nodes,ih]

@[simp] theorem nodes_identity (n : Nat) : nodes (identity n) = 0 := rfl

theorem nodes_fullAdder (a b c : Fin n) : nodes (RomAdder.fullAdder a b c) = 5 := rfl

theorem nodes_ripple (a b : Vector (Fin n) w) (c : Fin n) :
    nodes (RomAdder.ripple a b c) = 5*w := by
  induction w generalizing n with
  | zero => rfl
  | succ w ih =>
    simp [RomAdder.ripple,nodes_comp,nodes_fullAdder,ih,Nat.mul_add,Nat.add_comm]

theorem nodes_parallel (gates : Vector (RomCircuit.Gate n) k) :
    nodes (RomParallel.parallel gates) = k := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih => simp [RomParallel.parallel,nodes,ih,Nat.add_comm]

theorem nodes_xorWords (a b : Vector (Fin n) w) : nodes (RomParallel.xorWords a b) = w :=
  nodes_parallel _

end Blake3Prize.Submission.RomCounts
