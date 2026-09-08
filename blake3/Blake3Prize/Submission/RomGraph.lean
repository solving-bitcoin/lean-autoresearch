import Blake3Prize.Submission.RomCounts
import Blake3Prize.Submission.RomExecution

/-! Public graph facts extracted from the compiler's typed program. Wire
indices increase strictly; the complete trace extends its initial bits and
satisfies every gate equation. These facts connect the concrete evaluator to
the table-level security model. -/
namespace Blake3Prize.Submission.RomGraph
open SecretRelease RomProgram RomCounts

structure Node where
  isAnd : Bool
  left : Nat
  right : Nat
deriving DecidableEq

def Node.function (node : Node) (a b : Bool) : Bool := if node.isAnd then a && b else a ^^ b
def erase (gate : RomCircuit.Gate n) : Node := ⟨gate.isAnd,gate.left.val,gate.right.val⟩

def lookup : RomProgram.Program n m → Nat → Option Node
  | .done _, _ => none
  | .step gate tail, wire => if wire = n then some (erase gate) else lookup tail wire

def outputs : RomProgram.Program n m → Vector Nat m
  | .done wires => wires.map Fin.val
  | .step _ tail => outputs tail

def values : RomProgram.Program n m → Vector Bool n → Nat → Bool
  | .done _, known => fun i => if h : i < n then known.get ⟨i,h⟩ else false
  | .step gate tail, known => values tail
      (known.push (gate.function (known.get gate.left) (known.get gate.right)))

def Consistent : RomProgram.Program n m → (Nat → Bool) → Prop
  | .done _, _ => True
  | .step gate tail, bits =>
      bits n = gate.function (bits gate.left.val) (bits gate.right.val) ∧ Consistent tail bits

theorem values_prefix (program : RomProgram.Program n m) (known : Vector Bool n) (i : Fin n) :
    values program known i.val = known.get i := by
  induction program with
  | done wires => simp [values,i.isLt]
  | step gate tail ih =>
    simpa [values,Vector.get_eq_getElem] using ih
      (known.push (gate.function (known.get gate.left) (known.get gate.right))) i.castSucc

theorem values_consistent (program : RomProgram.Program n m) (known : Vector Bool n) :
    Consistent program (values program known) := by
  induction program with
  | done _ => trivial
  | @step n m gate tail ih =>
    change _ ∧ Consistent tail (values tail _)
    refine ⟨?_,ih _⟩
    change values tail _ n = gate.function (values tail _ gate.left.val) (values tail _ gate.right.val)
    let next := known.push (gate.function (known.get gate.left) (known.get gate.right))
    have h0 := values_prefix tail next (Fin.last n)
    have hl := values_prefix tail next gate.left.castSucc
    have hr := values_prefix tail next gate.right.castSucc
    simp only [Fin.val_last,Fin.val_castSucc] at h0 hl hr
    rw [h0,hl,hr]
    simp [next,Vector.get_eq_getElem]

theorem lookup_bounds (program : RomProgram.Program n m) (wire : Nat) (node : Node)
    (h : lookup program wire = some node) :
    n ≤ wire ∧ wire < n + nodes program ∧ node.left < wire ∧ node.right < wire := by
  induction program with
  | done wires => simp [lookup] at h
  | @step n m gate tail ih =>
    simp only [lookup] at h
    split at h
    · rename_i he
      subst wire
      cases h
      exact ⟨le_rfl,by simp [nodes],gate.left.isLt,gate.right.isLt⟩
    · have hb := ih h
      simp only [nodes]
      omega

theorem lookup_tail (gate : RomCircuit.Gate n) (tail : RomProgram.Program (n+1) m)
    (wire : Nat) (node : Node) (h : lookup tail wire = some node) :
    lookup (.step gate tail) wire = some node := by
  have hb := lookup_bounds tail wire node h
  rw [lookup,if_neg (by omega)]
  exact h

theorem lookup_consistent (program : RomProgram.Program n m) (bits : Nat → Bool)
    (hc : Consistent program bits) (wire : Nat) (node : Node)
    (h : lookup program wire = some node) :
    bits wire = node.function (bits node.left) (bits node.right) := by
  induction program with
  | done wires => simp [lookup] at h
  | step gate tail ih =>
    simp only [lookup] at h
    split at h
    · rename_i he
      subst wire
      cases h
      exact hc.1
    · exact ih hc.2 h

theorem outputs_bound (program : RomProgram.Program n m) (i : Fin m) :
    (outputs program).get i < n + nodes program := by
  induction program with
  | done wires => simpa [outputs,nodes] using (wires.get i).isLt
  | step gate tail ih =>
    have hb := ih i
    simp only [outputs,nodes]
    omega

theorem outputs_values (program : RomProgram.Program n m) (known : Vector Bool n) (i : Fin m) :
    values program known ((outputs program).get i) = (program.eval known).get i := by
  induction program with
  | done wires =>
    simp only [outputs,Vector.get_map,Program.eval]
    exact values_prefix (.done wires) known (wires.get i)
  | step gate tail ih => exact ih _ i

def render (program : RomProgram.Program n m) (tables : Nat → RomGate.Row → Label)
    (translations : Fin m → Bool → Label) : RomExecution.Artifact m :=
  match program with
  | .done _ => ⟨[],Vector.ofFn translations⟩
  | .step _ tail =>
      let rest := render tail tables translations
      ⟨tables n :: rest.gates,rest.translations⟩

theorem garble_render (program : RomProgram.Program n m) (hash : Hash)
    (context : RomCircuit.Context) (outputContext : RomExecution.OutputContext m)
    (keys : Nat → Bool → Label) (out : Fin m → Bool → Label)
    (tables : Nat → RomGate.Row → Label)
    (ht : ∀ wire node, lookup program wire = some node →
      tables wire = RomGate.table hash (context wire) node.function
        (keys node.left) (keys node.right) (keys wire)) :
    RomExecution.garble hash context outputContext keys out program =
      render program tables (fun i => RomGate.translate hash (outputContext i)
        (keys ((outputs program).get i)) (out i)) := by
  induction program with
  | done wires =>
    simp only [RomExecution.garble,render,outputs,Vector.get_map]
  | @step n m gate tail ih =>
    simp only [RomExecution.garble,render,outputs]
    rw [ih outputContext out (fun wire node h => ht wire node (lookup_tail gate tail wire node h))]
    rw [ht n (erase gate) (by simp [lookup])]
    rfl

end Blake3Prize.Submission.RomGraph
