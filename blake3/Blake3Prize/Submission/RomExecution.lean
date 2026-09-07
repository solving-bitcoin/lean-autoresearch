import Blake3Prize.Submission.RomProgram

/-! Complete label-level evaluation, including translation into the supplied
output labels. The evaluator advances public bits and active labels together.
The theorem below is exact for every hash and allows internal key collisions. -/
namespace Blake3Prize.Submission.RomExecution
open SecretRelease RomProgram

structure Artifact (outputs : Nat) where
  gates : List RomCircuit.Table
  translations : Vector (Bool → Label) outputs

abbrev OutputContext (m : Nat) := Fin m → Bool → ByteArray

def garble (hash : Hash) (context : RomCircuit.Context) (outputContext : OutputContext m)
    (keys : Nat → Bool → Label) (outputs : Fin m → Bool → Label) :
    RomProgram.Program n m → Artifact m
  | .done wires => ⟨[],Vector.ofFn fun i =>
      RomGate.translate hash (outputContext i) (keys (wires.get i).val) (outputs i)⟩
  | .step gate tail =>
      let rest := garble hash context outputContext keys outputs tail
      ⟨RomGate.table hash (context n) gate.function
        (keys gate.left.val) (keys gate.right.val) (keys n) :: rest.gates,rest.translations⟩

def evaluate (hash : Hash) (context : RomCircuit.Context) (outputContext : OutputContext m) :
    RomProgram.Program n m → Artifact m → Vector Bool n → Vector Label n → Vector Label m
  | .done wires, artifact, known, active => Vector.ofFn fun i =>
      let wire := wires.get i
      let bit := known.get wire
      RomGate.openTranslation hash (outputContext i bit)
        (artifact.translations.get i bit) (active.get wire)
  | .step gate tail, artifact, known, active =>
      let row := (known.get gate.left,known.get gate.right)
      let ciphertext := (artifact.gates.headD (fun _ => RomBytes.zero 32)) row
      let next := RomGate.evaluate hash (context n row) ciphertext
        (active.get gate.left) (active.get gate.right)
      evaluate hash context outputContext tail ⟨artifact.gates.tail,artifact.translations⟩
        (known.push (gate.function row.1 row.2)) (active.push next)

def selected (keys : Nat → Bool → Label) (known : Vector Bool n) : Vector Label n :=
  Vector.ofFn fun i => keys i.val (known.get i)

@[simp] theorem selected_get (keys : Nat → Bool → Label) (known : Vector Bool n) (i : Fin n) :
    (selected keys known).get i = keys i.val (known.get i) := by simp [selected]

theorem selected_push (keys : Nat → Bool → Label) (known : Vector Bool n) (bit : Bool) :
    (selected keys known).push (keys n bit) = selected keys (known.push bit) := by
  apply Vector.ext
  intro i hi
  by_cases h : i < n
  · simp [selected,Vector.get_eq_getElem,Vector.getElem_push_lt h]
  · have he : i = n := by omega
    subst i
    simp [selected,Vector.get_eq_getElem]

theorem evaluate_garble (hash : Hash) (context : RomCircuit.Context)
    (outputContext : OutputContext m) (keys : Nat → Bool → Label)
    (outputs : Fin m → Bool → Label) (program : RomProgram.Program n m)
    (known : Vector Bool n) :
    evaluate hash context outputContext program
      (garble hash context outputContext keys outputs program) known (selected keys known) =
        Vector.ofFn (fun i => outputs i ((program.eval known).get i)) := by
  induction program with
  | done wires =>
    apply Vector.ext
    intro i hi
    simp only [garble,evaluate,Vector.getElem_ofFn,Vector.get_ofFn,selected_get,
      RomGate.openTranslation_translate,RomProgram.Program.eval,Vector.get_map]
  | @step n m gate tail ih =>
    simp only [garble,evaluate,List.headD_cons,List.tail_cons,selected_get,
      RomGate.evaluate_table,selected_push,RomProgram.Program.eval]
    exact ih outputContext outputs _

end Blake3Prize.Submission.RomExecution
