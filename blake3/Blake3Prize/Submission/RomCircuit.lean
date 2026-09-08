import Blake3Prize.Submission.RomGate

/-! A topologically typed circuit and its four-row garbling. Each instruction
can read only earlier wires. The induction below proves label recovery for
the whole circuit, for every hash function and every consistent assignment.
The circuit and its topology are public, fixed program data. -/
namespace Blake3Prize.Submission.RomCircuit
open SecretRelease

structure Gate (n : Nat) where
  isAnd : Bool
  left : Fin n
  right : Fin n

def Gate.function (gate : Gate n) (a b : Bool) : Bool :=
  if gate.isAnd then a && b else xor a b

inductive Circuit : Nat → Type where
  | done : Circuit n
  | step : Gate n → Circuit (n+1) → Circuit n

def Circuit.gates : Circuit n → Nat
  | .done => 0
  | .step _ tail => 1 + tail.gates

def Consistent : Circuit n → (Nat → Bool) → Prop
  | .done, _ => True
  | .step gate tail, bits =>
      bits n = gate.function (bits gate.left.val) (bits gate.right.val) ∧
        Consistent tail bits

abbrev Table := RomGate.Row → Label
abbrev Context := Nat → RomGate.Row → ByteArray

def garble (hash : Hash) (context : Context) (keys : Nat → Bool → Label) :
    Circuit n → List Table
  | .done => []
  | .step gate tail =>
      RomGate.table hash (context n) gate.function
        (keys gate.left.val) (keys gate.right.val) (keys n) ::
        garble hash context keys tail

def evaluate (hash : Hash) (context : Context) (bits : Nat → Bool) :
    (circuit : Circuit n) → List Table → Vector Label n → Array Label
  | .done, _, active => active.toArray
  | .step gate tail, tables, active =>
      let row := (bits gate.left.val,bits gate.right.val)
      let ciphertext := (tables.headD (fun _ => RomBytes.zero 32)) row
      let next := RomGate.evaluate hash (context n row) ciphertext
        (active.get gate.left) (active.get gate.right)
      evaluate hash context bits tail tables.tail (active.push next)

def selected (n : Nat) (keys : Nat → Bool → Label) (bits : Nat → Bool) : Vector Label n :=
  Vector.ofFn fun i => (keys i.val) (bits i.val)

@[simp] theorem selected_get (keys : Nat → Bool → Label) (bits : Nat → Bool) (i : Fin n) :
    (selected n keys bits).get i = keys i.val (bits i.val) := by
  simp [selected]

theorem selected_push (keys : Nat → Bool → Label) (bits : Nat → Bool) :
    (selected n keys bits).push ((keys n) (bits n)) = selected (n+1) keys bits := by
  apply Vector.ext
  intro i hi
  by_cases h : i < n
  · simp [selected,Vector.getElem_push_lt h]
  · have he : i = n := by omega
    subst i
    simp [selected]

/-- The clear-label execution is only a correctness specification. It does
not occur in the evaluator or in the serialized public artifact. -/
def clear (keys : Nat → Bool → Label) (bits : Nat → Bool) : Circuit n → Array Label
  | .done => (selected n keys bits).toArray
  | .step _ tail => clear keys bits tail

theorem evaluate_garble (hash : Hash) (context : Context) (keys : Nat → Bool → Label)
    (bits : Nat → Bool) (circuit : Circuit n) (hc : Consistent circuit bits) :
    evaluate hash context bits circuit (garble hash context keys circuit)
      (selected n keys bits) = clear keys bits circuit := by
  induction circuit with
  | done => rfl
  | @step n gate tail ih =>
    simp only [garble,evaluate,clear,List.headD_cons,List.tail_cons,selected_get,
      RomGate.evaluate_table]
    rw [← hc.1, selected_push]
    exact ih hc.2

theorem garble_length (hash : Hash) (context : Context) (keys : Nat → Bool → Label)
    (circuit : Circuit n) : (garble hash context keys circuit).length = circuit.gates := by
  induction circuit with
  | done => rfl
  | step gate tail ih => simp [garble,Circuit.gates,ih,Nat.add_comm]

end Blake3Prize.Submission.RomCircuit
