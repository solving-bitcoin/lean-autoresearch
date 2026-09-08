import Blake3Prize.Submission.RomCircuit
import Blake3Prize.Submission.RomVector

/-! Circuit composition preserves sharing: intermediate values are wire
indices, and each gate is evaluated once. Rewiring changes only public
indices. These composition lemmas avoid trusting a hash-consing compiler. -/
namespace Blake3Prize.Submission.RomProgram
open RomCircuit

inductive Program : Nat → Nat → Type where
  | done : Vector (Fin n) m → Program n m
  | step : Gate n → Program (n+1) m → Program n m

def project (values : Vector α m) (wires : Fin n → Fin m) : Vector α n :=
  Vector.ofFn fun i => values.get (wires i)

def liftWire (wires : Fin n → Fin m) : Fin (n+1) → Fin (m+1) :=
  Fin.lastCases (Fin.last m) (fun i => (wires i).castSucc)

theorem project_push (values : Vector α m) (wires : Fin n → Fin m) (last : α) :
    project (values.push last) (liftWire wires) = (project values wires).push last := by
  apply Vector.ext
  intro i hi
  have h := Fin.lastCases
    (motive := fun j : Fin (n+1) =>
      (project (values.push last) (liftWire wires)).get j =
        ((project values wires).push last).get j)
    (by
      simp only [project,Vector.get_ofFn,liftWire,Fin.lastCases_last]
      simp [Vector.get_eq_getElem])
    (fun j => by
      simp only [project,Vector.get_ofFn,liftWire,Fin.lastCases_castSucc]
      simp [Vector.get_eq_getElem])
    (⟨i,hi⟩ : Fin (n+1))
  exact h

def Gate.rewire (gate : Gate n) (wires : Fin n → Fin m) : Gate m :=
  ⟨gate.isAnd,wires gate.left,wires gate.right⟩

def Program.rewire (program : Program n k) (wires : Fin n → Fin m) : Program m k :=
  match program with
  | .done output => .done (output.map wires)
  | .step gate tail => .step (Gate.rewire gate wires) (tail.rewire (liftWire wires))

theorem pushedBounds (mapping : Vector Nat n) (bound : ∀ i, mapping.get i < m) :
    ∀ i : Fin (n+1), (mapping.push m).get i < m+1 := by
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [Vector.get_eq_getElem]
  · have h := bound j
    simpa [Vector.get_eq_getElem] using Nat.lt_succ_of_lt h

/-- Array-backed renaming avoids a chain of one closure per previous gate.
The bounds are proof data; the executable map contains only natural indices. -/
def Program.fastWith (program : Program n k) (mapping : Vector Nat n)
    (bound : ∀ i, mapping.get i < m) : Program m k :=
  match program with
  | .done output => .done (output.map fun i => ⟨mapping.get i,bound i⟩)
  | .step gate tail =>
      .step ⟨gate.isAnd,⟨mapping.get gate.left,bound gate.left⟩,
        ⟨mapping.get gate.right,bound gate.right⟩⟩
        (tail.fastWith (mapping.push m) (pushedBounds mapping bound))

def Program.fastRewire (program : Program n k) (wires : Fin n → Fin m) : Program m k :=
  program.fastWith (Vector.ofFn fun i => (wires i).val) (by intro i; simp)

theorem fastWith_eq (program : Program n k) (mapping : Vector Nat n)
    (bound : ∀ i, mapping.get i < m) (wires : Fin n → Fin m)
    (agree : ∀ i, mapping.get i = (wires i).val) :
    program.fastWith mapping bound = program.rewire wires := by
  induction program generalizing m with
  | done output =>
    simp only [Program.fastWith,Program.rewire]
    congr 1
    ext i hi
    simp only [Vector.getElem_map]
    exact agree output[i]
  | step gate tail ih =>
    simp only [Program.fastWith,Program.rewire]
    congr 1
    · cases gate with
      | mk isAnd left right =>
        simp only [Gate.rewire]
        congr 1
        · exact Fin.ext (agree left)
        · exact Fin.ext (agree right)
    · apply ih _ _ (liftWire wires)
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp only [liftWire,Fin.lastCases_last,Fin.val_last,Vector.get_eq_getElem,
          Vector.getElem_push_eq]
      · simp only [liftWire,Fin.lastCases_castSucc,Fin.val_castSucc,
          Vector.get_eq_getElem]
        rw [Vector.getElem_push_lt j.isLt]
        exact agree j

@[simp] theorem fastRewire_eq (program : Program n k) (wires : Fin n → Fin m) :
    program.fastRewire wires = program.rewire wires := by
  apply fastWith_eq
  intro i
  simp

def Program.eval : Program n m → Vector Bool n → Vector Bool m
  | .done output, input => output.map input.get
  | .step gate tail, input => tail.eval
      (input.push (gate.function (input.get gate.left) (input.get gate.right)))

def Program.comp (left : Program n m) (right : Program m k) : Program n k :=
  match left with
  | .done output => right.fastRewire output.get
  | .step gate tail => .step gate (tail.comp right)

theorem eval_rewire (program : Program n k) (wires : Fin n → Fin m) (input : Vector Bool m) :
    (program.rewire wires).eval input = program.eval (project input wires) := by
  induction program generalizing m with
  | done output =>
    apply Vector.ext
    intro i hi
    simp [Program.rewire,Program.eval,project,Vector.get_eq_getElem]
  | step gate tail ih =>
    simp only [Program.rewire,Program.eval,ih,project_push]
    simp only [Gate.rewire,RomCircuit.Gate.function,project,Vector.get_ofFn]
    rfl

theorem eval_comp (left : Program n m) (right : Program m k) (input : Vector Bool n) :
    (left.comp right).eval input = right.eval (left.eval input) := by
  induction left with
  | done output =>
    simp only [Program.comp,fastRewire_eq,eval_rewire,Program.eval]
    congr 1
    apply Vector.ext
    intro i hi
    simp [project,Vector.get_eq_getElem]
  | step gate tail ih =>
    simp only [Program.comp,Program.eval]
    exact ih right _

def identity (n : Nat) : Program n n := .done (Vector.finRange n)

theorem eval_identity (input : Vector Bool n) : (identity n).eval input = input := by
  apply Vector.ext
  intro i hi
  simp [identity,Program.eval,Vector.get_eq_getElem]

def appendGate (gate : Gate n) : Program n (n+1) :=
  .step gate (identity (n+1))

theorem eval_appendGate (gate : Gate n) (input : Vector Bool n) :
    (appendGate gate).eval input =
      input.push (gate.function (input.get gate.left) (input.get gate.right)) := by
  simp [appendGate,Program.eval,eval_identity]

def Program.keepOne (wire : Fin n) : Program n m → Program n (m+1)
  | .done output => .done (RomVector.cons wire output)
  | .step gate tail => .step gate (tail.keepOne wire.castSucc)

theorem eval_keepOne (program : Program n m) (wire : Fin n) (input : Vector Bool n) :
    (program.keepOne wire).eval input = RomVector.cons (input.get wire) (program.eval input) := by
  induction program with
  | done output => simp [Program.keepOne,Program.eval]
  | step gate tail ih =>
    simp only [Program.keepOne,Program.eval,ih]
    congr 1
    simp [Vector.get_eq_getElem]

def Program.keep (wires : Vector (Fin n) k) : Program n m → Program n (k+m)
  | .done output => .done (wires ++ output)
  | .step gate tail => .step gate (tail.keep (wires.map Fin.castSucc))

theorem eval_keep (program : Program n m) (wires : Vector (Fin n) k) (input : Vector Bool n) :
    (program.keep wires).eval input = wires.map input.get ++ program.eval input := by
  induction program with
  | done output => simp [Program.keep,Program.eval]
  | step gate tail ih =>
    simp only [Program.keep,Program.eval,ih]
    congr 1
    ext i hi
    simp [Vector.get_eq_getElem]

end Blake3Prize.Submission.RomProgram
