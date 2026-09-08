import Blake3Prize.Submission.RomProgram

namespace Blake3Prize.Submission.RomParallel
open RomCircuit RomProgram

def value (gate : Gate n) (input : Vector Bool n) : Bool :=
  gate.function (input.get gate.left) (input.get gate.right)

def parallel : {k : Nat} → Vector (Gate n) k → RomProgram.Program n k
  | 0, _ => .done #v[]
  | _+1, gates => .step (gates.get 0)
      ((parallel ((RomVector.drop gates).map (fun gate => Gate.rewire gate Fin.castSucc))).keepOne
        (Fin.last n))

theorem value_lift (gate : Gate n) (input : Vector Bool n) (last : Bool) :
    value (Gate.rewire gate Fin.castSucc) (input.push last) = value gate input := by
  simp [value,Gate.rewire,RomCircuit.Gate.function,Vector.get_eq_getElem]

theorem eval_parallel (gates : Vector (Gate n) k) (input : Vector Bool n) :
    (parallel gates).eval input = gates.map (fun gate => value gate input) := by
  induction k generalizing n with
  | zero => simp [parallel,RomProgram.Program.eval]
  | succ k ih =>
    simp only [parallel,RomProgram.Program.eval,eval_keepOne,ih]
    have hs : ((input.push (value (gates.get 0) input)).get (Fin.last n)) =
        value (gates.get 0) input := by simp [Vector.get_eq_getElem]
    change RomVector.cons ((input.push (value (gates.get 0) input)).get (Fin.last n))
      (((RomVector.drop gates).map (fun gate => Gate.rewire gate Fin.castSucc)).map
        (fun gate => value gate (input.push (value (gates.get 0) input)))) = _
    rw [hs]
    have ht : (((RomVector.drop gates).map (fun gate => Gate.rewire gate Fin.castSucc)).map
        (fun gate => value gate (input.push (value (gates.get 0) input)))) =
        (RomVector.drop gates).map (fun gate => value gate input) := by
      ext i hi
      change (((RomVector.drop gates).map (fun gate => Gate.rewire gate Fin.castSucc)).map
        (fun gate => value gate (input.push (value (gates.get 0) input)))).get ⟨i,hi⟩ =
        ((RomVector.drop gates).map (fun gate => value gate input)).get ⟨i,hi⟩
      simp only [Vector.get_map,value_lift]
    rw [ht, ← RomVector.map_cons (fun gate => value gate input) (gates.get 0)
      (RomVector.drop gates),RomVector.cons_drop]

def xorWords (a b : Vector (Fin n) w) : RomProgram.Program n w :=
  parallel (Vector.ofFn fun i => ⟨false,a.get i,b.get i⟩)

theorem eval_xorWords (a b : Vector (Fin n) w) (input : Vector Bool n) :
    (xorWords a b).eval input =
      Vector.ofFn (fun i => input.get (a.get i) ^^ input.get (b.get i)) := by
  rw [xorWords,eval_parallel]
  ext i hi
  simp [value,RomCircuit.Gate.function,Vector.get_eq_getElem]

end Blake3Prize.Submission.RomParallel
