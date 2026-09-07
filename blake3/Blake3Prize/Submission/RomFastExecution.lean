import Blake3Prize.Submission.RomCells

/-! Tail-recursive construction and parsing avoid one native stack frame per
gate. Reversing the accumulator is proved to give exactly the specification
artifact, including its original table order. -/
namespace Blake3Prize.Submission.RomFastExecution
open SecretRelease

def garbleWith (hash : Hash) (context : RomCircuit.Context)
    (outputContext : RomExecution.OutputContext m) (keys : Nat → Bool → Label)
    (out : Fin m → Bool → Label) (acc : List RomCircuit.Table) :
    RomProgram.Program n m → RomExecution.Artifact m
  | .done wires => ⟨acc.reverse,Vector.ofFn fun i =>
      RomGate.translate hash (outputContext i) (keys (wires.get i).val) (out i)⟩
  | .step gate tail => garbleWith hash context outputContext keys out
      (RomGate.table hash (context n) gate.function
        (keys gate.left.val) (keys gate.right.val) (keys n) :: acc) tail

theorem garbleWith_eq (hash : Hash) (context : RomCircuit.Context)
    (outputContext : RomExecution.OutputContext m) (keys : Nat → Bool → Label)
    (out : Fin m → Bool → Label) (program : RomProgram.Program n m) (acc : List RomCircuit.Table) :
    garbleWith hash context outputContext keys out acc program =
      ⟨acc.reverse ++ (RomExecution.garble hash context outputContext keys out program).gates,
        (RomExecution.garble hash context outputContext keys out program).translations⟩ := by
  induction program generalizing acc with
  | done wires => simp [garbleWith,RomExecution.garble]
  | step gate tail ih =>
    simp only [garbleWith,ih,RomExecution.garble,List.reverse_cons,List.append_assoc,
      List.singleton_append]

def garble (hash : Hash) (context : RomCircuit.Context)
    (outputContext : RomExecution.OutputContext m) (keys : Nat → Bool → Label)
    (out : Fin m → Bool → Label) (program : RomProgram.Program n m) : RomExecution.Artifact m :=
  garbleWith hash context outputContext keys out [] program

theorem garble_eq (hash : Hash) (context : RomCircuit.Context)
    (outputContext : RomExecution.OutputContext m) (keys : Nat → Bool → Label)
    (out : Fin m → Bool → Label) (program : RomProgram.Program n m) :
    garble hash context outputContext keys out program =
      RomExecution.garble hash context outputContext keys out program := by
  simp [garble,garbleWith_eq]

def readWith (program : RomProgram.Program n m) (cells : List Label) (acc : List RomCircuit.Table) :
    RomExecution.Artifact m :=
  match program with
  | .done _ => ⟨acc.reverse,RomCells.readPairs m cells⟩
  | .step _ tail => readWith tail (cells.drop 4) (RomCells.readRow cells :: acc)

theorem readWith_eq (program : RomProgram.Program n m) (cells : List Label) (acc : List RomCircuit.Table) :
    readWith program cells acc =
      ⟨acc.reverse ++ (RomCells.read program cells).gates,(RomCells.read program cells).translations⟩ := by
  induction program generalizing cells acc with
  | done wires => simp [readWith,RomCells.read]
  | step gate tail ih =>
    simp only [readWith,ih,RomCells.read,List.reverse_cons,List.append_assoc,List.singleton_append]

def read (program : RomProgram.Program n m) (cells : List Label) : RomExecution.Artifact m :=
  readWith program cells []

theorem read_eq (program : RomProgram.Program n m) (cells : List Label) :
    read program cells = RomCells.read program cells := by simp [read,readWith_eq]

end Blake3Prize.Submission.RomFastExecution
