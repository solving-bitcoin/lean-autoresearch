import Blake3Prize.Submission.RomGraph
import Blake3Prize.Submission.RomAddress

namespace Blake3Prize.Submission.RomCells
open SecretRelease RomProgram RomCounts

def pair (table : Bool → Label) : List Label := [table false,table true]
def row (table : RomGate.Row → Label) : List Label :=
  [table (false,false),table (false,true),table (true,false),table (true,true)]

def readPair (cells : List Label) : Bool → Label :=
  fun bit => cells.getD (if bit then 1 else 0) (RomBytes.zero 32)
def readRow (cells : List Label) : RomGate.Row → Label :=
  fun bits => cells.getD (RomAddress.rowRole bits) (RomBytes.zero 32)

theorem readPair_pair (table : Bool → Label) (rest : List Label) :
    readPair (pair table ++ rest) = table := by
  funext bit
  cases bit <;> simp [readPair,pair]

theorem readRow_row (table : RomGate.Row → Label) (rest : List Label) :
    readRow (row table ++ rest) = table := by
  funext bits
  rcases bits with ⟨a,b⟩
  cases a <;> cases b <;> simp [readRow,row,RomAddress.rowRole]

def pairs : {n : Nat} → Vector (Bool → Label) n → List Label
  | 0, _ => []
  | _+1, tables => pair (tables.get 0) ++ pairs (RomVector.drop tables)

def readPairs : (n : Nat) → List Label → Vector (Bool → Label) n
  | 0, _ => #v[]
  | n+1, cells => RomVector.cons (readPair cells) (readPairs n (cells.drop 2))

theorem readPairs_pairs (tables : Vector (Bool → Label) n) :
    readPairs n (pairs tables) = tables := by
  induction n with
  | zero => exact Vector.ext (fun i hi => by omega)
  | succ n ih =>
    simp only [pairs,readPairs,readPair_pair]
    rw [show (pair (tables.get 0) ++ pairs (RomVector.drop tables)).drop 2 =
      pairs (RomVector.drop tables) by simp [pair]]
    rw [ih,RomVector.cons_drop]

theorem pairs_length (tables : Vector (Bool → Label) n) : (pairs tables).length = 2*n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [pairs,pair,ih]; omega

def flatten (artifact : RomExecution.Artifact m) : List Label :=
  artifact.gates.flatMap row ++ pairs artifact.translations

def read (program : RomProgram.Program n m) (cells : List Label) : RomExecution.Artifact m :=
  match program with
  | .done _ => ⟨[],readPairs m cells⟩
  | .step _ tail =>
      let rest := read tail (cells.drop 4)
      ⟨readRow cells :: rest.gates,rest.translations⟩

theorem read_garble (hash : Hash) (context : RomCircuit.Context)
    (outputContext : RomExecution.OutputContext m) (keys : Nat → Bool → Label)
    (out : Fin m → Bool → Label) (program : RomProgram.Program n m) :
    read program (flatten (RomExecution.garble hash context outputContext keys out program)) =
      RomExecution.garble hash context outputContext keys out program := by
  induction program with
  | done wires => simp [RomExecution.garble,flatten,read,readPairs_pairs]
  | step gate tail ih =>
    simp only [RomExecution.garble,flatten,List.flatMap_cons,List.append_assoc,read,readRow_row]
    rw [show (row (RomGate.table hash (context _) gate.function
        (keys gate.left.val) (keys gate.right.val) (keys _)) ++
      ((RomExecution.garble hash context outputContext keys out tail).gates.flatMap row ++
        pairs (RomExecution.garble hash context outputContext keys out tail).translations)).drop 4 =
      flatten (RomExecution.garble hash context outputContext keys out tail) by simp [row,flatten]]
    rw [ih outputContext out]

theorem garble_length (hash : Hash) (context : RomCircuit.Context)
    (outputContext : RomExecution.OutputContext m) (keys : Nat → Bool → Label)
    (out : Fin m → Bool → Label) (program : RomProgram.Program n m) :
    (flatten (RomExecution.garble hash context outputContext keys out program)).length =
      4 * nodes program + 2*m := by
  induction program with
  | done wires => simp [RomExecution.garble,flatten,nodes,pairs_length]
  | step gate tail ih =>
    simp only [RomExecution.garble,flatten,List.flatMap_cons,List.length_append,
      row,List.length_cons,List.length_nil,nodes]
    have hh := ih outputContext out
    simp only [flatten,List.length_append] at hh
    omega

end Blake3Prize.Submission.RomCells
