import Blake3Prize.Submission.RomKeyMaterial
import Blake3Prize.Submission.RomCells
import Blake3Prize.Submission.RomPacking
import Blake3Prize.Submission.RomFastExecution
import Blake3Prize.Protected.Target

set_option maxRecDepth 4096

namespace Blake3Prize.Submission.RomScheme
open SecretRelease Blake3Prize.Protected RomKeyMaterial

def tables (hash : Hash) (keys : KeySet) : RomExecution.Artifact 256 :=
  RomFastExecution.garble hash RomAddress.gateContext (fun i => RomAddress.outputContext i.val)
    (wireKeys keys) (outKeys keys) RomBlake3.program

theorem tables_spec (hash : Hash) (keys : KeySet) : tables hash keys =
    RomExecution.garble hash RomAddress.gateContext (fun i => RomAddress.outputContext i.val)
      (wireKeys keys) (outKeys keys) RomBlake3.program := RomFastExecution.garble_eq _ _ _ _ _ _

def cells (hash : Hash) (keys : KeySet) : List Label :=
  wireKeys keys 512 false :: wireKeys keys 513 true :: RomCells.flatten (tables hash keys)

theorem cells_length (hash : Hash) (keys : KeySet) : (cells hash keys).length = 245250 := by
  simp only [cells,List.length_cons,tables_spec,RomCells.garble_length,RomBlake3.program_nodes]

def garble (hash : Hash) (coins : Bytes 3915904) (_private : Unit)
    (inputs : Fin 512 → Pair) (outputs : Fin 256 → Pair) : Bytes 7848000 :=
  RomPacking.fixed (cells hash (assemble coins inputs outputs))
    (cells_length hash (assemble coins inputs outputs))

theorem garble_bytes (hash : Hash) (coins : Bytes 3915904) (p : Unit)
    (inputs : Fin 512 → Pair) (outputs : Fin 256 → Pair) :
    RomBytes.encode (garble hash coins p inputs outputs) =
      pack (cells hash (assemble coins inputs outputs)) := RomPacking.fixed_encode _ _

def evaluate (hash : Hash) (artifact : Bytes 7848000) (input : Input)
    (active : ByteArray) : Option ByteArray :=
  if active.size = 16384 then
    let decoded := (RomPacking.unpack 245250 (RomBytes.encode artifact)).toList
    let circuit := RomFastExecution.read RomBlake3.program (decoded.drop 2)
    let initial := (RomPacking.unpack 512 active).push
      (decoded.getD 0 (RomBytes.zero 32)) |>.push (decoded.getD 1 (RomBytes.zero 32))
    some (pack (RomExecution.evaluate hash RomAddress.gateContext
      (fun i => RomAddress.outputContext i.val) RomBlake3.program circuit
        (RomInput.known input) initial).toList)
  else none

def scheme : SecretRelease.Scheme challenge where
  Artifact := Bytes 7848000
  randomnessBytes := 3915904
  garble := garble
  encode := RomBytes.encode
  decode := RomBytes.decode 7848000
  evaluate := evaluate

theorem input_encoded (input : Input) (i : Fin 512) :
    ((SecretRelease.Codec.byteVector 64).encode input).get i = inputBit input i := rfl

theorem input_reveal (hash : Hash) (inputs : Fin 512 → Pair) (input : Input) :
    challenge.inputs.reveal hash inputs input =
      pack ((List.finRange 512).map fun i => (inputs i).get (inputBit input i)) := by
  change pack ((List.finRange 512).map fun i =>
    (inputs i).get (((SecretRelease.Codec.byteVector 64).encode input).get i)) = _
  apply congrArg pack
  apply List.map_congr_left
  intro i _
  exact congrArg (inputs i).get (input_encoded input i)

theorem honest_inputs (hash : Hash) (inputs : Fin 512 → Pair) (input : Input) :
    RomPacking.unpack 512 (challenge.inputs.reveal hash inputs input) =
      Vector.ofFn (fun i => (inputs i).get (inputBit input i)) := by
  rw [input_reveal]
  apply Vector.ext
  intro i hi
  simp only [RomPacking.unpack,Vector.getElem_ofFn]
  rw [RomPacking.readLabel_pack _ i (by simp; omega)]
  simp

theorem initial_selected (coins : Bytes 3915904) (inputs : Fin 512 → Pair)
    (outputs : Fin 256 → Pair) (input : Input) :
    ((Vector.ofFn (fun i : Fin 512 => (inputs i).get (inputBit input i))).push
        (wireKeys (assemble coins inputs outputs) 512 false)).push
        (wireKeys (assemble coins inputs outputs) 513 true) =
      RomExecution.selected (wireKeys (assemble coins inputs outputs)) (RomInput.known input) := by
  apply Vector.ext
  intro i hi
  by_cases h : i < 512
  · simp only [RomExecution.selected,Vector.getElem_ofFn]
    rw [RomInput.known_input input ⟨i,h⟩,assembled_input coins inputs outputs ⟨i,h⟩]
    simp [Vector.getElem_push_lt (by omega : i < 513),Vector.getElem_push_lt h]
  · have he : i = 512 ∨ i = 513 := by omega
    rcases he with rfl | rfl
    · simp only [RomExecution.selected,Vector.getElem_ofFn]
      rw [RomInput.known_zero input]
      simp [Vector.get_eq_getElem]
    · simp only [RomExecution.selected,Vector.getElem_ofFn]
      rw [RomInput.known_one input]
      simp [Vector.get_eq_getElem]

/-- Concrete byte interface, separated from the challenge's dependent key types. -/
def inputBytes (inputs : Fin 512 → Pair) (input : Input) : ByteArray :=
  pack ((List.finRange 512).map fun i => (inputs i).get (inputBit input i))

def outputBytes (outputs : Fin 256 → Pair) (input : Input) : ByteArray :=
  pack ((List.finRange 256).map fun i =>
    (outputs i).get (((SecretRelease.Codec.byteVector 32).encode (reference input)).get i))

theorem unpack_inputBytes (inputs : Fin 512 → Pair) (input : Input) :
    RomPacking.unpack 512 (inputBytes inputs input) =
      Vector.ofFn (fun i => (inputs i).get (inputBit input i)) := by
  apply Vector.ext
  intro i hi
  simp only [RomPacking.unpack,Vector.getElem_ofFn,inputBytes]
  rw [RomPacking.readLabel_pack _ i (by simp; omega)]
  simp

theorem output_reveal (hash : Hash) (outputs : Fin 256 → Pair) (input : Input) :
    challenge.outputs.reveal hash outputs (reference input) = outputBytes outputs input := rfl

theorem evaluate_honest (hash : Hash) (coins : Bytes 3915904) (p : Unit)
    (inputs : Fin 512 → Pair) (outputs : Fin 256 → Pair) (input : Input) :
    evaluate hash (garble hash coins p inputs outputs) input (inputBytes inputs input) =
      some (outputBytes outputs input) := by
  have hs : (inputBytes inputs input).size = 16384 := by
    rw [inputBytes,RomPacking.pack_length]
    simp
  rw [evaluate,if_pos hs,garble_bytes,
    RomPacking.unpack_pack_of_length _ (cells_length hash (assemble coins inputs outputs))]
  dsimp only
  rw [RomFastExecution.read_eq]
  simp only [cells,List.drop_succ_cons,List.drop_zero,List.getD_cons_zero,
    List.getD_cons_succ]
  rw [show RomCells.read RomBlake3.program (RomCells.flatten (tables hash
      (assemble coins inputs outputs))) = tables hash (assemble coins inputs outputs) from
    (by rw [tables_spec]; exact RomCells.read_garble _ _ _ _ _ _),unpack_inputBytes,initial_selected]
  rw [tables_spec,RomExecution.evaluate_garble,RomBlake3.program_correct]
  change some (pack (Vector.ofFn (fun i : Fin 256 =>
    outKeys (assemble coins inputs outputs) i (((SecretRelease.Codec.byteVector 32).encode (reference input)).get i))).toList) = _
  simp only [assembled_output,Vector.toList_ofFn]
  rfl

theorem correct : SecretRelease.Correct scheme := by
  intro hash coins p inputs outputs input
  delta SecretRelease.Scheme.evaluateBytes SecretRelease.Scheme.garbleBytes
  dsimp only [scheme]
  rw [RomBytes.decode_encode,Option.bind_some]
  exact (congrArg (evaluate hash (garble hash coins p inputs outputs) input)
    (input_reveal hash inputs input)).trans
    ((evaluate_honest hash coins p inputs outputs input).trans
      (congrArg some (output_reveal hash outputs input).symm))

theorem artifact_bound : SecretRelease.ArtifactBound scheme 7848000 := by
  intro hash coins p inputs outputs
  exact le_of_eq (RomBytes.encode_size _)

end Blake3Prize.Submission.RomScheme
