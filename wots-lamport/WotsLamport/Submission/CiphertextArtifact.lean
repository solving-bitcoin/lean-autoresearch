import WotsLamport.Submission.ArtifactAnswerCoordinates

namespace WotsLamport.Submission
open SecretRelease WotsLamport.Protected

def indexedCiphertextPrefix (ciphertext : SharePosition → Bytes 64)
    (i : Fin 256) (value : Bool) (index : Nat) : ByteArray :=
  if bound : index < (if value then 1982 else 1984) then
    ByteArray.mk (maskPrefix (ciphertext
      ⟨(i,value,⟨index,by cases value <;> simp_all <;> omega⟩),bound⟩)).toArray
  else ByteArray.empty

def ciphertextLabelTable (ciphertext : SharePosition → Bytes 64)
    (i : Fin 256) (value : Bool) : ByteArray :=
  concatenate ((slots i value).zipIdx.map fun entry =>
    indexedCiphertextPrefix ciphertext i value entry.2)

/-- This serialization contains no label, chain-node or coefficient argument.
The public nonce, commitment answers and ciphertext coordinates suffice. -/
def ciphertextBody (nonce : ByteArray) (commitments : CommitmentCell → Label)
    (ciphertext : SharePosition → Bytes 64) : ByteArray :=
  nonce ++ concatenate ((List.finRange 256).map fun i =>
    ByteArray.mk (commitments (i,false)).toArray ++ ByteArray.mk (commitments (i,true)).toArray) ++
  concatenate ((List.finRange 256).map fun i =>
    ciphertextLabelTable ciphertext i false ++ ciphertextLabelTable ciphertext i true)

theorem idealLabelTable_ciphertext (coins : ByteArray) (labels : Fin 256 → Pair)
    (answers : ArtifactAnswers) (i : Fin 256) (value : Bool) :
    idealLabelTable coins answers i value ((labels i).get value) =
      ciphertextLabelTable (artifactCiphertextCoordinates coins labels answers).1 i value := by
  unfold idealLabelTable ciphertextLabelTable
  apply congrArg concatenate
  apply List.map_congr_left
  intro entry member
  have bound : entry.2 < (if value then 1982 else 1984) := by
    have hb := List.snd_lt_of_mem_zipIdx member
    simpa only [Nat.add_zero, slots_length] using hb
  have bound' : entry.2 < 1984 := by cases value <;> simp_all <;> omega
  let position : SharePosition := ⟨(i,value,⟨entry.2,bound'⟩),bound⟩
  simp only [List.map_map, Function.comp_def]
  change xorBytes (idealPlaintextBytes coins labels position)
    (indexedAnswerMask answers i value entry.2) = _
  simp only [indexedAnswerMask, dif_pos bound]
  rw [← artifactCiphertextCoordinates_row coins labels answers position]
  simp only [indexedCiphertextPrefix, dif_pos bound, position]

/-- Exact full-body independence in ciphertext coordinates, retaining every
commitment and every serialized share in its original position. -/
theorem idealPreparedBody_ciphertext (coins : ByteArray) (labels : Fin 256 → Pair)
    (answers : ArtifactAnswers) :
    idealPreparedBody coins labels answers = ciphertextBody (coins.extract 0 32)
      (artifactCiphertextCoordinates coins labels answers).2
      (artifactCiphertextCoordinates coins labels answers).1 := by
  simp only [idealPreparedBody, ciphertextBody, idealLabelTable_ciphertext]
  rfl

theorem prepare_programmedHash_ciphertext (coins : ByteArray) (tape : ChainTape)
    (labels : Fin 256 → Pair) (answers : ArtifactAnswers) (baseline : Hash)
    (distinct : Function.Injective tape) :
    prepare (programmedHash (coins.extract 0 32) tape labels answers baseline)
      coins (tapeKeys tape) labels = ciphertextBody (coins.extract 0 32)
        (artifactCiphertextCoordinates coins labels answers).2
        (artifactCiphertextCoordinates coins labels answers).1 := by
  rw [prepare_programmedHash coins tape labels answers baseline distinct,
    idealPreparedBody_ciphertext]

end WotsLamport.Submission
