import WotsLamport.Submission.IdealArtifact
import WotsLamport.Submission.TwoHashMask

namespace WotsLamport.Submission
open SecretRelease MeasureTheory ProbabilityTheory

/-- Both complete 32-byte answers are retained by this equivalence. -/
def boolMaskPadEquiv : (Bool → Label) ≃ Bytes 64 :=
  (Equiv.piCongrLeft (fun _ : Bool => Label) finTwoEquiv).symm.trans (byteBlocksEquiv 2).symm

def artifactAnswerCoordinates : ArtifactAnswers ≃
    (SharePosition → Bytes 64) × (CommitmentCell → Label) :=
  (Equiv.sumArrowEquivProdArrow MaskCell CommitmentCell Label).trans
    (Equiv.prodCongr
      ((Equiv.curry SharePosition Bool Label).trans
        (Equiv.piCongrRight fun _ => boolMaskPadEquiv)) (Equiv.refl _))

theorem artifactAnswerCoordinates_mask (answers : ArtifactAnswers) (position : SharePosition) :
    ByteArray.mk (maskPrefix ((artifactAnswerCoordinates answers).1 position)).toArray =
      answerMask answers position := by
  change ByteArray.mk (maskPrefix (fullMaskPad
    (fun block => answers (Sum.inl (position,finTwoEquiv block))))).toArray = _
  rw [fullMaskPad_prefix]
  rfl

theorem artifactAnswerCoordinates_commitment (answers : ArtifactAnswers) (cell : CommitmentCell) :
    (artifactAnswerCoordinates answers).2 cell = answers (Sum.inr cell) := rfl

/-- Full joint answer law, including the unused 16-byte tail of each mask. -/
theorem uniform_artifact_answer_coordinates
    (event : Set ((SharePosition → Bytes 64) × (CommitmentCell → Label))) :
    uniformOn (Set.univ : Set ArtifactAnswers) (artifactAnswerCoordinates ⁻¹' event) =
      uniformOn (Set.univ : Set ((SharePosition → Bytes 64) × (CommitmentCell → Label))) event :=
  Shamir.uniform_event_equiv artifactAnswerCoordinates event

/-- Exactly the executable's 16 serialized field evaluations for one row. -/
def idealPlaintextBytes (coins : ByteArray) (labels : Fin 256 → Pair)
    (position : SharePosition) : ByteArray :=
  concatenate ((List.range 16).map fun limb => writeLE 3
    (evaluatePolynomial (polynomial coins ((labels position.val.1).get position.val.2.1)
      position.val.1.val limb position.val.2.1) (position.val.2.2.val+1)))

theorem idealPlaintextBytes_size (coins : ByteArray) (labels : Fin 256 → Pair)
    (position : SharePosition) : (idealPlaintextBytes coins labels position).size = 48 := by
  unfold idealPlaintextBytes
  rw [concatenate_map_size (List.range 16) _ 3 (by intro limb _; exact writeLE_size 3 _)]
  rfl

def idealPlaintext (coins : ByteArray) (labels : Fin 256 → Pair)
    (position : SharePosition) : Bytes 48 :=
  ⟨(idealPlaintextBytes coins labels position).data, idealPlaintextBytes_size coins labels position⟩

def artifactCiphertextCoordinates (coins : ByteArray) (labels : Fin 256 → Pair) :
    ArtifactAnswers ≃ (SharePosition → Bytes 64) × (CommitmentCell → Label) :=
  artifactAnswerCoordinates.trans
    (Equiv.prodCongr (Equiv.piCongrRight fun position =>
      xorVectorEquiv (extendMaskPlaintext (idealPlaintext coins labels position))) (Equiv.refl _))

theorem xorVector_comm {n : Nat} (a b : Bytes n) : xorVector a b = xorVector b a := by
  apply Vector.ext
  intro i hi
  simp only [xorVector, Vector.getElem_ofFn, UInt8.xor_comm]

/-- Each ciphertext prefix is exactly its serialized share XOR the actual
48-byte mask; the independent tail is carried through unchanged. -/
theorem artifactCiphertextCoordinates_row (coins : ByteArray) (labels : Fin 256 → Pair)
    (answers : ArtifactAnswers) (position : SharePosition) :
    ByteArray.mk (maskPrefix ((artifactCiphertextCoordinates coins labels answers).1 position)).toArray =
      xorBytes (idealPlaintextBytes coins labels position) (answerMask answers position) := by
  change ByteArray.mk (maskPrefix (xorVector ((artifactAnswerCoordinates answers).1 position)
    (extendMaskPlaintext (idealPlaintext coins labels position)))).toArray = _
  rw [maskPrefix_xor, maskPrefix_extend, xorVector_comm, xorVector_bytes,
    artifactAnswerCoordinates_mask]
  rfl

/-- For fixed coins and labels, the complete ciphertext/commitment table is
uniform. This is a bijection of all actual answer randomness, not a collection
of unrelated marginal equalities. -/
theorem uniform_artifact_ciphertext_coordinates (coins : ByteArray) (labels : Fin 256 → Pair)
    (event : Set ((SharePosition → Bytes 64) × (CommitmentCell → Label))) :
    uniformOn (Set.univ : Set ArtifactAnswers)
        ((artifactCiphertextCoordinates coins labels) ⁻¹' event) =
      uniformOn (Set.univ : Set ((SharePosition → Bytes 64) × (CommitmentCell → Label))) event :=
  Shamir.uniform_event_equiv (artifactCiphertextCoordinates coins labels) event

end WotsLamport.Submission
