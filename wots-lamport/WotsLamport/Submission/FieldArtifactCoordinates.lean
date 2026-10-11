import WotsLamport.Submission.VisibleProgrammedOracle
import WotsLamport.Submission.CanonicalLabels

namespace WotsLamport.Submission
open SecretRelease WotsLamport.Protected

/-- Ciphertext coordinates expressed in terms of the actual field table.
All 64 bytes per mask are retained, including its unused random tail. -/
noncomputable def fieldArtifactCoordinates (labels : Fin 256 → Pair) (c : AllocatedCoefficients) :
    ArtifactAnswers ≃ (SharePosition → Bytes 64) × (CommitmentCell → Label) :=
  artifactAnswerCoordinates.trans
    (Equiv.prodCongr (Equiv.piCongrRight fun position =>
      xorVectorEquiv (extendMaskPlaintext (fieldPlaintext labels c position))) (Equiv.refl _))

theorem actual_field_artifact_coordinates (coins : Bytes randomnessBytes) (labels : Fin 256 → Pair) :
    fieldArtifactCoordinates labels (polynomialTableEquiv (actualFieldTable coins)) =
      artifactCiphertextCoordinates (ByteArray.mk coins.toArray) labels := by
  have plaintext := funext (idealPlaintext_as_fields coins labels)
  unfold fieldArtifactCoordinates artifactCiphertextCoordinates
  rw [← plaintext]

noncomputable def fieldArtifactAnswers (labels : Fin 256 → Pair) (c : AllocatedCoefficients)
    (coordinates : (SharePosition → Bytes 64) × (CommitmentCell → Label)) : ArtifactAnswers :=
  (fieldArtifactCoordinates labels c).symm coordinates

theorem fieldArtifactAnswers_mask (labels : Fin 256 → Pair) (c : AllocatedCoefficients)
    (coordinates : (SharePosition → Bytes 64) × (CommitmentCell → Label))
    (position : SharePosition) (block : Bool) :
    fieldArtifactAnswers labels c coordinates (Sum.inl (position,block)) =
      (boolMaskPadEquiv.symm (xorVector (coordinates.1 position)
        (extendMaskPlaintext (fieldPlaintext labels c position)))) block := rfl

theorem fieldArtifactAnswers_commitment (labels : Fin 256 → Pair) (c : AllocatedCoefficients)
    (coordinates : (SharePosition → Bytes 64) × (CommitmentCell → Label)) (cell : CommitmentCell) :
    fieldArtifactAnswers labels c coordinates (Sum.inr cell) = coordinates.2 cell := rfl

/-- The full two-answer mask, not only its 48-byte prefix, is preserved at
visible positions by the explicit coefficient transport. -/
theorem fieldArtifactAnswers_visible_transport (m : Message) (a b : Fin 256 → Pair)
    (selected : ∀ i, (a i).get (outputCodec.encode m)[i.val] =
      (b i).get (outputCodec.encode m)[i.val]) (c : AllocatedCoefficients)
    (coordinates : (SharePosition → Bytes 64) × (CommitmentCell → Label))
    (cell : ArtifactCell) (visible : visibleArtifactCell m cell) :
    fieldArtifactAnswers b (visibleCoefficientEquiv m a b selected c) coordinates cell =
      fieldArtifactAnswers a c coordinates cell := by
  cases cell with
  | inl cell =>
    rw [fieldArtifactAnswers_mask, fieldArtifactAnswers_mask,
      fieldPlaintext_visible_transport m a b selected c cell.1 visible]
  | inr cell => rfl

theorem visibleArtifactCellAddress_transport (m : Message) (pk nonce : ByteArray)
    (nodes : SharePosition → Label) (a b : Fin 256 → Pair)
    (selected : ∀ i, (a i).get (outputCodec.encode m)[i.val] =
      (b i).get (outputCodec.encode m)[i.val])
    (cell : ArtifactCell) (visible : visibleArtifactCell m cell) :
    artifactCellAddress pk nonce nodes a cell = artifactCellAddress pk nonce nodes b cell := by
  cases cell with
  | inl cell => rfl
  | inr cell =>
    change cell.2 = (outputCodec.encode m)[cell.1.val] at visible
    change commitmentQuery pk nonce cell.1.val cell.2 ((a cell.1).get cell.2) =
      commitmentQuery pk nonce cell.1.val cell.2 ((b cell.1).get cell.2)
    rw [visible, selected]

/-- With the same ciphertext coordinates, the actual restricted oracle is
unchanged by replacing opposite labels via the concrete field bijection. -/
theorem visibleProgrammedHash_field_transport (m : Message) (nonce : ByteArray) (tape : ChainTape)
    (a b : Fin 256 → Pair)
    (selected : ∀ i, (a i).get (outputCodec.encode m)[i.val] =
      (b i).get (outputCodec.encode m)[i.val]) (c : AllocatedCoefficients)
    (coordinates : (SharePosition → Bytes 64) × (CommitmentCell → Label)) (baseline : Hash) :
    visibleProgrammedHash m nonce tape b
      (fieldArtifactAnswers b (visibleCoefficientEquiv m a b selected c) coordinates) baseline =
      visibleProgrammedHash m nonce tape a (fieldArtifactAnswers a c coordinates) baseline := by
  have addresses :
      (fun cell : {cell : ArtifactCell // visibleArtifactCell m cell} =>
        artifactCellAddress (keyCodec.encode (tapePublicKey tape)) nonce (sharePositionNode tape) b cell.val) =
      (fun cell : {cell : ArtifactCell // visibleArtifactCell m cell} =>
        artifactCellAddress (keyCodec.encode (tapePublicKey tape)) nonce (sharePositionNode tape) a cell.val) := by
    funext cell
    exact (visibleArtifactCellAddress_transport m _ _ _ a b selected cell.val cell.property).symm
  have answers :
      (fun cell : {cell : ArtifactCell // visibleArtifactCell m cell} =>
        fieldArtifactAnswers b (visibleCoefficientEquiv m a b selected c) coordinates cell.val) =
      (fun cell : {cell : ArtifactCell // visibleArtifactCell m cell} =>
        fieldArtifactAnswers a c coordinates cell.val) := by
    funext cell
    exact fieldArtifactAnswers_visible_transport m a b selected c coordinates cell.val cell.property
  unfold visibleProgrammedHash
  rw [addresses, answers]

end WotsLamport.Submission
