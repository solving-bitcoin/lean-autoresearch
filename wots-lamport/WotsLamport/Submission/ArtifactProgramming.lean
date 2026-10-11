import WotsLamport.Submission.ArtifactAddresses
import WotsLamport.Submission.UniformOverlay

namespace WotsLamport.Submission
open SecretRelease WotsLamport.Protected

abbrev ArtifactAnswers := ArtifactCell → Label

noncomputable def programArtifactOracle (pk nonce : ByteArray)
    (nodes : SharePosition → Label) (labels : Fin 256 → Pair)
    (answers : ArtifactAnswers) (baseline : Hash) : Hash :=
  overlayOracle (artifactCellAddress pk nonce nodes labels) answers baseline

theorem programArtifactOracle_read (pk nonce : ByteArray)
    (nodes : SharePosition → Label) (labels : Fin 256 → Pair)
    (answers : ArtifactAnswers) (baseline : Hash) (cell : ArtifactCell) :
    programArtifactOracle pk nonce nodes labels answers baseline
      (artifactCellAddress pk nonce nodes labels cell) = answers cell :=
  overlayOracle_at _ _ _ (artifactCellAddress_injective pk nonce nodes labels) cell

theorem programArtifactOracle_chain (pk nonce : ByteArray)
    (nodes : SharePosition → Label) (labels : Fin 256 → Pair)
    (answers : ArtifactAnswers) (baseline : Hash) (node : Label) :
    programArtifactOracle pk nonce nodes labels answers baseline (ByteArray.mk node.toArray) =
      baseline (ByteArray.mk node.toArray) :=
  overlayOracle_off _ _ _ _ (fun cell => artifactCellAddress_ne_chain pk nonce nodes labels cell node)

/-- Mask and commitment programming never alters any 32-byte chain input. -/
theorem programArtifactOracle_consistent (pk nonce : ByteArray)
    (nodes : SharePosition → Label) (labels : Fin 256 → Pair)
    (answers : ArtifactAnswers) (baseline : Hash) (tape : ChainTape)
    (consistent : TapeConsistent baseline tape) :
    TapeConsistent (programArtifactOracle pk nonce nodes labels answers baseline) tape := by
  intro edge
  rw [programArtifactOracle_chain]
  exact consistent edge

noncomputable def programmedHash (nonce : ByteArray) (tape : ChainTape)
    (labels : Fin 256 → Pair) (answers : ArtifactAnswers) (baseline : Hash) : Hash :=
  programArtifactOracle (keyCodec.encode (tapePublicKey tape)) nonce (sharePositionNode tape)
    labels answers (programChainOracle baseline tape)

theorem programmedHash_consistent (nonce : ByteArray) (tape : ChainTape)
    (labels : Fin 256 → Pair) (answers : ArtifactAnswers) (baseline : Hash)
    (distinct : Function.Injective tape) :
    TapeConsistent (programmedHash nonce tape labels answers baseline) tape :=
  programArtifactOracle_consistent _ _ _ _ _ _ tape
    (programChainOracle_consistent baseline tape distinct)

def answerMask (answers : ArtifactAnswers) (position : SharePosition) : ByteArray :=
  ByteArray.mk (answers (Sum.inl (position,false))).toArray ++
    (ByteArray.mk (answers (Sum.inl (position,true))).toArray).extract 0 16

theorem programArtifactOracle_mask (pk nonce : ByteArray)
    (nodes : SharePosition → Label) (labels : Fin 256 → Pair)
    (answers : ArtifactAnswers) (baseline : Hash) (position : SharePosition) :
    mask (programArtifactOracle pk nonce nodes labels answers baseline) pk nonce
      position.val.1.val position.val.2.1 (position.val.2.2.val+1) (nodes position) =
      answerMask answers position := by
  have left := programArtifactOracle_read pk nonce nodes labels answers baseline
    (Sum.inl (position,false))
  have right := programArtifactOracle_read pk nonce nodes labels answers baseline
    (Sum.inl (position,true))
  change _ (maskQuery pk nonce position.val.1.val position.val.2.1
    (position.val.2.2.val+1) (nodes position) 0) = _ at left
  change _ (maskQuery pk nonce position.val.1.val position.val.2.1
    (position.val.2.2.val+1) (nodes position) 1) = _ at right
  change ByteArray.mk (_ (maskQuery pk nonce position.val.1.val position.val.2.1
    (position.val.2.2.val+1) (nodes position) 0)).toArray ++
    (ByteArray.mk (_ (maskQuery pk nonce position.val.1.val position.val.2.1
      (position.val.2.2.val+1) (nodes position) 1)).toArray).extract 0 16 = _
  rw [left,right]
  rfl

theorem programArtifactOracle_commitment (pk nonce : ByteArray)
    (nodes : SharePosition → Label) (labels : Fin 256 → Pair)
    (answers : ArtifactAnswers) (baseline : Hash) (i : Fin 256) (value : Bool) :
    commitment (programArtifactOracle pk nonce nodes labels answers baseline) pk nonce
      i.val value ((labels i).get value) = answers (Sum.inr (i,value)) :=
  programArtifactOracle_read pk nonce nodes labels answers baseline (Sum.inr (i,value))

end WotsLamport.Submission
