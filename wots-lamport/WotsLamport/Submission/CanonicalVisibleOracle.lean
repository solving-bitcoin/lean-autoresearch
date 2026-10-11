import WotsLamport.Submission.FieldArtifactCoordinates
import WotsLamport.Submission.VisibleTapeOracle

namespace WotsLamport.Submission
open SecretRelease WotsLamport.Protected

/-- Canonical placeholder for undisclosed prefixes. The restricted oracle
never consults these entries; their values carry no adversarial information. -/
noncomputable def visibleTapeRepresentative (m : Message) (pk : PublicKey)
    (visible : MessageVisibleTape m) : ChainTape :=
  (messageChainPartition m).symm (pk,(fun _ => Vector.replicate 32 0),visible)

theorem visibleTapeRepresentative_publicKey (m : Message) (pk : PublicKey)
    (visible : MessageVisibleTape m) :
    tapePublicKey (visibleTapeRepresentative m pk visible) = pk :=
  congrArg Prod.fst ((messageChainPartition m).apply_symm_apply
    (pk,(fun _ => Vector.replicate 32 0),visible))

theorem visibleTapeRepresentative_visible (m : Message) (pk : PublicKey)
    (visible : MessageVisibleTape m) :
    (messageChainPartition m (visibleTapeRepresentative m pk visible)).2.2 = visible :=
  congrArg (fun sample => sample.2.2) ((messageChainPartition m).apply_symm_apply
    (pk,(fun _ => Vector.replicate 32 0),visible))

/-- All arguments are public/disclosed data or independent environmental
randomness. There is no opposite-label or hidden-prefix argument. -/
noncomputable def canonicalVisibleOracle (m : Message) (nonce : ByteArray) (pk : PublicKey)
    (visible : MessageVisibleTape m) (selected : Fin 256 → Label) (c : AllocatedCoefficients)
    (coordinates : (SharePosition → Bytes 64) × (CommitmentCell → Label)) (baseline : Hash) : Hash :=
  let labels := canonicalLabelTable (fun i => (outputCodec.encode m)[i.val]) selected
  visibleProgrammedHash m nonce (visibleTapeRepresentative m pk visible) labels
    (fieldArtifactAnswers labels c coordinates) baseline

/-- Exact separation after transporting uniformly sampled coefficients.
The transport still must be applied to the joint probability law before
using the selected-label trace bound. -/
theorem visibleOracle_canonical_form (m : Message) (nonce : ByteArray) (tape : ChainTape)
    (labels : Fin 256 → Pair) (c : AllocatedCoefficients)
    (coordinates : (SharePosition → Bytes 64) × (CommitmentCell → Label)) (baseline : Hash) :
    let bits := fun i : Fin 256 => (outputCodec.encode m)[i.val]
    let selected := fun i => (labels i).get (bits i)
    let canonical := canonicalLabelTable bits selected
    let same := fun i => (canonicalLabelTable_selected bits labels i).symm
    visibleProgrammedHash m nonce tape labels (fieldArtifactAnswers labels c coordinates) baseline =
      canonicalVisibleOracle m nonce (tapePublicKey tape) (messageChainPartition m tape).2.2
        selected (visibleCoefficientEquiv m labels canonical same c) coordinates baseline := by
  let bits : Fin 256 → Bool := fun i => (outputCodec.encode m)[i.val]
  let selected : Fin 256 → Label := fun i => (labels i).get (bits i)
  let canonical := canonicalLabelTable bits selected
  have same : ∀ i, (labels i).get (bits i) = (canonical i).get (bits i) :=
    fun i => (canonicalLabelTable_selected bits labels i).symm
  change visibleProgrammedHash m nonce tape labels (fieldArtifactAnswers labels c coordinates) baseline =
    canonicalVisibleOracle m nonce (tapePublicKey tape) (messageChainPartition m tape).2.2
      selected (visibleCoefficientEquiv m labels canonical same c) coordinates baseline
  have transport := visibleProgrammedHash_field_transport m nonce tape labels canonical same c coordinates baseline
  apply transport.symm.trans
  unfold canonicalVisibleOracle
  apply visibleProgrammedHash_tape_congr
  · exact (visibleTapeRepresentative_publicKey m _ _).symm
  · exact (visibleTapeRepresentative_visible m _ _).symm

end WotsLamport.Submission
