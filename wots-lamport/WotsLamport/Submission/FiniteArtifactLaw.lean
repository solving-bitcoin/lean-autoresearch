import WotsLamport.Submission.FiniteChainLaw
import WotsLamport.Submission.ArtifactAddresses
import WotsLamport.Submission.UniformOverlay

namespace WotsLamport.Submission
open SecretRelease WotsLamport.Protected MeasureTheory ProbabilityTheory

theorem oracleInput_injective : Function.Injective oracleInput := by
  intro a b he
  apply ByteArray.ext
  apply Array.toList_inj.mp
  exact (List.map_inj_right (fun x y h => UInt8.toFin_inj.mp h)).mp he

variable (inputs : Finset OracleInput) (contains : wotsProgrammingInputs ⊆ inputs)
  (pk nonce : ByteArray) (pkSize : pk.size = 2144) (nonceSize : nonce.size = 32)
  (nodes : SharePosition → Label) (labels : Fin 256 → Pair)

include contains pkSize nonceSize

theorem artifactCellAddress_mem (cell : ArtifactCell) :
    oracleInput (artifactCellAddress pk nonce nodes labels cell) ∈ inputs := by
  apply contains
  cases cell with
  | inl cell => exact mask_input_in_programming_domain pk nonce pkSize nonceSize _ _ _ _ _
  | inr cell => exact commitment_input_in_programming_domain pk nonce pkSize nonceSize _ _ _

def finiteArtifactAddress (cell : ArtifactCell) : inputs :=
  ⟨oracleInput (artifactCellAddress pk nonce nodes labels cell),
    artifactCellAddress_mem inputs contains pk nonce pkSize nonceSize nodes labels cell⟩

theorem finiteArtifactAddress_injective :
    Function.Injective (finiteArtifactAddress inputs contains pk nonce pkSize nonceSize nodes labels) := by
  intro a b he
  apply artifactCellAddress_injective pk nonce nodes labels
  apply oracleInput_injective
  exact congrArg Subtype.val he

/-- Actual mask and commitment addresses, including their embedded secrets,
form an injective family in the common fixed oracle domain. Uniform fresh
answers can replace those cells while retaining the entire oracle jointly. -/
theorem finite_artifact_programming_law
    (event : Set ((ArtifactCell → Label) × (inputs → Label))) :
    uniformOn (Set.univ : Set ((ArtifactCell → Label) × (inputs → Label)))
      {sample | (sample.1, overlayOracle
        (finiteArtifactAddress inputs contains pk nonce pkSize nonceSize nodes labels)
        sample.1 sample.2) ∈ event} =
    uniformOn (Set.univ : Set (inputs → Label))
      {oracle | (oracle ∘
        finiteArtifactAddress inputs contains pk nonce pkSize nonceSize nodes labels,
        oracle) ∈ event} := by
  classical
  exact uniform_overlay_joint_event _
    (finiteArtifactAddress_injective inputs contains pk nonce pkSize nonceSize nodes labels) event

/-- Programming these actual cells preserves all finite-domain chain reads. -/
theorem finiteArtifactAddress_ne_chain (cell : ArtifactCell) (node : Label)
    (chainMember : oracleInput (ByteArray.mk node.toArray) ∈ inputs) :
    finiteArtifactAddress inputs contains pk nonce pkSize nonceSize nodes labels cell ≠
      ⟨oracleInput (ByteArray.mk node.toArray), chainMember⟩ := by
  intro he
  exact artifactCellAddress_ne_chain pk nonce nodes labels cell node
    (oracleInput_injective (congrArg Subtype.val he))

/-- On a collision-free tape, the two actual programming families commute.
The disjointness is established from serialized input widths, not assumed. -/
theorem finite_artifact_chain_programming_commute (tape : ChainTape)
    (distinct : Function.Injective tape) (answers : ArtifactCell → Label)
    (baseline : inputs → Label) :
    overlayOracle (finiteArtifactAddress inputs contains pk nonce pkSize nonceSize nodes labels)
      answers (programFiniteChain inputs
        (fun node => contains (chain_input_in_programming_domain node)) tape baseline) =
    programFiniteChain inputs
      (fun node => contains (chain_input_in_programming_domain node)) tape
      (overlayOracle (finiteArtifactAddress inputs contains pk nonce pkSize nonceSize nodes labels)
        answers baseline) := by
  apply overlayOracle_commute
    (finiteArtifactAddress inputs contains pk nonce pkSize nonceSize nodes labels)
    (finiteChainAddress inputs (fun node => contains (chain_input_in_programming_domain node)) tape)
    (finiteArtifactAddress_injective inputs contains pk nonce pkSize nonceSize nodes labels)
    (finiteChainAddress_injective inputs _ tape distinct)
  intro cell edge
  exact finiteArtifactAddress_ne_chain inputs contains pk nonce pkSize nonceSize nodes labels cell
    (tape edge.val) _

/-- The fresh artifact-answer law remains exact after the chain oracle is
programmed. This transports the entire final oracle, not just its mask reads. -/
theorem finite_artifact_chain_event (tape : ChainTape)
    (distinct : Function.Injective tape) (event : Set (Keys × (inputs → Label))) :
    uniformOn (Set.univ : Set (inputs → Label))
      {baseline | (tapeKeys tape, programFiniteChain inputs
        (fun node => contains (chain_input_in_programming_domain node)) tape baseline) ∈ event} =
    uniformOn (Set.univ : Set ((ArtifactCell → Label) × (inputs → Label)))
      {sample | (tapeKeys tape,
        overlayOracle (finiteArtifactAddress inputs contains pk nonce pkSize nonceSize nodes labels)
          sample.1 (programFiniteChain inputs
            (fun node => contains (chain_input_in_programming_domain node)) tape sample.2)) ∈ event} := by
  classical
  have he := finite_artifact_programming_law inputs contains pk nonce pkSize nonceSize nodes labels
    {sample | (tapeKeys tape, programFiniteChain inputs
      (fun node => contains (chain_input_in_programming_domain node)) tape sample.2) ∈ event}
  calc
    _ = uniformOn (Set.univ : Set ((ArtifactCell → Label) × (inputs → Label)))
        {sample | (tapeKeys tape, programFiniteChain inputs
          (fun node => contains (chain_input_in_programming_domain node)) tape
          (overlayOracle (finiteArtifactAddress inputs contains pk nonce pkSize nonceSize nodes labels)
            sample.1 sample.2)) ∈ event} := he.symm
    _ = _ := by
      congr 1
      ext sample
      simp only [Set.mem_setOf_eq]
      rw [← finite_artifact_chain_programming_commute inputs contains pk nonce pkSize nonceSize
        nodes labels tape distinct sample.1 sample.2]

end WotsLamport.Submission
