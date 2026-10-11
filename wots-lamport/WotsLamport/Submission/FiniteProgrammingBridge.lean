import WotsLamport.Submission.CombinedProgrammingLaw
import WotsLamport.Submission.CiphertextArtifact

namespace WotsLamport.Submission
open SecretRelease WotsLamport.Protected

/-- A finite table overlay and the byte-oracle overlay agree at every input.
All programmed addresses belong to the finite domain; outside it both retain
the same fixed fallback. No second independent oracle is introduced. -/
theorem finite_overlay_hash {I : Type} (inputs : Finset OracleInput)
    (address : I → ByteArray) (injective : Function.Injective address)
    (contains : ∀ i, oracleInput (address i) ∈ inputs)
    (answers : I → Label) (baseline : inputs → Label) :
    ROM.hash (extendOracleTable inputs
      (overlayOracle (fun i => (⟨oracleInput (address i),contains i⟩ : inputs)) answers baseline)) =
    overlayOracle address answers (ROM.hash (extendOracleTable inputs baseline)) := by
  classical
  let finiteAddress : I → inputs := fun i => ⟨oracleInput (address i),contains i⟩
  have finiteInjective : Function.Injective finiteAddress := by
    intro i j he
    exact injective (oracleInput_injective (congrArg Subtype.val he))
  funext input
  change extendOracleTable inputs (overlayOracle finiteAddress answers baseline)
      (oracleInput input) = _
  rcases Classical.em (∃ i, address i = input) with found | found
  · obtain ⟨i,rfl⟩ := found
    rw [overlayOracle_at address answers _ injective i]
    rw [extendOracleTable, dif_pos (contains i)]
    exact overlayOracle_at finiteAddress answers baseline finiteInjective i
  · have absent : ∀ i, address i ≠ input := by intro i hi; exact found ⟨i,hi⟩
    rw [overlayOracle_off address answers _ input absent]
    change extendOracleTable inputs (overlayOracle finiteAddress answers baseline)
        (oracleInput input) = extendOracleTable inputs baseline (oracleInput input)
    by_cases member : oracleInput input ∈ inputs
    · rw [extendOracleTable, dif_pos member, extendOracleTable, dif_pos member]
      apply overlayOracle_off
      intro i he
      exact absent i (oracleInput_injective (congrArg Subtype.val he))
    · simp only [extendOracleTable, dif_neg member]

theorem finiteChain_hash (inputs : Finset OracleInput)
    (contains : ∀ node : Label, oracleInput (ByteArray.mk node.toArray) ∈ inputs)
    (tape : ChainTape) (distinct : Function.Injective tape) (baseline : inputs → Label) :
    ROM.hash (extendOracleTable inputs (programFiniteChain inputs contains tape baseline)) =
      programChainOracle (ROM.hash (extendOracleTable inputs baseline)) tape := by
  rw [programChainOracle_eq_overlay]
  exact finite_overlay_hash inputs (fun edge : ChainEdge => ByteArray.mk (tape edge.val).toArray)
    (chain_address_injective tape distinct) (fun edge => contains (tape edge.val))
    (fun edge => tape (edgeNext edge)) baseline

theorem combinedProgram_hash (inputs : Finset OracleInput)
    (contains : wotsProgrammingInputs ⊆ inputs) (nonce : ByteArray)
    (nonceSize : nonce.size = 32) (labels : Fin 256 → Pair)
    (sample : CombinedIdeal inputs) (distinct : Function.Injective sample.1) :
    ROM.hash (extendOracleTable inputs
      (combinedProgram inputs contains nonce nonceSize labels sample).2) =
    programmedHash nonce sample.1 labels sample.2.1
      (ROM.hash (extendOracleTable inputs sample.2.2)) := by
  have he := finite_overlay_hash inputs
    (artifactCellAddress (keyCodec.encode (tapePublicKey sample.1)) nonce
      (sharePositionNode sample.1) labels)
    (artifactCellAddress_injective _ _ _ _)
    (artifactCellAddress_mem inputs contains _ nonce (keyCodec_size _) nonceSize
      (sharePositionNode sample.1) labels) sample.2.1
    (programFiniteChain inputs (fun node => contains (chain_input_in_programming_domain node))
      sample.1 sample.2.2)
  change ROM.hash (extendOracleTable inputs
      (combinedProgram inputs contains nonce nonceSize labels sample).2) =
    programArtifactOracle _ nonce (sharePositionNode sample.1) labels sample.2.1
      (ROM.hash (extendOracleTable inputs
        (programFiniteChain inputs (fun node => contains (chain_input_in_programming_domain node))
          sample.1 sample.2.2))) at he
  rw [finiteChain_hash inputs _ sample.1 distinct sample.2.2] at he
  exact he

/-- The oracle in the normalized joint law produces precisely the independent
ciphertext serialization, for the same coins and fixed label table. -/
theorem combinedProgram_prepare (inputs : Finset OracleInput)
    (contains : wotsProgrammingInputs ⊆ inputs) (coins : ByteArray)
    (coinSize : 32 ≤ coins.size) (labels : Fin 256 → Pair)
    (sample : CombinedIdeal inputs) (distinct : Function.Injective sample.1) :
    let nonceSize : (coins.extract 0 32).size = 32 := by rw [ByteArray.size_extract]; omega
    let real := combinedProgram inputs contains (coins.extract 0 32) nonceSize labels sample
    prepare (ROM.hash (extendOracleTable inputs real.2)) coins real.1 labels =
      ciphertextBody (coins.extract 0 32)
        (artifactCiphertextCoordinates coins labels sample.2.1).2
        (artifactCiphertextCoordinates coins labels sample.2.1).1 := by
  dsimp only
  rw [combinedProgram_hash inputs contains _ _ labels sample distinct]
  exact prepare_programmedHash_ciphertext coins sample.1 labels sample.2.1 _ distinct

end WotsLamport.Submission
