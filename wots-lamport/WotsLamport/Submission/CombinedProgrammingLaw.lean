import WotsLamport.Submission.FiniteArtifactLaw
import WotsLamport.Submission.GoodKernelSubstitution

namespace WotsLamport.Submission
open SecretRelease WotsLamport.Protected MeasureTheory ProbabilityTheory

local instance : MeasurableSpace Keys := ⊤

variable (inputs : Finset OracleInput) (contains : wotsProgrammingInputs ⊆ inputs)
    (nonce : ByteArray) (nonceSize : nonce.size = 32) (labels : Fin 256 → Pair)

abbrev CombinedIdeal := ChainTape × ((ArtifactCell → Label) × (inputs → Label))

noncomputable def combinedProgram (sample : CombinedIdeal inputs) : Keys × (inputs → Label) :=
  (tapeKeys sample.1,
    overlayOracle (finiteArtifactAddress inputs contains
      (keyCodec.encode (tapePublicKey sample.1)) nonce (keyCodec_size _) nonceSize
      (sharePositionNode sample.1) labels) sample.2.1
      (programFiniteChain inputs (fun node => contains (chain_input_in_programming_domain node))
        sample.1 sample.2.2))

/-- Actual joint key/oracle law after all chain, mask and commitment cells are
programmed, restricted only by tape collisions. Address disjointness and the
normalization of the programming fibers are proved by the imported lemmas. -/
theorem combinedProgram_good_law :
    ((uniformOn (Set.univ : Set (CombinedIdeal inputs))).restrict
      {sample | Function.Injective sample.1}).map
        (combinedProgram inputs contains nonce nonceSize labels) =
    (uniformOn (Set.univ : Set (FiniteChainReal inputs))).restrict
      {sample | Function.Injective (finiteChainRealTape inputs sample)} := by
  classical
  letI := Fintype.ofFinite Label
  have substitute := good_kernel_substitution
    (uniformOn (Set.univ : Set ChainTape))
    (uniformOn (Set.univ : Set (inputs → Label)))
    (uniformOn (Set.univ : Set ((ArtifactCell → Label) × (inputs → Label))))
    {tape | Function.Injective tape}
    (finiteChainProgram inputs (fun node => contains (chain_input_in_programming_domain node)))
    (combinedProgram inputs contains nonce nonceSize labels) (by
      intro tape distinct event
      exact finite_artifact_chain_event inputs contains (keyCodec.encode (tapePublicKey tape))
        nonce (keyCodec_size _) nonceSize (sharePositionNode tape) labels tape distinct event)
  rw [← uniform_product, ← uniform_product] at substitute
  exact substitute.symm.trans
    (finiteChainProgram_good_law inputs (fun node => contains (chain_input_in_programming_domain node)))

/-- Any event on the actual keys and full finite oracle differs from the
complete independently sampled programming construction by at most the
ideal-tape collision mass. Coins and label tables may subsequently be
adjoined independently; no prepared-artifact independence is assumed here. -/
theorem combinedProgram_event_bounds (event : Set (FiniteChainReal inputs)) :
    uniformOn (Set.univ : Set (CombinedIdeal inputs))
        ((combinedProgram inputs contains nonce nonceSize labels) ⁻¹' event) ≤
      uniformOn (Set.univ : Set (FiniteChainReal inputs)) event +
        (1056 : ENNReal)^2 / 2^256 ∧
    uniformOn (Set.univ : Set (FiniteChainReal inputs)) event ≤
      uniformOn (Set.univ : Set (CombinedIdeal inputs))
        ((combinedProgram inputs contains nonce nonceSize labels) ⁻¹' event) +
        (1056 : ENNReal)^2 / 2^256 := by
  classical
  letI := Fintype.ofFinite Label
  have bad : uniformOn (Set.univ : Set (CombinedIdeal inputs))
      {sample | Function.Injective sample.1}ᶜ ≤ (1056 : ENNReal)^2 / 2^256 := by
    have bad_eq : ({sample : CombinedIdeal inputs | Function.Injective sample.1}ᶜ) =
        {tape | ¬Function.Injective tape} ×ˢ
          (Set.univ : Set ((ArtifactCell → Label) × (inputs → Label))) := by
      ext sample
      simp only [Set.mem_compl_iff, Set.mem_setOf_eq, Set.mem_prod, Set.mem_univ, and_true]
    rw [bad_eq]
    rw [uniform_product, Measure.prod_prod, measure_univ, mul_one]
    exact uniform_chainTape_collision_bound
  have bounds := good_law_event_bounds
    (uniformOn (Set.univ : Set (CombinedIdeal inputs)))
    (uniformOn (Set.univ : Set (FiniteChainReal inputs)))
    (combinedProgram inputs contains nonce nonceSize labels) _ _
    (combinedProgram_good_law inputs contains nonce nonceSize labels) event
  exact ⟨bounds.1.trans (add_le_add le_rfl bad), bounds.2.trans (add_le_add le_rfl bad)⟩

end WotsLamport.Submission
