import WotsLamport.Submission.BeforeReleaseCoordinates
import WotsLamport.Submission.ProductEventBounds
import WotsLamport.Submission.GroupedOracleLaw
import WotsLamport.Submission.WithholdingBudget

namespace WotsLamport.Submission
open SecretRelease WotsLamport.Protected MeasureTheory ProbabilityTheory OracleComp

local instance PreReleaseFiniteGame.labelSingleton : MeasurableSingletonClass Label :=
  ⟨fun _ => MeasurableSpace.measurableSet_top⟩
local instance PreReleaseFiniteGame.pairSingleton : MeasurableSingletonClass Pair := inferInstance

/-- The finite label table's product sigma algebra contains every set. -/
theorem labelTable_pi_measurable_eq_top :
    (MeasurableSpace.pi : MeasurableSpace (Fin 256 → Pair)) = ⊤ := by
  apply top_unique
  intro s _
  exact MeasurableSet.of_discrete

local instance PreReleaseFiniteGame.keysMeasurable : MeasurableSpace Keys := ⊤
local instance PreReleaseFiniteGame.labelsMeasurable : MeasurableSpace (Fin 256 → Pair) := ⊤
local instance PreReleaseFiniteGame.labelsSingleton : MeasurableSingletonClass (Fin 256 → Pair) :=
  ⟨fun _ => MeasurableSpace.measurableSet_top⟩

theorem coin_bytes_long (coins : Bytes randomnessBytes) :
    32 ≤ (ByteArray.mk coins.toArray).size := by
  rw [vectorBytes_size]
  decide +kernel

theorem coin_nonce_size (coins : Bytes randomnessBytes) :
    ((ByteArray.mk coins.toArray).extract 0 32).size = 32 := by
  rw [ByteArray.size_extract]
  have := coin_bytes_long coins
  omega

def finitePreEvent (inputs : Finset OracleInput) (coins : Bytes randomnessBytes)
    (labels : Fin 256 → Pair) (m : Message)
    (a : PreReleaseView challenge → Program challenge.Claim) : Set (FiniteChainReal inputs) :=
  {sample | let h := ROM.hash (extendOracleTable inputs sample.2)
    let artifact := keyCodec.encode (publicKey h sample.1) ++
      prepare h (ByteArray.mk coins.toArray) sample.1 labels
    let claim := ROM.run h (a ⟨m,artifact⟩)
    claim.2 = (labels claim.1).get false ∨ claim.2 = (labels claim.1).get true}

def rawProgrammedPreEvent (inputs : Finset OracleInput)
    (contains : wotsProgrammingInputs ⊆ inputs) (m : Message)
    (a : PreReleaseView challenge → Program challenge.Claim) : Set (RawProgrammedSample inputs) :=
  {sample | combinedProgram inputs contains ((ByteArray.mk sample.1.1.toArray).extract 0 32)
      (coin_nonce_size sample.1.1) sample.1.2 sample.2 ∈
    finitePreEvent inputs sample.1.1 sample.1.2 m a}

def beforeWinEvent (inputs : Finset OracleInput) (m : Message)
    (a : PreReleaseView challenge → Program challenge.Claim) :
    Set (BeforeEnvironment inputs × HiddenSetup) :=
  {sample | let claim := ROM.run (beforeHash sample.1 sample.2) (a ⟨m,beforeArtifact sample.1⟩)
    claim.2 = (sample.2.2 claim.1).get false ∨ claim.2 = (sample.2.2 claim.1).get true}

theorem beforeHash_coordinates (inputs : Finset OracleInput) (sample : RawProgrammedSample inputs) :
    beforeHash (beforeReleaseCoordinates inputs sample).1 (beforeReleaseCoordinates inputs sample).2 =
      programmedHash ((ByteArray.mk sample.1.1.toArray).extract 0 32) sample.2.1 sample.1.2 sample.2.2.1
        (ROM.hash (extendOracleTable inputs sample.2.2.2)) := by
  simp only [beforeHash, beforeAnswers, beforeReleaseCoordinates, Equiv.coe_fn_mk,
    Prod.eta, Equiv.symm_apply_apply]

theorem beforeArtifact_coordinates (inputs : Finset OracleInput) (sample : RawProgrammedSample inputs) :
    beforeArtifact (beforeReleaseCoordinates inputs sample).1 =
      keyCodec.encode (tapePublicKey sample.2.1) ++
        ciphertextBody ((ByteArray.mk sample.1.1.toArray).extract 0 32)
          (artifactCiphertextCoordinates (ByteArray.mk sample.1.1.toArray) sample.1.2 sample.2.2.1).2
          (artifactCiphertextCoordinates (ByteArray.mk sample.1.1.toArray) sample.1.2 sample.2.2.1).1 := rfl

theorem programmed_pre_event_good (inputs : Finset OracleInput)
    (contains : wotsProgrammingInputs ⊆ inputs) (m : Message)
    (a : PreReleaseView challenge → Program challenge.Claim)
    (sample : RawProgrammedSample inputs) (distinct : Function.Injective sample.2.1) :
    sample ∈ rawProgrammedPreEvent inputs contains m a ↔
      beforeReleaseCoordinates inputs sample ∈ beforeWinEvent inputs m a := by
  let h := programmedHash ((ByteArray.mk sample.1.1.toArray).extract 0 32)
    sample.2.1 sample.1.2 sample.2.2.1 (ROM.hash (extendOracleTable inputs sample.2.2.2))
  have consistent : TapeConsistent h sample.2.1 := programmedHash_consistent _ _ _ _ _ distinct
  change
    (let claim := ROM.run
        (ROM.hash (extendOracleTable inputs (combinedProgram inputs contains
          ((ByteArray.mk sample.1.1.toArray).extract 0 32) (coin_nonce_size sample.1.1) sample.1.2 sample.2).2))
        (a ⟨m, keyCodec.encode (publicKey
          (ROM.hash (extendOracleTable inputs (combinedProgram inputs contains
            ((ByteArray.mk sample.1.1.toArray).extract 0 32) (coin_nonce_size sample.1.1) sample.1.2 sample.2).2))
          (tapeKeys sample.2.1)) ++ prepare
          (ROM.hash (extendOracleTable inputs (combinedProgram inputs contains
            ((ByteArray.mk sample.1.1.toArray).extract 0 32) (coin_nonce_size sample.1.1) sample.1.2 sample.2).2))
          (ByteArray.mk sample.1.1.toArray) (tapeKeys sample.2.1) sample.1.2⟩)
     claim.2 = (sample.1.2 claim.1).get false ∨ claim.2 = (sample.1.2 claim.1).get true) ↔ _
  rw [combinedProgram_hash inputs contains _ _ sample.1.2 sample.2 distinct]
  rw [publicKey_tape h sample.2.1 consistent,
    prepare_programmedHash_ciphertext _ _ _ _ _ distinct]
  simp only [beforeWinEvent, Set.mem_setOf_eq, beforeHash_coordinates, beforeArtifact_coordinates]
  rfl

theorem raw_tape_bad_bound (inputs : Finset OracleInput) :
    uniformOn (Set.univ : Set (RawProgrammedSample inputs))
      {sample | Function.Injective sample.2.1}ᶜ ≤ (1056 : ENNReal)^2/2^256 := by
  classical
  have outer_eq : ({sample : RawProgrammedSample inputs | Function.Injective sample.2.1}ᶜ) =
      (Set.univ : Set (Bytes randomnessBytes × (Fin 256 → Pair))) ×ˢ
        {sample : CombinedIdeal inputs | ¬Function.Injective sample.1} := by
    ext sample
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, Set.mem_prod, Set.mem_univ, true_and]
  rw [outer_eq]
  rw [uniform_product, Measure.prod_prod, measure_univ, one_mul]
  have inner_eq : {sample : CombinedIdeal inputs | ¬Function.Injective sample.1} =
      {tape | ¬Function.Injective tape} ×ˢ
        (Set.univ : Set ((ArtifactCell → Label) × (inputs → Label))) := by
    ext sample
    simp only [Set.mem_setOf_eq, Set.mem_prod, Set.mem_univ, and_true]
  rw [inner_eq]
  rw [uniform_product, Measure.prod_prod, measure_univ, mul_one]
  exact uniform_chainTape_collision_bound

/-- The conditional trace/guessing theorem holds for the entire independent
pre-release environment, including coefficients, the public key and oracle. -/
theorem before_release_product_bound (inputs : Finset OracleInput) (m : Message)
    (a : PreReleaseView challenge → Program challenge.Claim) (q : Nat) (bound : ROM.Bounded a q) :
    uniformOn (Set.univ : Set (BeforeEnvironment inputs × HiddenSetup))
      (beforeWinEvent inputs m a) ≤ (4 : ENNReal)/2^256 + (3002 : ENNReal)*q/2^256 := by
  classical
  rw [uniform_product]
  apply product_event_constant_bound
  intro environment
  have h := before_release_fiber_bound inputs environment m a q bound
  rw [labelTable_pi_measurable_eq_top] at h
  simpa only [beforeWinEvent, Set.mem_setOf_eq] using h

theorem raw_programmed_pre_bound (inputs : Finset OracleInput)
    (contains : wotsProgrammingInputs ⊆ inputs) (m : Message)
    (a : PreReleaseView challenge → Program challenge.Claim) (q : Nat) (bound : ROM.Bounded a q) :
    uniformOn (Set.univ : Set (RawProgrammedSample inputs))
      (rawProgrammedPreEvent inputs contains m a) ≤
        ((4 : ENNReal)/2^256 + (3002 : ENNReal)*q/2^256) + (1056 : ENNReal)^2/2^256 := by
  classical
  haveI : MeasurableSingletonClass (CombinedIdeal inputs) := inferInstance
  haveI : MeasurableSingletonClass (RawProgrammedSample inputs) := inferInstance
  haveI : DiscreteMeasurableSpace (RawProgrammedSample inputs) :=
    ⟨fun s => (Set.toFinite s).measurableSet⟩
  haveI : MeasurableSingletonClass (BeforeEnvironment inputs) := inferInstance
  haveI : MeasurableSingletonClass HiddenSetup := inferInstance
  haveI : MeasurableSingletonClass (BeforeEnvironment inputs × HiddenSetup) := inferInstance
  haveI : DiscreteMeasurableSpace (BeforeEnvironment inputs × HiddenSetup) :=
    ⟨fun s => (Set.toFinite s).measurableSet⟩
  have comparison := event_bound_of_agree_on_good
    (uniformOn (Set.univ : Set (RawProgrammedSample inputs)))
    (rawProgrammedPreEvent inputs contains m a)
    ((beforeReleaseCoordinates inputs) ⁻¹' beforeWinEvent inputs m a)
    {sample | Function.Injective sample.2.1}
    (fun sample distinct => programmed_pre_event_good inputs contains m a sample distinct)
  rw [Shamir.uniform_event_equiv (beforeReleaseCoordinates inputs)] at comparison
  exact comparison.trans (add_le_add (before_release_product_bound inputs m a q bound)
    (raw_tape_bad_bound inputs))

/-- First compare the actual finite key/oracle law with the independent
programming sample, then apply exact artifact reserialization and its bound. -/
theorem finite_pre_outer_bound (inputs : Finset OracleInput)
    (contains : wotsProgrammingInputs ⊆ inputs) (m : Message)
    (a : PreReleaseView challenge → Program challenge.Claim) (q : Nat) (bound : ROM.Bounded a q) :
    uniformOn (Set.univ : Set ((Bytes randomnessBytes × (Fin 256 → Pair)) × FiniteChainReal inputs))
      {sample | sample.2 ∈ finitePreEvent inputs sample.1.1 sample.1.2 m a} ≤
      (((4 : ENNReal)/2^256 + (3002 : ENNReal)*q/2^256) +
        (1056 : ENNReal)^2/2^256) + (1056 : ENNReal)^2/2^256 := by
  classical
  have comparison := product_event_bound
    (uniformOn (Set.univ : Set (Bytes randomnessBytes × (Fin 256 → Pair))))
    (uniformOn (Set.univ : Set (FiniteChainReal inputs)))
    (uniformOn (Set.univ : Set (CombinedIdeal inputs)))
    {sample | sample.2 ∈ finitePreEvent inputs sample.1.1 sample.1.2 m a}
    (rawProgrammedPreEvent inputs contains m a) ((1056 : ENNReal)^2/2^256) (by
      intro outer
      exact (combinedProgram_event_bounds inputs contains
        ((ByteArray.mk outer.1.toArray).extract 0 32) (coin_nonce_size outer.1) outer.2
        (finitePreEvent inputs outer.1 outer.2 m a)).2)
  rw [← uniform_product, ← uniform_product] at comparison
  exact comparison.trans (add_le_add (raw_programmed_pre_bound inputs contains m a q bound) le_rfl)

/-- Only a permutation of the independently sampled initial coordinates. -/
def initialPreCoordinates (inputs : Finset OracleInput) :
    (InitialData × (inputs → Label)) ≃
      ((Bytes randomnessBytes × (Fin 256 → Pair)) × FiniteChainReal inputs) where
  toFun sample := ((sample.1.2.2, sample.1.2.1), (sample.1.1, sample.2))
  invFun sample := ((sample.2.1, sample.1.2, sample.1.1), sample.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

theorem finite_withholding_success (inputs : Finset OracleInput) (m : Message)
    (a : PreReleaseView challenge → Program challenge.Claim)
    (sample : InitialData × (inputs → Label)) :
    ROM.run (ROM.hash (extendOracleTable inputs sample.2))
      (withholdingGameProgram m a sample.1) = true ↔
      (initialPreCoordinates inputs sample).2 ∈
        finitePreEvent inputs (initialPreCoordinates inputs sample).1.1
          (initialPreCoordinates inputs sample).1.2 m a := by
  simp only [withholdingGameProgram, preReleaseViewProgram, run_bind, run_map,
    run_pure, run_wrappedPrepareProgram, decide_eq_true_eq]
  rfl

/-- Actual protected infinite-oracle withholding game. The two collision
losses arise from joint-law comparison and agreement on injective tapes. -/
theorem withholding_probability_bound (m : Message)
    (a : PreReleaseView challenge → Program challenge.Claim)
    (q : Nat) (bound : ROM.Bounded a q) :
    ROM.law (wrapped construction)
      (ROM.preReleaseEvent (wrapped construction)
        (fun _ _ _ _ labels claim => claim.2 = (labels claim.1).get false ∨
          claim.2 = (labels claim.1).get true) () m a) ≤
      (((4 : ENNReal)/2^256 + (3002 : ENNReal)*q/2^256) +
        (1056 : ENNReal)^2/2^256) + (1056 : ENNReal)^2/2^256 := by
  classical
  obtain ⟨inputs, contains, law⟩ :=
    protected_game_finite_joint_law (withholdingGameProgram m a) wotsProgrammingInputs
  have originalEvent :
      {sample : ROM.Sample (wrapped construction) |
        ROM.run (ROM.hash sample.2.2.2)
          (withholdingGameProgram m a (sample.1, sample.2.1, sample.2.2.1)) = true} =
      ROM.preReleaseEvent (wrapped construction)
        (fun _ _ _ _ labels claim => claim.2 = (labels claim.1).get false ∨
          claim.2 = (labels claim.1).get true) () m a := by
    ext sample
    exact withholdingGame_success m a sample
  have finiteEvent :
      {sample : InitialData × (inputs → Label) |
        ROM.run (ROM.hash (extendOracleTable inputs sample.2))
          (withholdingGameProgram m a sample.1) = true} =
      (initialPreCoordinates inputs) ⁻¹'
        {sample | sample.2 ∈ finitePreEvent inputs sample.1.1 sample.1.2 m a} := by
    ext sample
    exact finite_withholding_success inputs m a sample
  rw [originalEvent, finiteEvent, Shamir.uniform_event_equiv] at law
  rw [law]
  exact finite_pre_outer_bound inputs contains m a q bound

/-- Withholding only. This does not supply the post-release or adaptive
security fields and therefore is not a complete certificate. -/
theorem construction_withholdingSecure : ROM.WithholdingSecure (wrapped construction) := by
  intro p m q hq a bound
  cases p
  exact ⟨measurable_withholding_event m a,
    (withholding_probability_bound m a q bound).trans (withholding_bound_fits_target q)⟩

end WotsLamport.Submission
