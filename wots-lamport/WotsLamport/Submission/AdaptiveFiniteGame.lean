import WotsLamport.Submission.AdaptiveProgrammingBridge
import WotsLamport.Submission.AdaptiveBudget
import WotsLamport.Submission.GameReductions

namespace WotsLamport.Submission
open SecretRelease WotsLamport.Protected MeasureTheory ProbabilityTheory

local instance AdaptiveFiniteGame.keysMeasurable : MeasurableSpace Keys := ⊤
local instance AdaptiveFiniteGame.labelsMeasurable : MeasurableSpace (Fin 256 → Pair) := ⊤
local instance AdaptiveFiniteGame.labelSingleton : MeasurableSingletonClass Label :=
  AfterReleaseLaw.labelSingleton
local instance AdaptiveFiniteGame.labelsSingleton : MeasurableSingletonClass (Fin 256 → Pair) :=
  ⟨fun _ => MeasurableSpace.measurableSet_top⟩

theorem raw_programmed_adaptive_bound (inputs : Finset OracleInput)
    (contains : wotsProgrammingInputs ⊆ inputs) (a : AdaptiveAdversary) (q₁ q₂ : Nat)
    (chooseBound : ROM.Bounded a.choose q₁) (finishBound : ∀ state, ROM.Bounded (a.finish state) q₂) :
    uniformOn (Set.univ : Set (RawProgrammedSample inputs)) (rawProgrammedAdaptiveEvent inputs contains a) ≤
      ((((1056 : ENNReal)^2/2^256 + ((512 : ENNReal)/2^256 + (1501 : ENNReal)*q₂/2^256)) +
        (3002 : ENNReal)*q₁/2^256) + (coefficientCount : ENNReal)*Sampler.exceptionWeight) +
        (1056 : ENNReal)^2/2^256 := by
  classical
  haveI : MeasurableSingletonClass (CombinedIdeal inputs) := inferInstance
  haveI : MeasurableSingletonClass (RawProgrammedSample inputs) := inferInstance
  haveI : DiscreteMeasurableSpace (RawProgrammedSample inputs) :=
    ⟨fun s => (Set.toFinite s).measurableSet⟩
  haveI : MeasurableSingletonClass PublicKey := inferInstance
  haveI : MeasurableSingletonClass HiddenChainTape := inferInstance
  haveI : MeasurableSingletonClass (SharePosition → Bytes 64) := inferInstance
  haveI : MeasurableSingletonClass (CommitmentCell → Label) := inferInstance
  haveI : MeasurableSingletonClass (AdaptiveAux inputs) := inferInstance
  haveI : MeasurableSingletonClass (Bytes randomnessBytes × AdaptiveAux inputs) := inferInstance
  haveI : DiscreteMeasurableSpace (Bytes randomnessBytes × AdaptiveAux inputs) :=
    ⟨fun s => (Set.toFinite s).measurableSet⟩
  have comparison := event_bound_of_agree_on_good
    (uniformOn (Set.univ : Set (RawProgrammedSample inputs)))
    (rawProgrammedAdaptiveEvent inputs contains a)
    ((rawCoinCoordinates inputs) ⁻¹' coinAdaptiveEvent inputs a)
    {sample | Function.Injective sample.2.1}
    (fun sample distinct => programmed_adaptive_event_good inputs contains a sample distinct)
  rw [Shamir.uniform_event_equiv] at comparison
  have coinBound := coin_adaptive_probability_bound inputs a q₁ q₂ chooseBound finishBound
  rw [labelTable_pi_measurable_eq_top] at coinBound
  exact comparison.trans (add_le_add coinBound (raw_tape_bad_bound inputs))

theorem finite_adaptive_outer_bound (inputs : Finset OracleInput)
    (contains : wotsProgrammingInputs ⊆ inputs) (a : AdaptiveAdversary) (q₁ q₂ : Nat)
    (chooseBound : ROM.Bounded a.choose q₁) (finishBound : ∀ state, ROM.Bounded (a.finish state) q₂) :
    uniformOn (Set.univ : Set ((Bytes randomnessBytes × (Fin 256 → Pair)) × FiniteChainReal inputs))
      {sample | sample.2 ∈ finiteAdaptiveEvent inputs sample.1.1 sample.1.2 a} ≤
      (((((1056 : ENNReal)^2/2^256 + ((512 : ENNReal)/2^256 + (1501 : ENNReal)*q₂/2^256)) +
        (3002 : ENNReal)*q₁/2^256) + (coefficientCount : ENNReal)*Sampler.exceptionWeight) +
        (1056 : ENNReal)^2/2^256) + (1056 : ENNReal)^2/2^256 := by
  classical
  have comparison := product_event_bound
    (uniformOn (Set.univ : Set (Bytes randomnessBytes × (Fin 256 → Pair))))
    (uniformOn (Set.univ : Set (FiniteChainReal inputs)))
    (uniformOn (Set.univ : Set (CombinedIdeal inputs)))
    {sample | sample.2 ∈ finiteAdaptiveEvent inputs sample.1.1 sample.1.2 a}
    (rawProgrammedAdaptiveEvent inputs contains a) ((1056 : ENNReal)^2/2^256) (by
      intro outer
      exact (combinedProgram_event_bounds inputs contains
        ((ByteArray.mk outer.1.toArray).extract 0 32) (coin_nonce_size outer.1) outer.2
        (finiteAdaptiveEvent inputs outer.1 outer.2 a)).2)
  rw [← uniform_product, ← uniform_product] at comparison
  exact comparison.trans (add_le_add
    (raw_programmed_adaptive_bound inputs contains a q₁ q₂ chooseBound finishBound) le_rfl)

theorem finite_adaptive_success (inputs : Finset OracleInput) (a : AdaptiveAdversary)
    (sample : InitialData × (inputs → Label)) :
    ROM.run (ROM.hash (extendOracleTable inputs sample.2)) (adaptiveGameProgram a sample.1) = true ↔
      (initialPreCoordinates inputs sample).2 ∈ finiteAdaptiveEvent inputs
        (initialPreCoordinates inputs sample).1.1 (initialPreCoordinates inputs sample).1.2 a := by
  exact adaptiveGame_success a
    (sample.1.1,sample.1.2.1,sample.1.2.2,extendOracleTable inputs sample.2)

/-- Actual protected infinite-oracle adaptive game, with the exact sampler,
artifact and signature. Compilation of this reduction and every prerequisite
is required before any adaptive-security claim may be made. -/
theorem construction_adaptiveSecure : AdaptiveSecure (wrapped construction) := by
  intro a q₁ q₂ hq chooseBound finishBound
  refine ⟨measurable_adaptive_event a, ?_⟩
  obtain ⟨inputs,contains,law⟩ := protected_game_finite_joint_law (adaptiveGameProgram a) wotsProgrammingInputs
  have originalEvent :
      {sample : ROM.Sample (wrapped construction) |
        ROM.run (ROM.hash sample.2.2.2) (adaptiveGameProgram a (sample.1,sample.2.1,sample.2.2.1)) = true} =
      adaptiveEvent (wrapped construction) a := by
    ext sample
    exact adaptiveGame_success a sample
  have finiteEvent :
      {sample : InitialData × (inputs → Label) |
        ROM.run (ROM.hash (extendOracleTable inputs sample.2)) (adaptiveGameProgram a sample.1) = true} =
      (initialPreCoordinates inputs) ⁻¹'
        {sample | sample.2 ∈ finiteAdaptiveEvent inputs sample.1.1 sample.1.2 a} := by
    ext sample
    exact finite_adaptive_success inputs a sample
  rw [originalEvent, finiteEvent, Shamir.uniform_event_equiv] at law
  rw [law]
  exact (finite_adaptive_outer_bound inputs contains a q₁ q₂ chooseBound finishBound).trans
    (adaptive_bound_fits_target q₁ q₂)

/-- The static post-release game is the fixed-message adaptive adversary. -/
theorem construction_releaseSecure : ROM.ReleaseSecure (wrapped construction) :=
  adaptive_implies_release (wrapped construction) construction_adaptiveSecure

end WotsLamport.Submission
