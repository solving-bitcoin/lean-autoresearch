import G1Release.Submission.DutyFreeReleaseReduction
import G1Release.Submission.TraceMeasurable

namespace G1Release.Submission.DutyFreeBadQueries

local instance : MeasurableSpace DutyFreeSlots.Keys := ⊤
open SecretRelease G1Release.Protected DutyFreeSlots DutyFreeRealIdeal DutyFreeGameLaw
open DutyFreeQueryGuessing MeasureTheory ProbabilityTheory
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

local instance : Countable challenge.Input := by change Countable Input; infer_instance

def event (privateValue : Private) (input : Input) (adversary : View challenge → Program α) :
    Set (ExtendedState privateValue) := {state |
      ∃ query ∈ ROMTrace.queries (ROM.hash (base state.2.2))
        (adversary (DutyFreeGameViews.ideal privateValue state.2.1 input
          (active state.1.1 input) state.1.2 state.2.2)),
        ∃ slot, address state.1.1 state.1.2 input slot = query.data.toList.map UInt8.toFin}

theorem measurable (privateValue : Private) (input : Input) (adversary : View challenge → Program α) :
    MeasurableSet (event privateValue input adversary) := by
  classical
  let hits (keys : KeyPair) (queriesFound : List ByteArray) : Bool :=
    decide (∃ query ∈ queriesFound, ∃ slot, address keys.1 keys.2 input slot =
      query.data.toList.map UInt8.toFin)
  have hm : Measurable (fun state : ExtendedState privateValue => hits state.1
      (ROMTrace.queries (ROM.hash (base state.2.2))
        (adversary (DutyFreeGameViews.ideal privateValue state.2.1 input
          (active state.1.1 input) state.1.2 state.2.2)))) := by
    apply measurable_from_prod_countable_right
    intro keys
    apply measurable_from_prod_countable_right
    intro random
    have hb : Measurable (base : ExtendedOracle → ROM.Oracle) :=
      measurable_pi_lambda _ fun query => measurable_pi_apply (Sum.inl query : List (Fin 256) ⊕ Slot)
    have ht := (TraceMeasurable.queries_variable_measurable adversary).comp
      ((DutyFreeGameViews.ideal_measurable privateValue random input (active keys.1 input) keys.2).prodMk hb)
    exact (Measurable.of_discrete : Measurable (hits keys)).comp ht
  simpa only [hits, event, Set.preimage, Set.mem_singleton_iff, decide_eq_true_eq] using
    hm (measurableSet_singleton true)

theorem conditioned_subset (privateValue : Private) (random : Randomness privateValue) (input : Input)
    (oracle : ExtendedOracle) (revealed : DutyFreeConditionalKeys.Revealed input)
    (adversary : View challenge → Program α) :
    {hidden : DutyFreeConditionalKeys.Hidden |
      (DutyFreeKeyInverse.keys input revealed hidden,random,oracle) ∈ event privateValue input adversary} ⊆
      {hidden | guessed
        (DutyFreeGuessLaw.labels revealed.1 (LamportLaw.hiddenFromRanks revealed.1 hidden.1,hidden.2))
        (queryGuesses input (ROM.hash (base oracle))
          (adversary (DutyFreeKeyInverse.view privateValue random input revealed oracle)))} := by
  intro hidden hh
  simp only [event, Set.mem_setOf_eq, DutyFreeKeyInverse.ideal_eq_view] at hh
  have hg := hit_implies_guess (DutyFreeKeyInverse.keys input revealed hidden).1
    (DutyFreeKeyInverse.keys input revealed hidden).2 input oracle
    (adversary (DutyFreeKeyInverse.view privateValue random input revealed oracle)) hh
  rw [DutyFreeKeyInverse.secret_keys] at hg
  exact hg

theorem conditioned_probability_le (privateValue : Private) (random : Randomness privateValue)
    (input : Input) (oracle : ExtendedOracle) (revealed : DutyFreeConditionalKeys.Revealed input)
    (adversary : View challenge → Program α) (q : Nat) (ha : ROM.Bounded adversary q) :
    uniformOn (Set.univ : Set DutyFreeConditionalKeys.Hidden)
      {hidden | (DutyFreeKeyInverse.keys input revealed hidden,random,oracle) ∈
        event privateValue input adversary} ≤ (q : ENNReal) / (2^256-1 : Nat) := by
  apply (measure_mono (conditioned_subset privateValue random input oracle revealed adversary)).trans
  rw [← LamportLaw.prod_uniform_univ]
  apply (DutyFreeGuessLaw.rank_guesses_bound _ _).trans
  apply ENNReal.div_le_div_right
  exact_mod_cast queryGuesses_length input (ROM.hash (base oracle))
    (adversary (DutyFreeKeyInverse.view privateValue random input revealed oracle)) q (ha _)

theorem probability_le (privateValue : Private) (input : Input)
    (randomLaw : Measure (Randomness privateValue)) [IsProbabilityMeasure randomLaw]
    (adversary : View challenge → Program α) (q : Nat) (ha : ROM.Bounded adversary q) :
    extendedLaw privateValue randomLaw (event privateValue input adversary) ≤
      (q : ENNReal) / (2^256-1 : Nat) := by
  apply DutyFreeConditionalKeys.bound input
    (randomLaw.prod (OracleLaw.law (List (Fin 256) ⊕ Slot)))
    (event privateValue input adversary) (measurable privateValue input adversary)
  intro revealed context
  exact conditioned_probability_le privateValue context.1 input context.2 revealed adversary q ha

theorem outcomes_agree (privateValue : Private) (input : Input) (adversary : View challenge → Program α)
    (state : ExtendedState privateValue) (h : state ∉ event privateValue input adversary) :
    realOutcome privateValue input adversary (programState privateValue input state) =
      idealOutcome privateValue input adversary state := by
  rw [DutyFreeReleaseReduction.realOutcome_programmed]
  exact (run_eq_without_hit state.1.1 state.1.2 input state.2.2
    (adversary (DutyFreeGameViews.ideal privateValue state.2.1 input
      (active state.1.1 input) state.1.2 state.2.2)) h).symm

end G1Release.Submission.DutyFreeBadQueries
