import G1Release.Submission.ReleaseReduction
import G1Release.Submission.TraceMeasurable

set_option maxRecDepth 4096
set_option maxHeartbeats 800000

namespace G1Release.Submission.BadQueries
open SecretRelease G1Release.Protected Randomized RealIdeal GameLaw
open MeasureTheory ProbabilityTheory LamportLaw LamportGuessing QueryGuessing

local instance : MeasurableSpace Keys := ⊤

def event (hidden : Hidden) (input : Input) (adversary : View challenge → Program α) :
    Set (ExtendedState hidden) := {state |
      ∃ query ∈ ROMTrace.queries (ROM.hash (baseOracle state.2.2))
        (adversary (GameViews.ideal hidden state.2.1 input (selected state.1 input) state.2.2)),
        ∃ slot, SlotAddresses.inactive state.1 input slot = query.data.toList.map UInt8.toFin}

theorem measurable (hidden : Hidden) (input : Input) (adversary : View challenge → Program α) :
    MeasurableSet (event hidden input adversary) := by
  classical
  let hits (keys : Keys) (queriesFound : List ByteArray) : Bool :=
    decide (∃ query ∈ queriesFound, ∃ slot, SlotAddresses.inactive keys input slot =
      query.data.toList.map UInt8.toFin)
  have hm : Measurable (fun state : ExtendedState hidden => hits state.1
      (ROMTrace.queries (ROM.hash (baseOracle state.2.2))
        (adversary (GameViews.ideal hidden state.2.1 input (selected state.1 input) state.2.2)))) := by
    apply measurable_from_prod_countable_right
    intro keys
    apply measurable_from_prod_countable_right
    intro random
    have hs : Measurable (hits keys) := Measurable.of_discrete
    have hr := TraceMeasurable.ideal_trace_measurable hidden random input (selected keys input) adversary
    have hc := hs.comp hr
    exact hc
  simpa only [hits, event, Set.preimage, Set.mem_singleton_iff, decide_eq_true_eq] using hm (measurableSet_singleton true)

theorem hit_implies_guesses (keys : Keys) (input : Input) (hash : Hash) (program : Program α)
    (hh : ∃ query ∈ ROMTrace.queries hash program,
      ∃ slot, SlotAddresses.inactive keys input slot = query.data.toList.map UInt8.toFin) :
    oppositeKeys keys input ∈ guessesEvent (selected keys input) (queryGuesses hash program) := by
  obtain ⟨query,hquery,slot,hslot⟩ := hh
  let g : Fin 512 × Label :=
    (SlotAddresses.wire slot, (keys (SlotAddresses.wire slot)).get (!(SlotAddresses.bit input slot)))
  have hd : byteGuess query = some g := by
    unfold byteGuess
    rw [← hslot]
    change listGuess (encoded (slot,g.2)) = some g
    exact listGuess_encoded (slot,g.2)
  exact ⟨g,List.mem_filterMap.mpr ⟨query,hquery,hd⟩,oppositeKeys_slot keys input slot⟩

theorem conditioned_subset (hidden : Hidden) (random : Randomness hidden) (input : Input)
    (oracle : ExtendedOracle) (active : Fin 512 → Label) (adversary : View challenge → Program α) :
    {ranks : Fin 512 → Rank | (KeyInverse.keys input active ranks,random,oracle) ∈ event hidden input adversary} ⊆
      hiddenFromRanks active ⁻¹' guessesEvent active
        (queryGuesses (ROM.hash (baseOracle oracle)) (adversary (GameViews.ideal hidden random input active oracle))) := by
  intro ranks hr
  simp only [event, Set.mem_setOf_eq, KeyInverse.selected_keys] at hr
  have hh := hit_implies_guesses (KeyInverse.keys input active ranks) input
    (ROM.hash (baseOracle oracle)) (adversary (GameViews.ideal hidden random input active oracle)) hr
  obtain ⟨guess,hguess,hsecret⟩ := hh
  exact ⟨guess,hguess,(KeyInverse.opposite_keys input active ranks guess.1).symm.trans hsecret⟩

theorem conditioned_probability_le (hidden : Hidden) (random : Randomness hidden) (input : Input)
    (oracle : ExtendedOracle) (active : Fin 512 → Label) (adversary : View challenge → Program α)
    (q : Nat) (ha : ROM.Bounded adversary q) :
    uniformOn (Set.univ : Set (Fin 512 → Rank))
      {ranks | (KeyInverse.keys input active ranks,random,oracle) ∈ event hidden input adversary} ≤
        (q : ENNReal) / (2^256-1 : Nat) := by
  apply (measure_mono (conditioned_subset hidden random input oracle active adversary)).trans
  let gs := queryGuesses (ROM.hash (baseOracle oracle)) (adversary (GameViews.ideal hidden random input active oracle))
  have he : MeasurableSet (guessesEvent active gs) := MeasurableSet.of_discrete
  rw [(hiddenFromRanks_preserving active).measure_preimage he.nullMeasurableSet]
  apply (guesses_probability_le active gs).trans
  apply ENNReal.div_le_div_right
  exact_mod_cast queryGuesses_length (ROM.hash (baseOracle oracle))
    (adversary (GameViews.ideal hidden random input active oracle)) q (ha _)

theorem probability_le (hidden : Hidden) (input : Input)
    (randomLaw : Measure (Randomness hidden)) [IsProbabilityMeasure randomLaw]
    (adversary : View challenge → Program α) (q : Nat) (ha : ROM.Bounded adversary q) :
    extendedLaw hidden randomLaw (event hidden input adversary) ≤
      (q : ENNReal) / (2^256-1 : Nat) := by
  apply ConditionalKeys.bound (inputBits input)
    (randomLaw.prod (OracleLaw.law (List (Fin 256) ⊕ IdealView.Slot)))
    (event hidden input adversary) (measurable hidden input adversary)
  intro active context
  exact conditioned_probability_le hidden context.1 input context.2 active adversary q ha

theorem outcomes_agree (hidden : Hidden) (input : Input) (adversary : View challenge → Program α)
    (state : ExtendedState hidden) (h : state ∉ event hidden input adversary) :
    realOutcome hidden input adversary (programState hidden input state) =
      idealOutcome hidden input adversary state := by
  rw [ReleaseReduction.realOutcome_programmed]
  exact (run_eq_without_hit hidden state.2.1 state.1 input state.2.2
    (adversary (GameViews.ideal hidden state.2.1 input (selected state.1 input) state.2.2)) h).symm

end G1Release.Submission.BadQueries
