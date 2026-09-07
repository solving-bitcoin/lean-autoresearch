import G1Release.Submission.CosetGameLaw
import G1Release.Submission.CosetKeyInverse

set_option maxRecDepth 4096
set_option maxHeartbeats 800000

namespace G1Release.Submission.CosetReleaseReduction
open SecretRelease G1Release.Protected CosetSampler CosetSlots CosetRealIdeal CosetGameLaw
open MeasureTheory ProbabilityTheory LamportLaw LamportGuessing CosetQueryGuessing

local instance : MeasurableSpace Keys := ⊤

theorem realOutcome_programmed (hidden : Hidden) (input : Input)
    (adversary : View challenge → Program α) (keys : Keys) (random : Randomness hidden)
    (oracle : ExtendedOracle) :
    realOutcome hidden input adversary (programState hidden input (keys,random,oracle)) =
      ROM.run (ROM.hash (programmed hidden random keys input oracle))
        (adversary (CosetGameViews.ideal hidden random input (selected keys input) oracle)) := by
  unfold realOutcome programState
  rw [CosetGameViews.real_programmed]

theorem conditioned_subset (hidden : Hidden) (random : Randomness hidden) (input : Input)
    (oracle : ExtendedOracle) (active : Fin 512 → Label)
    (adversary : View challenge → Program (Fin 512 × Label)) :
    {ranks : Fin 512 → Rank |
      programState hidden input (CosetKeyInverse.keys input active ranks,random,oracle) ∈
        realWin hidden input adversary} ⊆
    hiddenFromRanks active ⁻¹' guessesEvent active
      (guesses (ROM.hash (baseOracle oracle)) (adversary (CosetGameViews.ideal hidden random input active oracle))) := by
  intro ranks hw
  let keys := CosetKeyInverse.keys input active ranks
  let program := adversary (CosetGameViews.ideal hidden random input active oracle)
  have hwin :
      (ROM.run (ROM.hash (programmed hidden random keys input oracle)) program).2 =
        (keys (ROM.run (ROM.hash (programmed hidden random keys input oracle)) program).1).get
          (!(inputBits input (ROM.run (ROM.hash (programmed hidden random keys input oracle)) program).1)) := by
    simp only [realWin, Set.mem_setOf_eq, realOutcome_programmed, CosetKeyInverse.selected_keys] at hw
    exact hw
  have hh := win_implies_guesses hidden random keys input oracle program hwin
  obtain ⟨guess,hguess,hsecret⟩ := hh
  refine ⟨guess,hguess,?_⟩
  exact (CosetKeyInverse.opposite_keys input active ranks guess.1).symm.trans hsecret

theorem conditioned_probability_le (hidden : Hidden) (random : Randomness hidden) (input : Input)
    (oracle : ExtendedOracle) (active : Fin 512 → Label)
    (adversary : View challenge → Program (Fin 512 × Label)) (q : Nat) (ha : ROM.Bounded adversary q) :
    uniformOn (Set.univ : Set (Fin 512 → Rank))
      {ranks | programState hidden input (CosetKeyInverse.keys input active ranks,random,oracle) ∈
        realWin hidden input adversary} ≤ (q+1 : ENNReal) / (2^256-1 : Nat) := by
  apply (measure_mono (conditioned_subset hidden random input oracle active adversary)).trans
  have hm := hiddenFromRanks_preserving active
  have he : MeasurableSet (guessesEvent active
      (guesses (ROM.hash (baseOracle oracle)) (adversary (CosetGameViews.ideal hidden random input active oracle)))) :=
    MeasurableSet.of_discrete
  rw [hm.measure_preimage he.nullMeasurableSet]
  exact fixed_program_guess_bound active (ROM.hash (baseOracle oracle))
    (adversary (CosetGameViews.ideal hidden random input active oracle)) q (ha _)

/-- Release security for any independent distribution of arithmetic
randomness, not only the ideal uniform distribution. -/
theorem realWin_probability_le (hidden : Hidden) (input : Input)
    (randomLaw : Measure (Randomness hidden)) [IsProbabilityMeasure randomLaw]
    (adversary : View challenge → Program (Fin 512 × Label)) (q : Nat) (ha : ROM.Bounded adversary q) :
    realLaw hidden randomLaw (realWin hidden input adversary) ≤
      (q+1 : ENNReal) / (2^256-1 : Nat) := by
  have hm := programState_preserving hidden input randomLaw
  have he := realWin_measurable hidden input adversary
  rw [← hm.measure_preimage he.nullMeasurableSet]
  apply ConditionalKeys.bound (inputBits input)
    (randomLaw.prod (OracleLaw.law (List (Fin 256) ⊕ CosetSlots.Slot)))
    (programState hidden input ⁻¹' realWin hidden input adversary) (hm.measurable he)
  intro active context
  exact conditioned_probability_le hidden context.1 input context.2 active adversary q ha

end G1Release.Submission.CosetReleaseReduction
