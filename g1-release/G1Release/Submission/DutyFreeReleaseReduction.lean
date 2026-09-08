import G1Release.Submission.DutyFreeGameLaw
import G1Release.Submission.DutyFreeKeyInverse

/-! An arbitrary independent arithmetic-coin distribution is sufficient for
label release security. Conditioning removes every hidden label from the
ideal view, leaving at most q oracle guesses and one final label guess. -/
namespace G1Release.Submission.DutyFreeReleaseReduction

local instance : MeasurableSpace DutyFreeSlots.Keys := ⊤
open SecretRelease G1Release.Protected DutyFreeRealIdeal DutyFreeGameLaw
open DutyFreeQueryGuessing MeasureTheory ProbabilityTheory
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

theorem realOutcome_programmed (privateValue : Private) (input : Input)
    (adversary : View challenge → Program α) (keys : KeyPair)
    (random : Randomness privateValue) (oracle : ExtendedOracle) :
    realOutcome privateValue input adversary (programState privateValue input (keys,random,oracle)) =
      ROM.run (ROM.hash (programmed keys.1 keys.2 input oracle))
        (adversary (DutyFreeGameViews.ideal privateValue random input (active keys.1 input) keys.2 oracle)) := by
  unfold realOutcome programState
  rw [DutyFreeGameViews.real_programmed]

theorem conditioned_subset (privateValue : Private) (random : Randomness privateValue) (input : Input)
    (oracle : ExtendedOracle) (revealed : DutyFreeConditionalKeys.Revealed input)
    (adversary : View challenge → Program (Fin 512 × Label)) :
    {hidden : DutyFreeConditionalKeys.Hidden |
      programState privateValue input (DutyFreeKeyInverse.keys input revealed hidden,random,oracle) ∈
        realWin privateValue input adversary} ⊆
      {hidden | guessed
        (DutyFreeGuessLaw.labels revealed.1 (LamportLaw.hiddenFromRanks revealed.1 hidden.1,hidden.2))
        (guesses input (ROM.hash (base oracle))
          (adversary (DutyFreeKeyInverse.view privateValue random input revealed oracle)))} := by
  intro hidden hw
  let keys := DutyFreeKeyInverse.keys input revealed hidden
  let program := adversary (DutyFreeKeyInverse.view privateValue random input revealed oracle)
  have hwin : challenge.wins (ROM.hash (programmed keys.1 keys.2 input oracle)) privateValue
      input keys.1 () (ROM.run (ROM.hash (programmed keys.1 keys.2 input oracle)) program) := by
    simp only [realWin, Set.mem_setOf_eq, realOutcome_programmed,
      DutyFreeKeyInverse.ideal_eq_view] at hw
    exact hw
  have hh := win_implies_guesses keys.1 keys.2 input oracle program privateValue hwin
  rw [DutyFreeKeyInverse.secret_keys] at hh
  exact hh

theorem conditioned_probability_le (privateValue : Private) (random : Randomness privateValue)
    (input : Input) (oracle : ExtendedOracle) (revealed : DutyFreeConditionalKeys.Revealed input)
    (adversary : View challenge → Program (Fin 512 × Label)) (q : Nat) (ha : ROM.Bounded adversary q) :
    uniformOn (Set.univ : Set DutyFreeConditionalKeys.Hidden)
      {hidden | programState privateValue input (DutyFreeKeyInverse.keys input revealed hidden,random,oracle) ∈
        realWin privateValue input adversary} ≤ (q+1 : ENNReal) / (2^256-1 : Nat) := by
  apply (measure_mono (conditioned_subset privateValue random input oracle revealed adversary)).trans
  rw [← LamportLaw.prod_uniform_univ]
  apply (DutyFreeGuessLaw.rank_guesses_bound _ _).trans
  apply ENNReal.div_le_div_right
  exact_mod_cast guesses_length input (ROM.hash (base oracle))
    (adversary (DutyFreeKeyInverse.view privateValue random input revealed oracle)) q (ha _)

theorem realWin_probability_le (privateValue : Private) (input : Input)
    (randomLaw : Measure (Randomness privateValue)) [IsProbabilityMeasure randomLaw]
    (adversary : View challenge → Program (Fin 512 × Label)) (q : Nat) (ha : ROM.Bounded adversary q) :
    realLaw privateValue randomLaw (realWin privateValue input adversary) ≤
      (q+1 : ENNReal) / (2^256-1 : Nat) := by
  have hm := programState_preserving privateValue input randomLaw
  have he := realWin_measurable privateValue input adversary
  rw [← hm.measure_preimage he.nullMeasurableSet]
  apply DutyFreeConditionalKeys.bound input
    (randomLaw.prod (OracleLaw.law (List (Fin 256) ⊕ DutyFreeSlots.Slot)))
    (programState privateValue input ⁻¹' realWin privateValue input adversary) (hm.measurable he)
  intro revealed context
  exact conditioned_probability_le privateValue context.1 input context.2 revealed adversary q ha

end G1Release.Submission.DutyFreeReleaseReduction
