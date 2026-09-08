import G1Release.Submission.DutyFreeBadQueries
import G1Release.Submission.EventBounds

set_option maxRecDepth 4096
set_option maxHeartbeats 300000

namespace G1Release.Submission.DutyFreeGameHops

local instance : MeasurableSpace DutyFreeSlots.Keys := ⊤
open SecretRelease G1Release.Protected DutyFreeSlots DutyFreeRealIdeal DutyFreeGameLaw
open MeasureTheory ProbabilityTheory


theorem real_le_ideal (hidden : Private) (input : Input)
    (randomLaw : Measure (Randomness hidden)) [IsProbabilityMeasure randomLaw]
    (adversary : View challenge → Program Bool) (q : Nat) (ha : ROM.Bounded adversary q) :
    realLaw hidden randomLaw (realDistinguish hidden input adversary) ≤
      extendedLaw hidden randomLaw (idealDistinguish hidden input adversary) +
        (q : ENNReal) / (2^256-1 : Nat) := by
  have hp := programState_preserving hidden input randomLaw
  rw [← hp.measure_preimage (realDistinguish_measurable hidden input adversary).nullMeasurableSet]
  apply (EventBounds.event_le_add_bad (extendedLaw hidden randomLaw) _ _
    (DutyFreeBadQueries.event hidden input adversary) ?_).trans
      (add_le_add le_rfl (DutyFreeBadQueries.probability_le hidden input randomLaw adversary q ha))
  intro state hs hb
  change realOutcome hidden input adversary (programState hidden input state) = true at hs
  change idealOutcome hidden input adversary state = true
  rw [← DutyFreeBadQueries.outcomes_agree hidden input adversary state hb]
  exact hs

theorem ideal_le_real (hidden : Private) (input : Input)
    (randomLaw : Measure (Randomness hidden)) [IsProbabilityMeasure randomLaw]
    (adversary : View challenge → Program Bool) (q : Nat) (ha : ROM.Bounded adversary q) :
    extendedLaw hidden randomLaw (idealDistinguish hidden input adversary) ≤
      realLaw hidden randomLaw (realDistinguish hidden input adversary) +
        (q : ENNReal) / (2^256-1 : Nat) := by
  have hp := programState_preserving hidden input randomLaw
  rw [← hp.measure_preimage (realDistinguish_measurable hidden input adversary).nullMeasurableSet]
  apply (EventBounds.event_le_add_bad (extendedLaw hidden randomLaw) _ _
    (DutyFreeBadQueries.event hidden input adversary) ?_).trans
      (add_le_add le_rfl (DutyFreeBadQueries.probability_le hidden input randomLaw adversary q ha))
  intro state hs hb
  change idealOutcome hidden input adversary state = true at hs
  change realOutcome hidden input adversary (programState hidden input state) = true
  rw [DutyFreeBadQueries.outcomes_agree hidden input adversary state hb]
  exact hs

end G1Release.Submission.DutyFreeGameHops
