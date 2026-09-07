import G1Release.Submission.GameLaw
import G1Release.Submission.SamplerMeasure

set_option maxRecDepth 4096
set_option maxHeartbeats 300000

namespace G1Release.Submission.IdealGameCoupling
open SecretRelease G1Release.Protected Randomized RealIdeal GameLaw
open MeasureTheory ProbabilityTheory

local instance : MeasurableSpace Keys := ⊤

def transport (source target : Hidden) (input : Input)
    (hequal : OffsetFamily.mapAt source input = OffsetFamily.mapAt target input)
    (state : ExtendedState source) : ExtendedState target :=
  (state.1, targetRandomness input source target hequal state.2.1, state.2.2)

theorem preserving (source target : Hidden) (input : Input)
    (hequal : OffsetFamily.mapAt source input = OffsetFamily.mapAt target input) :
    MeasurePreserving (transport source target input hequal)
      (extendedLaw source (idealLaw source)) (extendedLaw target (idealLaw target)) :=
  (MeasurePreserving.id (uniformOn (Set.univ : Set Keys))).prod
    ((randomnessEquiv_measurePreserving input source target hequal).prod
      (MeasurePreserving.id (OracleLaw.law (List (Fin 256) ⊕ IdealView.Slot))))

theorem outcome_eq (source target : Hidden) (input : Input)
    (hequal : OffsetFamily.mapAt source input = OffsetFamily.mapAt target input)
    (href : reference source input = reference target input)
    (adversary : View challenge → Program α) (state : ExtendedState source) :
    idealOutcome source input adversary state =
      idealOutcome target input adversary (transport source target input hequal state) := by
  unfold idealOutcome transport
  rw [GameViews.ideal_coupled source target input hequal href]

theorem probability_eq (source target : Hidden) (input : Input)
    (hequal : OffsetFamily.mapAt source input = OffsetFamily.mapAt target input)
    (href : reference source input = reference target input)
    (adversary : View challenge → Program Bool) :
    extendedLaw source (idealLaw source) (idealDistinguish source input adversary) =
      extendedLaw target (idealLaw target) (idealDistinguish target input adversary) := by
  have hp := preserving source target input hequal
  rw [← hp.measure_preimage (idealDistinguish_measurable target input adversary).nullMeasurableSet]
  apply congrArg (extendedLaw source (idealLaw source))
  ext state
  change (idealOutcome source input adversary state = true) ↔
    (idealOutcome target input adversary (transport source target input hequal state) = true)
  rw [outcome_eq source target input hequal href adversary state]

end G1Release.Submission.IdealGameCoupling
