import G1Release.Submission.PredicateMeasurable
import G1Release.Submission.CosetGameViews
import G1Release.Submission.CosetSamplerMeasure
import G1Release.Submission.ConditionalKeys

set_option maxRecDepth 4096
set_option maxHeartbeats 100000

namespace G1Release.Submission.CosetGameLaw
open SecretRelease G1Release.Protected CosetSampler CosetSlots CosetRealIdeal
open MeasureTheory ProbabilityTheory MeasurableModels

abbrev Keys := Fin 512 → Pair
local instance : MeasurableSpace Keys := ⊤

abbrev RealState (hidden : Hidden) := Keys × Randomness hidden × ROM.Oracle
abbrev ExtendedState (hidden : Hidden) := Keys × Randomness hidden × ExtendedOracle

noncomputable def realLaw (hidden : Hidden) (randomLaw : Measure (Randomness hidden)) :
    Measure (RealState hidden) :=
  (uniformOn (Set.univ : Set Keys)).prod (randomLaw.prod (OracleLaw.law (List (Fin 256))))

noncomputable def extendedLaw (hidden : Hidden) (randomLaw : Measure (Randomness hidden)) :
    Measure (ExtendedState hidden) :=
  (uniformOn (Set.univ : Set Keys)).prod (randomLaw.prod (OracleLaw.law (List (Fin 256) ⊕ CosetSlots.Slot)))

noncomputable def programState (hidden : Hidden) (input : Input)
    (state : ExtendedState hidden) : RealState hidden :=
  (state.1,state.2.1,programmed hidden state.2.1 state.1 input state.2.2)

theorem program_random_preserving (hidden : Hidden) (input : Input) (keys : Keys)
    (randomLaw : Measure (Randomness hidden)) [SFinite randomLaw] :
    MeasurePreserving (fun s : Randomness hidden × ExtendedOracle =>
      (s.1,programmed hidden s.1 keys input s.2))
      (randomLaw.prod (OracleLaw.law (List (Fin 256) ⊕ CosetSlots.Slot)))
      (randomLaw.prod (OracleLaw.law (List (Fin 256)))) := by
  refine (MeasurePreserving.id randomLaw).skew_product
    (μc := OracleLaw.law (List (Fin 256) ⊕ CosetSlots.Slot))
    (μd := OracleLaw.law (List (Fin 256)))
    (g := fun random oracle => programmed hidden random keys input oracle) ?_ ?_
  · exact measurable_from_prod_countable_right fun random =>
      (OracleLaw.program_preserving (CosetSlots.inactive keys input)
        (payload hidden random input)).measurable
  · exact Filter.Eventually.of_forall fun random =>
      (OracleLaw.program_preserving (CosetSlots.inactive keys input)
        (payload hidden random input)).map_eq

theorem programState_preserving (hidden : Hidden) (input : Input)
    (randomLaw : Measure (Randomness hidden)) [SFinite randomLaw] :
    MeasurePreserving (programState hidden input)
      (extendedLaw hidden randomLaw) (realLaw hidden randomLaw) := by
  unfold programState extendedLaw realLaw
  refine (MeasurePreserving.id (uniformOn (Set.univ : Set Keys))).skew_product
    (μc := randomLaw.prod (OracleLaw.law (List (Fin 256) ⊕ CosetSlots.Slot)))
    (μd := randomLaw.prod (OracleLaw.law (List (Fin 256))))
    (g := fun keys s => (s.1,programmed hidden s.1 keys input s.2)) ?_ ?_
  · exact measurable_from_prod_countable_right fun keys =>
      (program_random_preserving hidden input keys randomLaw).measurable
  · exact Filter.Eventually.of_forall fun keys =>
      (program_random_preserving hidden input keys randomLaw).map_eq

def realOutcome (hidden : Hidden) (input : Input) (adversary : View challenge → Program α)
    (state : RealState hidden) : α :=
  ROM.run (ROM.hash state.2.2)
    (adversary (CosetGameViews.real (ROM.hash state.2.2) hidden state.2.1 state.1 input))

def idealOutcome (hidden : Hidden) (input : Input) (adversary : View challenge → Program α)
    (state : ExtendedState hidden) : α :=
  ROM.run (ROM.hash (baseOracle state.2.2))
    (adversary (CosetGameViews.ideal hidden state.2.1 input (selected state.1 input) state.2.2))

theorem realOutcome_measurable [MeasurableSpace α] (hidden : Hidden) (input : Input)
    (adversary : View challenge → Program α) : Measurable (realOutcome hidden input adversary) :=
  measurable_from_prod_countable_right fun keys =>
    measurable_from_prod_countable_right fun random =>
      CosetGameViews.real_run_measurable hidden random keys input adversary

theorem idealOutcome_measurable [MeasurableSpace α] (hidden : Hidden) (input : Input)
    (adversary : View challenge → Program α) : Measurable (idealOutcome hidden input adversary) :=
  measurable_from_prod_countable_right fun keys =>
    measurable_from_prod_countable_right fun random =>
      CosetGameViews.ideal_run_measurable hidden random input (selected keys input) adversary

def realDistinguish (hidden : Hidden) (input : Input) (adversary : View challenge → Program Bool) :
    Set (RealState hidden) := {state | realOutcome hidden input adversary state = true}

def idealDistinguish (hidden : Hidden) (input : Input) (adversary : View challenge → Program Bool) :
    Set (ExtendedState hidden) := {state | idealOutcome hidden input adversary state = true}

theorem realDistinguish_measurable (hidden : Hidden) (input : Input)
    (adversary : View challenge → Program Bool) :
    MeasurableSet (realDistinguish hidden input adversary) :=
  realOutcome_measurable hidden input adversary (measurableSet_singleton true)

theorem idealDistinguish_measurable (hidden : Hidden) (input : Input)
    (adversary : View challenge → Program Bool) :
    MeasurableSet (idealDistinguish hidden input adversary) :=
  idealOutcome_measurable hidden input adversary (measurableSet_singleton true)

def realWin (hidden : Hidden) (input : Input) (adversary : View challenge → Program (Fin 512 × Label)) :
    Set (RealState hidden) := {state |
      (realOutcome hidden input adversary state).2 =
        (state.1 (realOutcome hidden input adversary state).1).get
          (!(inputBits input (realOutcome hidden input adversary state).1))}

theorem realWin_measurable (hidden : Hidden) (input : Input)
    (adversary : View challenge → Program (Fin 512 × Label)) :
    MeasurableSet (realWin hidden input adversary) := by
  exact PredicateMeasurable.event
    (fun (keys : Keys) (claim : Fin 512 × Label) =>
      claim.2 = (keys claim.1).get (!(inputBits input claim.1)))
    (fun state : RealState hidden => state.1)
    (realOutcome hidden input adversary) measurable_fst
    (realOutcome_measurable hidden input adversary)

end G1Release.Submission.CosetGameLaw
