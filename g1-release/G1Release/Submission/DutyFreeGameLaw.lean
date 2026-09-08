import G1Release.Submission.DutyFreeGameViews
import G1Release.Submission.DutyFreeConditionalKeys
import G1Release.Submission.PredicateMeasurable

namespace G1Release.Submission.DutyFreeGameLaw

local instance : MeasurableSpace DutyFreeSlots.Keys := ⊤
open SecretRelease G1Release.Protected DutyFreeSlots DutyFreeRealIdeal
open MeasureTheory ProbabilityTheory
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

abbrev KeyPair := DutyFreeConditionalKeys.KeyPair
abbrev Randomness := CosetSampler.Randomness
abbrev RealState (hidden : Private) := KeyPair × Randomness hidden × ROM.Oracle
abbrev ExtendedState (hidden : Private) := KeyPair × Randomness hidden × ExtendedOracle

noncomputable def realLaw (hidden : Private) (randomLaw : Measure (Randomness hidden)) :
    Measure (RealState hidden) :=
  (uniformOn (Set.univ : Set KeyPair)).prod (randomLaw.prod (OracleLaw.law (List (Fin 256))))

noncomputable def extendedLaw (hidden : Private) (randomLaw : Measure (Randomness hidden)) :
    Measure (ExtendedState hidden) :=
  (uniformOn (Set.univ : Set KeyPair)).prod (randomLaw.prod (OracleLaw.law (List (Fin 256) ⊕ Slot)))

noncomputable def programState (hidden : Private) (input : Input)
    (state : ExtendedState hidden) : RealState hidden :=
  (state.1,state.2.1,programmed state.1.1 state.1.2 input state.2.2)

theorem programState_preserving (hidden : Private) (input : Input)
    (randomLaw : Measure (Randomness hidden)) [SFinite randomLaw] :
    MeasurePreserving (programState hidden input)
      (extendedLaw hidden randomLaw) (realLaw hidden randomLaw) := by
  unfold programState extendedLaw realLaw
  refine (MeasurePreserving.id (uniformOn (Set.univ : Set KeyPair))).skew_product
    (μc := randomLaw.prod (OracleLaw.law (List (Fin 256) ⊕ Slot)))
    (μd := randomLaw.prod (OracleLaw.law (List (Fin 256))))
    (g := fun keys s => (s.1,programmed keys.1 keys.2 input s.2)) ?_ ?_
  · exact measurable_from_prod_countable_right fun keys =>
      ((MeasurePreserving.id randomLaw).prod (oracle_preserving keys.1 keys.2 input)).measurable
  · exact Filter.Eventually.of_forall fun keys =>
      ((MeasurePreserving.id randomLaw).prod (oracle_preserving keys.1 keys.2 input)).map_eq

def realOutcome (hidden : Private) (input : Input) (adversary : View challenge → Program α)
    (state : RealState hidden) : α :=
  ROM.run (ROM.hash state.2.2)
    (adversary (DutyFreeGameViews.real (ROM.hash state.2.2) hidden state.2.1 state.1.1 state.1.2 input))

def idealOutcome (hidden : Private) (input : Input) (adversary : View challenge → Program α)
    (state : ExtendedState hidden) : α :=
  ROM.run (ROM.hash (base state.2.2))
    (adversary (DutyFreeGameViews.ideal hidden state.2.1 input (active state.1.1 input) state.1.2 state.2.2))

theorem realOutcome_measurable [MeasurableSpace α] (hidden : Private) (input : Input)
    (adversary : View challenge → Program α) : Measurable (realOutcome hidden input adversary) :=
  measurable_from_prod_countable_right fun keys =>
    measurable_from_prod_countable_right fun random =>
      DutyFreeGameViews.real_run_measurable hidden random keys.1 keys.2 input adversary

theorem idealOutcome_measurable [MeasurableSpace α] (hidden : Private) (input : Input)
    (adversary : View challenge → Program α) : Measurable (idealOutcome hidden input adversary) :=
  measurable_from_prod_countable_right fun keys =>
    measurable_from_prod_countable_right fun random =>
      DutyFreeGameViews.ideal_run_measurable hidden random input (active keys.1 input) keys.2 adversary

def realDistinguish (hidden : Private) (input : Input) (adversary : View challenge → Program Bool) :
    Set (RealState hidden) := {state | realOutcome hidden input adversary state = true}
def idealDistinguish (hidden : Private) (input : Input) (adversary : View challenge → Program Bool) :
    Set (ExtendedState hidden) := {state | idealOutcome hidden input adversary state = true}

theorem realDistinguish_measurable (hidden : Private) (input : Input)
    (adversary : View challenge → Program Bool) : MeasurableSet (realDistinguish hidden input adversary) :=
  realOutcome_measurable hidden input adversary (measurableSet_singleton true)
theorem idealDistinguish_measurable (hidden : Private) (input : Input)
    (adversary : View challenge → Program Bool) : MeasurableSet (idealDistinguish hidden input adversary) :=
  idealOutcome_measurable hidden input adversary (measurableSet_singleton true)

def realWin (hidden : Private) (input : Input) (adversary : View challenge → Program (Fin 512 × Label)) :
    Set (RealState hidden) := {state |
      (realOutcome hidden input adversary state).2 =
        (state.1.1 (realOutcome hidden input adversary state).1).get
          (!(inputCodec.encode input)[(realOutcome hidden input adversary state).1.val])}

theorem realWin_measurable (hidden : Private) (input : Input)
    (adversary : View challenge → Program (Fin 512 × Label)) : MeasurableSet (realWin hidden input adversary) := by
  exact PredicateMeasurable.event
    (fun (keys : Keys) (claim : Fin 512 × Label) =>
      claim.2 = (keys claim.1).get (!(inputCodec.encode input)[claim.1.val]))
    (fun state : RealState hidden => state.1.1)
    (realOutcome hidden input adversary) (measurable_fst.comp measurable_fst)
    (realOutcome_measurable hidden input adversary)

end G1Release.Submission.DutyFreeGameLaw
