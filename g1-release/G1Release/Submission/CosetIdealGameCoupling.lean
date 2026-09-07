import G1Release.Submission.CosetGameLaw
import G1Release.Submission.CosetViewCoupling
import G1Release.Submission.CosetOracleSplit

namespace G1Release.Submission.CosetIdealGameCoupling
set_option maxRecDepth 4096
set_option maxHeartbeats 800000
open SecretRelease G1Release.Protected CosetSampler CosetSlots CosetRealIdeal CosetGameLaw
open MeasureTheory ProbabilityTheory
local instance : MeasurableSpace Keys := ⊤
local instance : DiscreteMeasurableSpace Keys where
  forall_measurableSet := fun _ => MeasurableSpace.measurableSet_top
local instance : DiscreteMeasurableSpace CosetOracleSplit.Aux := by
  change DiscreteMeasurableSpace ((Fin 91 × Fin 8 × Fin 254) → Label)
  infer_instance

abbrev FiniteState (hidden : Hidden) := Keys × CosetViewCoupling.RandomPads hidden
abbrev SplitState (hidden : Hidden) := ROM.Oracle × FiniteState hidden

local instance (hidden : Hidden) :
    DiscreteMeasurableSpace ((Keys × Randomness hidden) × CosetOracleSplit.Aux) :=
  MeasurableSingletonClass.toDiscreteMeasurableSpace
local instance (hidden : Hidden) : DiscreteMeasurableSpace (FiniteState hidden) :=
  MeasurableSingletonClass.toDiscreteMeasurableSpace

noncomputable def shuffle (hidden : Hidden) : ExtendedState hidden ≃ᵐ SplitState hidden :=
  (MeasurableEquiv.prodAssoc : (Keys × Randomness hidden) × ExtendedOracle ≃ᵐ
    Keys × Randomness hidden × ExtendedOracle).symm.trans
    (CosetOracleSplit.shuffle.trans
      (MeasurableEquiv.prodCongr (MeasurableEquiv.refl _)
        (MeasurableEquiv.prodAssoc : (Keys × Randomness hidden) × CosetOracleSplit.Aux ≃ᵐ
          Keys × Randomness hidden × CosetOracleSplit.Aux)))

noncomputable def splitLaw (hidden : Hidden) : Measure (SplitState hidden) :=
  (OracleLaw.law (List (Fin 256))).prod (uniformOn Set.univ)

theorem shuffle_preserving (hidden : Hidden) :
    MeasurePreserving (shuffle hidden) (extendedLaw hidden (idealLaw hidden)) (splitLaw hidden) := by
  have h1 := (measurePreserving_prodAssoc
    (uniformOn (Set.univ : Set Keys)) (uniformOn (Set.univ : Set (Randomness hidden)))
    (OracleLaw.law (List (Fin 256) ⊕ Slot))).symm
    (MeasurableEquiv.prodAssoc : (Keys × Randomness hidden) × ExtendedOracle ≃ᵐ
      Keys × Randomness hidden × ExtendedOracle)
  rw [LamportLaw.prod_uniform_univ] at h1
  have h2 := CosetOracleSplit.shuffle_preserving (X := Keys × Randomness hidden)
  have h3 := (MeasurePreserving.id (OracleLaw.law (List (Fin 256)))).prod
    (FiniteProbability.uniform_equiv (Equiv.prodAssoc Keys (Randomness hidden) CosetOracleSplit.Aux))
  exact h3.comp (h2.comp h1)

noncomputable def move (base : ROM.Oracle) (source target : Hidden) (input : Input)
    (hequal : GLVOffsetFamily.mapAt source input = GLVOffsetFamily.mapAt target input) :
    FiniteState source ≃ FiniteState target :=
  Equiv.prodCongrRight fun keys => CosetViewCoupling.transport
    (CosetViewCoupling.answers (ROM.hash base) (selected keys input)) input source target hequal

theorem move_measurable (source target : Hidden) (input : Input)
    (hequal : GLVOffsetFamily.mapAt source input = GLVOffsetFamily.mapAt target input) :
    Measurable (fun s : SplitState source => move s.1 source target input hequal s.2) := by
  apply measurable_from_prod_countable_left
  intro state
  have hf : Measurable (fun observed : CosetViewCoupling.Answers =>
      (state.1,CosetViewCoupling.transport observed input source target hequal state.2)) :=
    Measurable.of_discrete
  have ho : Measurable (fun base : ROM.Oracle =>
      CosetViewCoupling.answers (ROM.hash base) (selected state.1 input)) := by
    apply measurable_pi_lambda
    intro slot
    exact ROMTrace.hash_measurable _
  exact hf.comp ho

noncomputable def moveState (source target : Hidden) (input : Input)
    (hequal : GLVOffsetFamily.mapAt source input = GLVOffsetFamily.mapAt target input)
    (state : SplitState source) : SplitState target :=
  (state.1,move state.1 source target input hequal state.2)

theorem moveState_preserving (source target : Hidden) (input : Input)
    (hequal : GLVOffsetFamily.mapAt source input = GLVOffsetFamily.mapAt target input) :
    MeasurePreserving (moveState source target input hequal) (splitLaw source) (splitLaw target) := by
  unfold moveState splitLaw
  refine (MeasurePreserving.id (OracleLaw.law (List (Fin 256)))).skew_product
    (μc := uniformOn (Set.univ : Set (FiniteState source)))
    (μd := uniformOn (Set.univ : Set (FiniteState target)))
    (g := fun base state => move base source target input hequal state) ?_ ?_
  · exact move_measurable source target input hequal
  · exact Filter.Eventually.of_forall fun base =>
      (FiniteProbability.uniform_equiv (move base source target input hequal)).map_eq

noncomputable def transport (source target : Hidden) (input : Input)
    (hequal : GLVOffsetFamily.mapAt source input = GLVOffsetFamily.mapAt target input)
    (state : ExtendedState source) : ExtendedState target :=
  (shuffle target).symm (moveState source target input hequal (shuffle source state))

theorem preserving (source target : Hidden) (input : Input)
    (hequal : GLVOffsetFamily.mapAt source input = GLVOffsetFamily.mapAt target input) :
    MeasurePreserving (transport source target input hequal)
      (extendedLaw source (idealLaw source)) (extendedLaw target (idealLaw target)) :=
  ((shuffle_preserving target).symm (shuffle target)).comp
    ((moveState_preserving source target input hequal).comp (shuffle_preserving source))

theorem outcome_eq (source target : Hidden) (input : Input)
    (hequal : GLVOffsetFamily.mapAt source input = GLVOffsetFamily.mapAt target input)
    (href : reference source input = reference target input)
    (adversary : View challenge → Program α) (state : ExtendedState source) :
    idealOutcome source input adversary state =
      idealOutcome target input adversary (transport source target input hequal state) := by
  let randomPads : CosetViewCoupling.RandomPads source := (state.2.1,fakePads state.2.2)
  have ha := CosetViewCoupling.artifact_preserved (ROM.hash (baseOracle state.2.2)) input
    (selected state.1 input) source target hequal randomPads
  apply congrArg (ROM.run (ROM.hash (baseOracle state.2.2)))
  apply congrArg adversary
  change CosetGameViews.make source input (selected state.1 input)
      (CosetIdealView.garble (ROM.hash (baseOracle state.2.2)) input source randomPads.1
        (selected state.1 input) randomPads.2) =
    CosetGameViews.make target input (selected state.1 input) _
  rw [← ha]
  unfold CosetGameViews.make
  rw [href]
  rfl

theorem probability_eq (source target : Hidden) (input : Input)
    (hequal : GLVOffsetFamily.mapAt source input = GLVOffsetFamily.mapAt target input)
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

end G1Release.Submission.CosetIdealGameCoupling
