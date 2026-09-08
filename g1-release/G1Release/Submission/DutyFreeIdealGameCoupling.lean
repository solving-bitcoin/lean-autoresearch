import G1Release.Submission.DutyFreeGameLaw
import G1Release.Submission.DutyFreeAuxCoupling
import G1Release.Submission.CosetCoinLaw

/-! Couple equal-output ideal games by a bijection of their finite state.
The base oracle is fixed throughout. The only exceptional states are the
explicitly counted incomplete 512-bit residue blocks. -/
namespace G1Release.Submission.DutyFreeIdealGameCoupling

local instance : MeasurableSpace DutyFreeSlots.Keys := ⊤
open SecretRelease G1Release.Protected DutyFreeSlots DutyFreeRealIdeal DutyFreeGameLaw
open MeasureTheory ProbabilityTheory
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

abbrev FiniteState := DutyFreeAuxCoupling.FiniteState
abbrev SplitState (hidden : Private) := ROM.Oracle × FiniteState hidden

local instance (hidden : Private) : DiscreteMeasurableSpace (FiniteState hidden) :=
  MeasurableSingletonClass.toDiscreteMeasurableSpace
local instance (hidden : Private) : DiscreteMeasurableSpace (KeyPair × Randomness hidden) :=
  MeasurableSingletonClass.toDiscreteMeasurableSpace
local instance (hidden : Private) :
    DiscreteMeasurableSpace ((KeyPair × Randomness hidden) × DutyFreeOracleSplit.Aux) :=
  MeasurableSingletonClass.toDiscreteMeasurableSpace

noncomputable def shuffle (hidden : Private) : ExtendedState hidden ≃ᵐ SplitState hidden :=
  (MeasurableEquiv.prodAssoc : (KeyPair × Randomness hidden) × ExtendedOracle ≃ᵐ
    KeyPair × Randomness hidden × ExtendedOracle).symm.trans
    (DutyFreeOracleSplit.shuffle.trans
      (MeasurableEquiv.prodCongr (MeasurableEquiv.refl _)
        (MeasurableEquiv.prodAssoc : (KeyPair × Randomness hidden) × DutyFreeOracleSplit.Aux ≃ᵐ
          KeyPair × Randomness hidden × DutyFreeOracleSplit.Aux)))

noncomputable def splitLaw (hidden : Private) : Measure (SplitState hidden) :=
  (OracleLaw.law (List (Fin 256))).prod (uniformOn Set.univ)

theorem shuffle_preserving (hidden : Private) :
    MeasurePreserving (shuffle hidden) (extendedLaw hidden (CosetSampler.idealLaw hidden))
      (splitLaw hidden) := by
  have h1 := (measurePreserving_prodAssoc
    (uniformOn (Set.univ : Set KeyPair)) (uniformOn (Set.univ : Set (Randomness hidden)))
    (OracleLaw.law (List (Fin 256) ⊕ Slot))).symm
    (MeasurableEquiv.prodAssoc : (KeyPair × Randomness hidden) × ExtendedOracle ≃ᵐ
      KeyPair × Randomness hidden × ExtendedOracle)
  rw [LamportLaw.prod_uniform_univ] at h1
  have h2 := DutyFreeOracleSplit.shuffle_preserving (X := KeyPair × Randomness hidden)
  have h3 := (MeasurePreserving.id (OracleLaw.law (List (Fin 256)))).prod
    (FiniteProbability.uniform_equiv (Equiv.prodAssoc KeyPair (Randomness hidden) DutyFreeOracleSplit.Aux))
  exact h3.comp (h2.comp h1)

noncomputable def moveState (source target : Private) (input : Input)
    (hequal : GLVOffsetFamily.mapAt source input = GLVOffsetFamily.mapAt target input)
    (state : SplitState source) : SplitState target :=
  (state.1,DutyFreeAuxCoupling.move source target input hequal state.2)

theorem moveState_preserving (source target : Private) (input : Input)
    (hequal : GLVOffsetFamily.mapAt source input = GLVOffsetFamily.mapAt target input) :
    MeasurePreserving (moveState source target input hequal) (splitLaw source) (splitLaw target) :=
  (MeasurePreserving.id (OracleLaw.law (List (Fin 256)))).prod
    (FiniteProbability.uniform_equiv (DutyFreeAuxCoupling.move source target input hequal))

noncomputable def transport (source target : Private) (input : Input)
    (hequal : GLVOffsetFamily.mapAt source input = GLVOffsetFamily.mapAt target input)
    (state : ExtendedState source) : ExtendedState target :=
  (shuffle target).symm (moveState source target input hequal (shuffle source state))

theorem preserving (source target : Private) (input : Input)
    (hequal : GLVOffsetFamily.mapAt source input = GLVOffsetFamily.mapAt target input) :
    MeasurePreserving (transport source target input hequal)
      (extendedLaw source (CosetSampler.idealLaw source)) (extendedLaw target (CosetSampler.idealLaw target)) :=
  ((shuffle_preserving target).symm (shuffle target)).comp
    ((moveState_preserving source target input hequal).comp (shuffle_preserving source))

def bad (hidden : Private) : Set (ExtendedState hidden) :=
  shuffle hidden ⁻¹' (Set.univ ×ˢ DutyFreeAuxCoupling.bad hidden)

theorem bad_bound (hidden : Private) :
    extendedLaw hidden (CosetSampler.idealLaw hidden) (bad hidden) ≤ (1 : ENNReal) / 2^240 := by
  unfold bad
  rw [(shuffle_preserving hidden).measure_preimage
    (MeasurableSet.univ.prod MeasurableSet.of_discrete).nullMeasurableSet,
    splitLaw, Measure.prod_prod, measure_univ, one_mul]
  exact DutyFreeAuxCoupling.bad_bound hidden

theorem outcome_eq (source target : Private) (input : Input)
    (hequal : GLVOffsetFamily.mapAt source input = GLVOffsetFamily.mapAt target input)
    (href : reference source input = reference target input)
    (adversary : View challenge → Program α) (state : ExtendedState source)
    (hg : state ∉ bad source) :
    idealOutcome source input adversary state =
      idealOutcome target input adversary (transport source target input hequal state) := by
  let randomPads : DutyFreeViewCoupling.RandomPads source := (state.2.1.1,plainPads state.2.2)
  have hgood : DutyFreeViewCoupling.good randomPads.2 := by
    change ¬(True ∧ ¬DutyFreeViewCoupling.good randomPads.2) at hg
    exact Classical.not_not.mp (fun h => hg ⟨True.intro,h⟩)
  have ha := DutyFreeViewCoupling.artifact_preserved (ROM.hash (base state.2.2)) input
    source target hequal (active state.1.1 input) state.1.2 (bridgePads state.2.2) randomPads hgood
  apply congrArg (ROM.run (ROM.hash (base state.2.2)))
  apply congrArg adversary
  change DutyFreeGameViews.make source input (active state.1.1 input)
      (DutyFreeArtifact.encode (DutyFreeIdeal.garble (ROM.hash (base state.2.2)) input source
        randomPads.1 (active state.1.1 input) state.1.2 (bridgePads state.2.2) randomPads.2)) =
    DutyFreeGameViews.make target input (active state.1.1 input) _
  rw [← ha]
  unfold DutyFreeGameViews.make
  rw [href]
  rfl

theorem probability_le (source target : Private) (input : Input)
    (hequal : GLVOffsetFamily.mapAt source input = GLVOffsetFamily.mapAt target input)
    (href : reference source input = reference target input)
    (adversary : View challenge → Program Bool) :
    extendedLaw source (CosetSampler.idealLaw source) (idealDistinguish source input adversary) ≤
      extendedLaw target (CosetSampler.idealLaw target) (idealDistinguish target input adversary) + 1 / 2^240 := by
  have hp := preserving source target input hequal
  rw [← hp.measure_preimage (idealDistinguish_measurable target input adversary).nullMeasurableSet]
  apply (EventBounds.event_le_add_bad (extendedLaw source (CosetSampler.idealLaw source)) _ _
    (bad source) ?_).trans (add_le_add le_rfl (bad_bound source))
  intro state hs hb
  change idealOutcome source input adversary state = true at hs
  change idealOutcome target input adversary (transport source target input hequal state) = true
  rw [← outcome_eq source target input hequal href adversary state hb]
  exact hs

end G1Release.Submission.DutyFreeIdealGameCoupling
