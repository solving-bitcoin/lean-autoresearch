import G1Release.Submission.DutyFreeOracleSplit
import G1Release.Submission.DutyFreePadLaw
import G1Release.Submission.DutyFreeConditionalKeys
import G1Release.Submission.CosetSampler

/-! Regroup the finite auxiliary oracle answers into bridge ciphertexts
and pairs of selected plain pads. Only the latter and the arithmetic core
move in the equal-output coupling; all labels and unused coins stay fixed. -/
namespace G1Release.Submission.DutyFreeAuxCoupling

local instance : MeasurableSpace DutyFreeSlots.Keys := ⊤
open SecretRelease G1Release.Protected DutyFreeSlots DutyFreeIdeal DutyFreeOracleSplit
open MeasureTheory ProbabilityTheory
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

def padsEquiv : Aux ≃ BridgePads × PlainPads where
  toFun aux := (fun slot => aux (.inl slot),
    fun table chunk => (aux (.inr (table,chunk,0)),aux (.inr (table,chunk,1))))
  invFun pads := Sum.elim pads.1 (fun slot =>
    if slot.2.2 = 0 then (pads.2 slot.1 slot.2.1).1 else (pads.2 slot.1 slot.2.1).2)
  left_inv aux := by
    funext slot
    rcases slot with slot | ⟨table,chunk,half⟩
    · rfl
    · fin_cases half <;> rfl
  right_inv pads := by
    apply Prod.ext
    · rfl
    · funext table chunk
      rfl

abbrev FiniteState (hidden : Private) :=
  DutyFreeConditionalKeys.KeyPair × CosetSampler.Randomness hidden × Aux
abbrev Context := (DutyFreeConditionalKeys.KeyPair × CosetScheme.Coins) × BridgePads

local instance : Finite Context := by infer_instance
local instance : Nonempty Context := by infer_instance
local instance (hidden : Private) : Finite (DutyFreeViewCoupling.RandomPads hidden) := by infer_instance
local instance (hidden : Private) : MeasurableSingletonClass (DutyFreeViewCoupling.RandomPads hidden) :=
  inferInstance
local instance (hidden : Private) : DiscreteMeasurableSpace (FiniteState hidden) :=
  MeasurableSingletonClass.toDiscreteMeasurableSpace
local instance : DiscreteMeasurableSpace Context :=
  MeasurableSingletonClass.toDiscreteMeasurableSpace
local instance (hidden : Private) :
    DiscreteMeasurableSpace (Context × DutyFreeViewCoupling.RandomPads hidden) :=
  MeasurableSingletonClass.toDiscreteMeasurableSpace

def regroup (hidden : Private) :
    FiniteState hidden ≃ Context × DutyFreeViewCoupling.RandomPads hidden where
  toFun s := (((s.1,s.2.1.2),(padsEquiv s.2.2).1),(s.2.1.1,(padsEquiv s.2.2).2))
  invFun s := (s.1.1.1,(s.2.1,s.1.1.2),padsEquiv.symm (s.1.2,s.2.2))
  left_inv s := by
    change (s.1,s.2.1,padsEquiv.symm (padsEquiv s.2.2)) = s
    rw [Equiv.symm_apply_apply]
  right_inv s := by simp only [Equiv.apply_symm_apply]

noncomputable def move (source target : Private) (input : Input)
    (hequal : GLVOffsetFamily.mapAt source input = GLVOffsetFamily.mapAt target input) :
    FiniteState source ≃ FiniteState target :=
  (regroup source).trans
    ((Equiv.prodCongr (Equiv.refl Context) (DutyFreeViewCoupling.transport input source target hequal)).trans
      (regroup target).symm)

def bad (hidden : Private) : Set (FiniteState hidden) :=
  {state | (padsEquiv state.2.2).2 ∈ DutyFreePadLaw.bad}

theorem bad_bound (hidden : Private) : uniformOn (Set.univ : Set (FiniteState hidden)) (bad hidden) ≤
    (1 : ENNReal) / 2^240 := by
  have hr := FiniteProbability.uniform_equiv (regroup hidden)
  have h1 : MeasurePreserving (Prod.snd : Context × DutyFreeViewCoupling.RandomPads hidden → _)
      (uniformOn Set.univ) (uniformOn Set.univ) := by
    rw [← LamportLaw.prod_uniform_univ (α := Context) (β := DutyFreeViewCoupling.RandomPads hidden)]
    exact measurePreserving_snd (μ := uniformOn (Set.univ : Set Context))
      (ν := uniformOn (Set.univ : Set (DutyFreeViewCoupling.RandomPads hidden)))
  have h2 : MeasurePreserving (Prod.snd : DutyFreeViewCoupling.RandomPads hidden → PlainPads)
      (uniformOn Set.univ) (uniformOn Set.univ) := by
    rw [← LamportLaw.prod_uniform_univ (α := DutyFreeProgram.Randomness hidden) (β := PlainPads)]
    exact measurePreserving_snd (μ := uniformOn (Set.univ : Set (DutyFreeProgram.Randomness hidden)))
      (ν := uniformOn (Set.univ : Set PlainPads))
  have hm := h2.comp (h1.comp hr)
  exact (hm.measure_preimage
    (MeasurableSet.of_discrete : MeasurableSet DutyFreePadLaw.bad).nullMeasurableSet).trans_le
    (DutyFreePadLaw.bad_bound.trans DutyFreePadLaw.bad_small)

end G1Release.Submission.DutyFreeAuxCoupling
