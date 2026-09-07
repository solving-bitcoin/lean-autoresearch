import G1Release.Submission.CosetCorePrivacy
import G1Release.Submission.CosetIdealView

/-! Finite conditional coupling of the entire ideal artifact. Fix all selected
labels and the base oracle. Offset/quotient transport and independent row
transports form a bijection of core randomness, row coins, and inactive
oracle answers. The resulting artifact is unchanged pointwise. -/
namespace G1Release.Submission.CosetViewCoupling
open SecretRelease G1Release.Protected GarblingPrize.Protected
open CosetSlots CosetIdealView
abbrev Core := CosetRandomness.Randomness
abbrev Answers := Slot → Label

def answers (hash : Hash) (active : Fin 512 → Label) : Answers :=
  fun slot => AffineTable.pad hash (active (wire slot)) (purpose slot) slot.2.2.val

abbrev Rows := Slot → CosetRowCoupling.InactiveState
abbrev RandomPads (hidden : Private) := CosetSampler.Randomness hidden × InactivePads

def regroup (hidden : Private) : RandomPads hidden ≃ Core hidden × Rows where
  toFun s := (s.1.1,fun slot => (s.1.2 slot.1 slot.2.1 slot.2.2,s.2 slot))
  invFun s := ((s.1,fun i k j => (s.2 (i,k,j)).1),fun slot => (s.2 slot).2)
  left_inv s := rfl
  right_inv s := by
    apply Prod.ext rfl
    funext slot
    rfl

noncomputable def rowChange (observed : Answers) (input : Input)
    (source target : Private)
    (hequal : GLVOffsetFamily.mapAt source input = GLVOffsetFamily.mapAt target input)
    (core : Core source) (slot : Slot) : Equiv.Perm CosetRowCoupling.InactiveState :=
  CosetRowCoupling.transport
    (CosetScheme.mapParams source core slot.1 slot.2.1)
    (CosetScheme.mapParams target (CosetCorePrivacy.targetRandomness input source target hequal core)
      slot.1 slot.2.1)
    slot.2.2 (bit input slot)
    (observed slot)

noncomputable def jointEquiv (observed : Answers) (input : Input)
    (source target : Private)
    (hequal : GLVOffsetFamily.mapAt source input = GLVOffsetFamily.mapAt target input) :
    (Core source × Rows) ≃ (Core target × Rows) :=
  (Equiv.prodCongrRight fun core => Equiv.piCongrRight fun slot =>
    rowChange observed input source target hequal core slot).trans
    (Equiv.prodCongr (CosetCorePrivacy.randomnessEquiv input source target hequal) (Equiv.refl _))

noncomputable def transport (observed : Answers) (input : Input)
    (source target : Private)
    (hequal : GLVOffsetFamily.mapAt source input = GLVOffsetFamily.mapAt target input) :
    RandomPads source ≃ RandomPads target :=
  (regroup source).trans ((jointEquiv observed input source target hequal).trans (regroup target).symm)

theorem transport_core (hash : Hash) (input : Input) (active : Fin 512 → Label)
    (source target : Private)
    (hequal : GLVOffsetFamily.mapAt source input = GLVOffsetFamily.mapAt target input)
    (state : RandomPads source) :
    (transport (answers hash active) input source target hequal state).1.1 =
      CosetCorePrivacy.targetRandomness input source target hequal state.1.1 := rfl

theorem rowState_transport (hash : Hash) (input : Input) (active : Fin 512 → Label)
    (source target : Private)
    (hequal : GLVOffsetFamily.mapAt source input = GLVOffsetFamily.mapAt target input)
    (state : RandomPads source) (slot : Slot) :
    rowState hash input (transport (answers hash active) input source target hequal state).1 active
        (transport (answers hash active) input source target hequal state).2 slot =
      HintAffineTablePrivacy.rowTransport
        (CosetScheme.mapParams source state.1.1 slot.1 slot.2.1)
        (CosetScheme.mapParams target (CosetCorePrivacy.targetRandomness input source target hequal state.1.1)
          slot.1 slot.2.1) slot.2.2 (bit input slot)
        (rowState hash input state.1 active state.2 slot) := by
  exact CosetRowCoupling.assemble_transport _ _ _ _ _ _

theorem artifact_preserved (hash : Hash) (input : Input) (active : Fin 512 → Label)
    (source target : Private)
    (hequal : GLVOffsetFamily.mapAt source input = GLVOffsetFamily.mapAt target input)
    (state : RandomPads source) :
    CosetIdealView.garble hash input target
        (transport (answers hash active) input source target hequal state).1 active
        (transport (answers hash active) input source target hequal state).2 =
      CosetIdealView.garble hash input source state.1 active state.2 := by
  apply congrArg CosetScheme.encode
  apply CosetFamilyArtifact.Artifact.ext
  funext index
  apply CosetHintMap.Artifact.ext
  funext kind
  change HintAffineTablePrivacy.tableFromState _ _ = _
  have hr : (fun row => rowState hash input
      (transport (answers hash active) input source target hequal state).1 active
      (transport (answers hash active) input source target hequal state).2 (index,kind,row)) =
    HintAffineTablePrivacy.tableTransport
      (CosetScheme.mapParams source state.1.1 index kind)
      (CosetScheme.mapParams target (CosetCorePrivacy.targetRandomness input source target hequal state.1.1)
        index kind) (bitsFor kind input)
      (fun row => rowState hash input state.1 active state.2 (index,kind,row)) := by
    funext row
    exact rowState_transport hash input active source target hequal state (index,kind,row)
  rw [hr, transport_core]
  apply HintAffineTablePrivacy.tableFromState_transport
  exact CosetCorePrivacy.params_preserved input source target hequal state.1.1 index kind

theorem transport_preserving (observed : Answers) (input : Input)
    (source target : Private)
    (hequal : GLVOffsetFamily.mapAt source input = GLVOffsetFamily.mapAt target input) :
    MeasureTheory.MeasurePreserving (transport observed input source target hequal)
      (ProbabilityTheory.uniformOn Set.univ) (ProbabilityTheory.uniformOn Set.univ) :=
  FiniteProbability.uniform_equiv _

end G1Release.Submission.CosetViewCoupling
