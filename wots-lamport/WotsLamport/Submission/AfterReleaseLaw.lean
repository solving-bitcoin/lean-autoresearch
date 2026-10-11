import WotsLamport.Submission.AfterReleaseCoordinates

namespace WotsLamport.Submission
open SecretRelease WotsLamport.Protected MeasureTheory ProbabilityTheory OracleComp

abbrev AfterInnerSample := HiddenChainTape × (Fin 256 → Pair) × AllocatedCoefficients
abbrev AfterInnerEnvironment (m : Message) := MessageVisibleTape m × AllocatedCoefficients

/-- Fixing public endpoints fixes the chosen message before this bijection is
applied. Thus its message-dependent hidden/visible dimensions cause no union
bound over messages and no change to the outer public-key law. -/
noncomputable def afterInnerCoordinates (m : Message) :
    AfterInnerSample ≃ AfterInnerEnvironment m × AfterHiddenSetup m where
  toFun sample :=
    (((tablePartitionEquiv (hiddenAfterMessage m) sample.1).2,
      afterCoefficientEquiv m sample.2.1 sample.2.2),
      (tablePartitionEquiv (hiddenAfterMessage m) sample.1).1,sample.2.1)
  invFun sample :=
    ((tablePartitionEquiv (hiddenAfterMessage m)).symm (sample.2.1,sample.1.1),
      sample.2.2,(afterCoefficientEquiv m sample.2.2).symm sample.1.2)
  left_inv sample := by
    change ((tablePartitionEquiv (hiddenAfterMessage m)).symm
      (tablePartitionEquiv (hiddenAfterMessage m) sample.1),sample.2.1,
      (afterCoefficientEquiv m sample.2.1).symm (afterCoefficientEquiv m sample.2.1 sample.2.2)) = _
    rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  right_inv sample := by
    change (((tablePartitionEquiv (hiddenAfterMessage m)
        ((tablePartitionEquiv (hiddenAfterMessage m)).symm (sample.2.1,sample.1.1))).2,
      afterCoefficientEquiv m sample.2.2 ((afterCoefficientEquiv m sample.2.2).symm sample.1.2)),
      (tablePartitionEquiv (hiddenAfterMessage m)
        ((tablePartitionEquiv (hiddenAfterMessage m)).symm (sample.2.1,sample.1.1))).1,sample.2.2) = _
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]

theorem afterInnerCoordinates_tape (m : Message) (pk : PublicKey) (sample : AfterInnerSample) :
    afterTape m (pk,(afterInnerCoordinates m sample).1) (afterInnerCoordinates m sample).2 =
      chainPartitionEquiv.symm (pk,sample.1) := by
  change chainPartitionEquiv.symm (pk,
    (tablePartitionEquiv (hiddenAfterMessage m)).symm
      (tablePartitionEquiv (hiddenAfterMessage m) sample.1)) = _
  rw [Equiv.symm_apply_apply]

theorem afterInnerCoordinates_answers (m : Message) (sample : AfterInnerSample) (pk : PublicKey)
    (coordinates : (SharePosition → Bytes 64) × (CommitmentCell → Label)) :
    afterAnswers m (pk,(afterInnerCoordinates m sample).1) (afterInnerCoordinates m sample).2 coordinates =
      fieldArtifactAnswers sample.2.1 sample.2.2 coordinates := by
  change fieldArtifactAnswers sample.2.1
    ((afterCoefficientEquiv m sample.2.1).symm (afterCoefficientEquiv m sample.2.1 sample.2.2)) coordinates = _
  rw [Equiv.symm_apply_apply]

def conditionalTapeBad (pk : PublicKey) : Set HiddenChainTape :=
  {hidden | ¬Function.Injective (chainPartitionEquiv.symm (pk,hidden))}

theorem afterInner_bad_law (m : Message) (pk : PublicKey) :
    uniformOn (Set.univ : Set (AfterInnerEnvironment m × AfterHiddenSetup m))
      {sample | ¬Function.Injective (afterTape m (pk,sample.1) sample.2)} =
      uniformOn (Set.univ : Set HiddenChainTape) (conditionalTapeBad pk) := by
  classical
  rw [← Shamir.uniform_event_equiv (afterInnerCoordinates m)]
  change uniformOn (Set.univ : Set AfterInnerSample)
    {sample | ¬Function.Injective (afterTape m (pk,(afterInnerCoordinates m sample).1)
      (afterInnerCoordinates m sample).2)} = _
  simp only [afterInnerCoordinates_tape]
  have event_eq : {sample : AfterInnerSample |
      ¬Function.Injective (chainPartitionEquiv.symm (pk,sample.1))} =
      conditionalTapeBad pk ×ˢ (Set.univ : Set ((Fin 256 → Pair) × AllocatedCoefficients)) := by
    ext sample
    simp only [conditionalTapeBad, Set.mem_setOf_eq, Set.mem_prod, Set.mem_univ, and_true]
  rw [event_eq]
  rw [uniform_product, Measure.prod_prod, measure_univ, mul_one]

/-- Conditional public-endpoint bound for the complete finishing phase. The
state and message may depend on the fixed outer environment; the comparison
retains every coefficient, ciphertext and oracle coordinate jointly. -/
theorem after_finish_joint_bound (m : Message) (nonce : ByteArray) (pk : PublicKey)
    (coordinates : (SharePosition → Bytes 64) × (CommitmentCell → Label)) (baseline : Hash)
    (finish : View challenge → Program challenge.Claim) (q : Nat) (bound : ROM.Bounded finish q) :
    uniformOn (Set.univ : Set (AfterInnerEnvironment m × AfterHiddenSetup m))
      {sample | let selected := fun i => (sample.2.2 i).get (outputCodec.encode m)[i.val]
        let claim := ROM.run (afterHash m nonce (pk,sample.1) sample.2 coordinates baseline)
          (finish (afterReleaseView m nonce (pk,sample.1) coordinates selected))
        claim.2 = (sample.2.2 claim.1).get (!(outputCodec.encode m)[claim.1.val])} ≤
      uniformOn (Set.univ : Set HiddenChainTape) (conditionalTapeBad pk) +
        ((512 : ENNReal)/2^256 + (1501 : ENNReal)*q/2^256) := by
  classical
  have h := product_event_bound
    (uniformOn (Set.univ : Set (AfterInnerEnvironment m)))
    (uniformOn (Set.univ : Set (AfterHiddenSetup m)))
    (uniformOn (Set.univ : Set (AfterHiddenSetup m)))
    {sample | let selected := fun i => (sample.2.2 i).get (outputCodec.encode m)[i.val]
      let claim := ROM.run (afterHash m nonce (pk,sample.1) sample.2 coordinates baseline)
        (finish (afterReleaseView m nonce (pk,sample.1) coordinates selected))
      claim.2 = (sample.2.2 claim.1).get (!(outputCodec.encode m)[claim.1.val])}
    {sample | ¬Function.Injective (afterTape m (pk,sample.1) sample.2)}
    ((512 : ENNReal)/2^256 + (1501 : ENNReal)*q/2^256) (by
      intro environment
      simpa only [add_comm] using after_finish_fiber_bound m nonce (pk,environment)
        coordinates baseline finish q bound)
  rw [← uniform_product, afterInner_bad_law] at h
  exact h

end WotsLamport.Submission
