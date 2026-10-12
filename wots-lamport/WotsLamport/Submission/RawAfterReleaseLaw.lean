import WotsLamport.Submission.AfterReleaseLaw

namespace WotsLamport.Submission
open SecretRelease WotsLamport.Protected MeasureTheory ProbabilityTheory

theorem messagePartition_rebuild (m : Message) (pk : PublicKey) (hidden : HiddenChainTape) :
    messageChainPartition m (chainPartitionEquiv.symm (pk,hidden)) =
      (pk,tablePartitionEquiv (hiddenAfterMessage m) hidden) := by
  change (Equiv.prodCongr (Equiv.refl PublicKey) (tablePartitionEquiv (hiddenAfterMessage m)))
    (chainPartitionEquiv (chainPartitionEquiv.symm (pk,hidden))) = _
  rw [Equiv.apply_symm_apply]
  rfl

theorem afterInnerCoordinates_signature (m : Message) (pk : PublicKey) (sample : AfterInnerSample) :
    signatureFromVisible m pk (afterInnerCoordinates m sample).1.1 =
      tapeSignature (chainPartitionEquiv.symm (pk,sample.1)) m := by
  have h := signature_from_visible m (chainPartitionEquiv.symm (pk,sample.1))
  rw [messagePartition_rebuild] at h
  exact h

noncomputable def rawAfterHash (nonce : ByteArray) (pk : PublicKey) (sample : AfterInnerSample)
    (coordinates : (SharePosition → Bytes 64) × (CommitmentCell → Label)) (baseline : Hash) : Hash :=
  programmedHash nonce (chainPartitionEquiv.symm (pk,sample.1)) sample.2.1
    (fieldArtifactAnswers sample.2.1 sample.2.2 coordinates) baseline

def rawAfterView (m : Message) (nonce : ByteArray) (pk : PublicKey) (sample : AfterInnerSample)
    (coordinates : (SharePosition → Bytes 64) × (CommitmentCell → Label)) : View challenge :=
  ⟨m,keyCodec.encode pk ++ ciphertextBody nonce coordinates.2 coordinates.1,
    signatureBytes (tapeSignature (chainPartitionEquiv.symm (pk,sample.1)) m),
    pack ((List.finRange 256).map fun i => (sample.2.1 i).get (outputCodec.encode m)[i.val])⟩

def rawAfterEvent (m : Message) (nonce : ByteArray) (pk : PublicKey)
    (coordinates : (SharePosition → Bytes 64) × (CommitmentCell → Label)) (baseline : Hash)
    (finish : View challenge → Program challenge.Claim) : Set AfterInnerSample :=
  {sample |
    let claim := ROM.run (rawAfterHash nonce pk sample coordinates baseline)
      (finish (rawAfterView m nonce pk sample coordinates))
    claim.2 = (sample.2.1 claim.1).get (!(outputCodec.encode m)[claim.1.val])}

theorem afterInnerCoordinates_hash (m : Message) (nonce : ByteArray) (pk : PublicKey)
    (sample : AfterInnerSample) (coordinates : (SharePosition → Bytes 64) × (CommitmentCell → Label))
    (baseline : Hash) :
    afterHash m nonce (pk,(afterInnerCoordinates m sample).1) (afterInnerCoordinates m sample).2
      coordinates baseline = rawAfterHash nonce pk sample coordinates baseline := by
  unfold afterHash
  rw [afterInnerCoordinates_tape, afterInnerCoordinates_answers]
  rfl

theorem afterInnerCoordinates_view (m : Message) (nonce : ByteArray) (pk : PublicKey)
    (sample : AfterInnerSample) (coordinates : (SharePosition → Bytes 64) × (CommitmentCell → Label)) :
    afterReleaseView m nonce (pk,(afterInnerCoordinates m sample).1) coordinates
      (fun i => (sample.2.1 i).get (outputCodec.encode m)[i.val]) =
      rawAfterView m nonce pk sample coordinates := by
  unfold afterReleaseView rawAfterView
  rw [afterInnerCoordinates_signature]

theorem rawAfterEvent_bound (m : Message) (nonce : ByteArray) (pk : PublicKey)
    (coordinates : (SharePosition → Bytes 64) × (CommitmentCell → Label)) (baseline : Hash)
    (finish : View challenge → Program challenge.Claim) (q : Nat) (bound : ROM.Bounded finish q) :
    uniformOn (Set.univ : Set AfterInnerSample) (rawAfterEvent m nonce pk coordinates baseline finish) ≤
      uniformOn (Set.univ : Set HiddenChainTape) (conditionalTapeBad pk) +
        ((512 : ENNReal)/2^256 + (1501 : ENNReal)*q/2^256) := by
  classical
  let event : Set (AfterInnerEnvironment m × AfterHiddenSetup m) :=
    {sample | let selected := fun i => (sample.2.2 i).get (outputCodec.encode m)[i.val]
      let claim := ROM.run (afterHash m nonce (pk,sample.1) sample.2 coordinates baseline)
        (finish (afterReleaseView m nonce (pk,sample.1) coordinates selected))
      claim.2 = (sample.2.2 claim.1).get (!(outputCodec.encode m)[claim.1.val])}
  have reindex : rawAfterEvent m nonce pk coordinates baseline finish =
      (afterInnerCoordinates m) ⁻¹' event := by
    ext sample
    change _ ↔
      (let claim := ROM.run
          (afterHash m nonce (pk,(afterInnerCoordinates m sample).1) (afterInnerCoordinates m sample).2
            coordinates baseline)
          (finish (afterReleaseView m nonce (pk,(afterInnerCoordinates m sample).1) coordinates
            (fun i => (sample.2.1 i).get (outputCodec.encode m)[i.val])))
       claim.2 = (sample.2.1 claim.1).get (!(outputCodec.encode m)[claim.1.val]))
    rw [afterInnerCoordinates_hash, afterInnerCoordinates_view]
    rfl
  rw [reindex, Shamir.uniform_event_equiv]
  exact after_finish_joint_bound m nonce pk coordinates baseline finish q bound

/-- Endpoint averaging preserves the full tape law. It does not use the
chosen message, so message-dependent tape partitions do not add a loss. -/
theorem conditionalTapeBad_average :
    ((uniformOn (Set.univ : Set PublicKey)).prod (uniformOn (Set.univ : Set HiddenChainTape)))
      {sample | sample.2 ∈ conditionalTapeBad sample.1} ≤ (1056 : ENNReal)^2/2^256 := by
  classical
  rw [← uniform_product]
  have h := Shamir.uniform_event_equiv chainPartitionEquiv
    {sample : PublicKey × HiddenChainTape | sample.2 ∈ conditionalTapeBad sample.1}
  have event : chainPartitionEquiv ⁻¹'
      {sample : PublicKey × HiddenChainTape | sample.2 ∈ conditionalTapeBad sample.1} =
      {tape | ¬Function.Injective tape} := by
    ext tape
    change ¬Function.Injective (chainPartitionEquiv.symm (chainPartitionEquiv tape)) ↔ _
    rw [Equiv.symm_apply_apply]
    rfl
  rw [event] at h
  rw [← h]
  exact uniform_chainTape_collision_bound

/-- The selected message and finishing program may be arbitrary functions of
public endpoints and other fixed outer data. No adversary-state finiteness is
required, since only the finite endpoint/credential randomness is integrated. -/
theorem rawAfterEvent_public_bound (nonce : ByteArray)
    (coordinates : (SharePosition → Bytes 64) × (CommitmentCell → Label)) (baseline : Hash)
    (message : PublicKey → Message) (finish : PublicKey → View challenge → Program challenge.Claim)
    (q : Nat) (bound : ∀ pk, ROM.Bounded (finish pk) q) :
    uniformOn (Set.univ : Set (PublicKey × AfterInnerSample))
      {sample | sample.2 ∈ rawAfterEvent (message sample.1) nonce sample.1 coordinates baseline (finish sample.1)} ≤
        (1056 : ENNReal)^2/2^256 + ((512 : ENNReal)/2^256 + (1501 : ENNReal)*q/2^256) := by
  classical
  have h := product_event_bound (uniformOn (Set.univ : Set PublicKey))
    (uniformOn (Set.univ : Set AfterInnerSample)) (uniformOn (Set.univ : Set HiddenChainTape))
    {sample | sample.2 ∈ rawAfterEvent (message sample.1) nonce sample.1 coordinates baseline (finish sample.1)}
    {sample | sample.2 ∈ conditionalTapeBad sample.1}
    ((512 : ENNReal)/2^256 + (1501 : ENNReal)*q/2^256)
    (fun pk => rawAfterEvent_bound (message pk) nonce pk coordinates baseline (finish pk) q (bound pk))
  rw [← uniform_product] at h
  exact h.trans (add_le_add conditionalTapeBad_average le_rfl)

end WotsLamport.Submission
