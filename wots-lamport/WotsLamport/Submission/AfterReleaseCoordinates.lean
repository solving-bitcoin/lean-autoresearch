import WotsLamport.Submission.CanonicalVisibleOracle
import WotsLamport.Submission.SelectedTraceCoupling

namespace WotsLamport.Submission
open SecretRelease WotsLamport.Protected OracleComp MeasureTheory ProbabilityTheory

abbrev AfterHiddenSetup (m : Message) := MessageHiddenTape m × (Fin 256 → Pair)
abbrev AfterEnvironment (m : Message) := PublicKey × MessageVisibleTape m × AllocatedCoefficients

noncomputable def afterTape (m : Message) (environment : AfterEnvironment m)
    (secret : AfterHiddenSetup m) : ChainTape :=
  (messageChainPartition m).symm (environment.1,secret.1,environment.2.1)

theorem afterTape_publicKey (m : Message) (environment : AfterEnvironment m) (secret : AfterHiddenSetup m) :
    tapePublicKey (afterTape m environment secret) = environment.1 :=
  congrArg Prod.fst ((messageChainPartition m).apply_symm_apply
    (environment.1,secret.1,environment.2.1))

theorem afterTape_visible (m : Message) (environment : AfterEnvironment m) (secret : AfterHiddenSetup m) :
    (messageChainPartition m (afterTape m environment secret)).2.2 = environment.2.1 :=
  congrArg (fun sample => sample.2.2) ((messageChainPartition m).apply_symm_apply
    (environment.1,secret.1,environment.2.1))

theorem afterTape_hidden (m : Message) (environment : AfterEnvironment m) (secret : AfterHiddenSetup m)
    (edge : {edge : ChainEdge // hiddenAfterMessage m edge}) :
    afterTape m environment secret edge.val.val = secret.1 edge :=
  congrArg (fun sample => sample.2.1 edge) ((messageChainPartition m).apply_symm_apply
    (environment.1,secret.1,environment.2.1))

noncomputable def afterCoefficientEquiv (m : Message) (labels : Fin 256 → Pair) :
    AllocatedCoefficients ≃ AllocatedCoefficients :=
  visibleCoefficientEquiv m labels
    (canonicalLabelTable (fun i => (outputCodec.encode m)[i.val])
      (fun i => (labels i).get (outputCodec.encode m)[i.val]))
    (fun i => (canonicalLabelTable_selected _ labels i).symm)

noncomputable def afterAnswers (m : Message) (environment : AfterEnvironment m)
    (secret : AfterHiddenSetup m)
    (coordinates : (SharePosition → Bytes 64) × (CommitmentCell → Label)) : ArtifactAnswers :=
  fieldArtifactAnswers secret.2 ((afterCoefficientEquiv m secret.2).symm environment.2.2) coordinates

noncomputable def afterHash (m : Message) (nonce : ByteArray) (environment : AfterEnvironment m)
    (secret : AfterHiddenSetup m)
    (coordinates : (SharePosition → Bytes 64) × (CommitmentCell → Label)) (baseline : Hash) : Hash :=
  programmedHash nonce (afterTape m environment secret) secret.2
    (afterAnswers m environment secret coordinates) baseline

noncomputable def afterBaseline (m : Message) (nonce : ByteArray) (environment : AfterEnvironment m)
    (coordinates : (SharePosition → Bytes 64) × (CommitmentCell → Label)) (baseline : Hash)
    (selected : Fin 256 → Label) : Hash :=
  canonicalVisibleOracle m nonce environment.1 environment.2.1 selected environment.2.2 coordinates baseline

theorem after_visible_hash (m : Message) (nonce : ByteArray) (environment : AfterEnvironment m)
    (secret : AfterHiddenSetup m)
    (coordinates : (SharePosition → Bytes 64) × (CommitmentCell → Label)) (baseline : Hash) :
    visibleProgrammedHash m nonce (afterTape m environment secret) secret.2
      (afterAnswers m environment secret coordinates) baseline =
      afterBaseline m nonce environment coordinates baseline
        (fun i => (secret.2 i).get (outputCodec.encode m)[i.val]) := by
  have he := visibleOracle_canonical_form m nonce (afterTape m environment secret) secret.2
    ((afterCoefficientEquiv m secret.2).symm environment.2.2) coordinates baseline
  change visibleProgrammedHash m nonce (afterTape m environment secret) secret.2
      (afterAnswers m environment secret coordinates) baseline =
    canonicalVisibleOracle m nonce (tapePublicKey (afterTape m environment secret))
      (messageChainPartition m (afterTape m environment secret)).2.2
      (fun i => (secret.2 i).get (outputCodec.encode m)[i.val])
      (afterCoefficientEquiv m secret.2 ((afterCoefficientEquiv m secret.2).symm environment.2.2))
      coordinates baseline at he
  rw [Equiv.apply_symm_apply, afterTape_publicKey, afterTape_visible] at he
  exact he

theorem after_hash_off_targets (m : Message) (nonce : ByteArray) (environment : AfterEnvironment m)
    (secret : AfterHiddenSetup m)
    (coordinates : (SharePosition → Bytes 64) × (CommitmentCell → Label)) (baseline : Hash)
    (distinct : Function.Injective (afterTape m environment secret)) (input : ByteArray)
    (nodesMissing : ∀ edge, chainMaskQueryTarget (keyCodec.encode environment.1) nonce input ≠ some (secret.1 edge))
    (labelsMissing : ∀ i, commitmentQueryTarget (keyCodec.encode environment.1) nonce input ≠
      some ((secret.2 i).get (!(outputCodec.encode m)[i.val]))) :
    afterBaseline m nonce environment coordinates baseline
        (fun i => (secret.2 i).get (outputCodec.encode m)[i.val]) input =
      afterHash m nonce environment secret coordinates baseline input := by
  rw [← after_visible_hash m nonce environment secret coordinates baseline]
  symm
  apply programmedHash_eq_visible_off_targets m nonce _ distinct
  · intro edge
    rw [afterTape_publicKey, afterTape_hidden]
    exact nodesMissing edge
  · intro i
    rw [afterTape_publicKey]
    exact labelsMissing i

/-- Only selected labels enter the baseline execution. All target-bearing
oracle changes and the exceptional collision set remain in the bound. -/
theorem after_trace_difference_bound {A : Type} (m : Message) (nonce : ByteArray)
    (environment : AfterEnvironment m)
    (coordinates : (SharePosition → Bytes 64) × (CommitmentCell → Label)) (baseline : Hash)
    (program : (Fin 256 → Label) → Program A) (q : Nat)
    (bound : ∀ selected, IsTotalQueryBound (program selected) q) :
    uniformOn (Set.univ : Set (AfterHiddenSetup m))
      {secret | let selected := fun i => (secret.2 i).get (outputCodec.encode m)[i.val]
        ROM.run (afterBaseline m nonce environment coordinates baseline selected) (program selected) ≠
          ROM.run (afterHash m nonce environment secret coordinates baseline) (program selected)} ≤
      (1501 : ENNReal)*q/2^256 +
        uniformOn (Set.univ : Set (AfterHiddenSetup m))
          {secret | ¬Function.Injective (afterTape m environment secret)} := by
  classical
  have h := selected_trace_difference_on_good_bound
    (fun i : Fin 256 => (outputCodec.encode m)[i.val])
    (chainMaskQueryTarget (keyCodec.encode environment.1) nonce)
    (commitmentQueryTarget (keyCodec.encode environment.1) nonce)
    (afterBaseline m nonce environment coordinates baseline)
    (fun secret => afterHash m nonce environment secret coordinates baseline)
    program q bound {secret | Function.Injective (afterTape m environment secret)}
    (fun secret distinct input => after_hash_off_targets m nonce environment secret
      coordinates baseline distinct input)
  have cardinal : (Fintype.card {edge : ChainEdge // hiddenAfterMessage m edge} : ENNReal) ≤ 989 := by
    exact_mod_cast (show Fintype.card {edge : ChainEdge // hiddenAfterMessage m edge} ≤ 989 from
      by simpa only [Nat.card_eq_fintype_card] using messageHidden_card_le m)
  refine h.trans (add_le_add ?_ le_rfl)
  calc
    _ ≤ (989 : ENNReal)*q/2^256 + (256 : ENNReal)*q*2/2^256 := by
      simp only [Fintype.card_fin, Nat.cast_ofNat]
      gcongr
    _ = (1501 : ENNReal)*q/2^256 := by ring

theorem after_release_fiber_bound (m : Message) (nonce : ByteArray)
    (environment : AfterEnvironment m)
    (coordinates : (SharePosition → Bytes 64) × (CommitmentCell → Label)) (baseline : Hash)
    (program : (Fin 256 → Label) → Program (Fin 256 × Label)) (q : Nat)
    (bound : ∀ selected, IsTotalQueryBound (program selected) q) :
    uniformOn (Set.univ : Set (AfterHiddenSetup m))
      {secret | let selected := fun i => (secret.2 i).get (outputCodec.encode m)[i.val]
        let claim := ROM.run (afterHash m nonce environment secret coordinates baseline) (program selected)
        claim.2 = (secret.2 claim.1).get (!(outputCodec.encode m)[claim.1.val])} ≤
      ((512 : ENNReal)/2^256 + (1501 : ENNReal)*q/2^256) +
        uniformOn (Set.univ : Set (AfterHiddenSetup m))
          {secret | ¬Function.Injective (afterTape m environment secret)} := by
  classical
  let guess selected := ROM.run (afterBaseline m nonce environment coordinates baseline selected)
    (program selected)
  let baselineWin : Set (AfterHiddenSetup m) :=
    {secret | let claim := guess (fun i => (secret.2 i).get (outputCodec.encode m)[i.val])
      claim.2 = (secret.2 claim.1).get (!(outputCodec.encode m)[claim.1.val])}
  let changed : Set (AfterHiddenSetup m) :=
    {secret | let selected := fun i => (secret.2 i).get (outputCodec.encode m)[i.val]
      guess selected ≠ ROM.run (afterHash m nonce environment secret coordinates baseline) (program selected)}
  have subset : {secret : AfterHiddenSetup m |
      let selected := fun i => (secret.2 i).get (outputCodec.encode m)[i.val]
      let claim := ROM.run (afterHash m nonce environment secret coordinates baseline) (program selected)
      claim.2 = (secret.2 claim.1).get (!(outputCodec.encode m)[claim.1.val])} ⊆
      baselineWin ∪ changed := by
    intro secret win
    by_cases same : guess (fun i => (secret.2 i).get (outputCodec.encode m)[i.val]) =
        ROM.run (afterHash m nonce environment secret coordinates baseline)
          (program (fun i => (secret.2 i).get (outputCodec.encode m)[i.val]))
    · exact Or.inl (by simpa only [baselineWin, Set.mem_setOf_eq, same] using win)
    · exact Or.inr same
  have guessing : uniformOn (Set.univ : Set (AfterHiddenSetup m)) baselineWin ≤ (512 : ENNReal)/2^256 := by
    have event_eq : baselineWin = (Set.univ : Set (MessageHiddenTape m)) ×ˢ
        {labels | let claim := guess (fun i => (labels i).get (outputCodec.encode m)[i.val])
          claim.2 = (labels claim.1).get (!(outputCodec.encode m)[claim.1.val])} := by
      ext secret
      simp only [baselineWin, Set.mem_setOf_eq, Set.mem_prod, Set.mem_univ, true_and]
    rw [event_eq]
    rw [uniform_product, Measure.prod_prod, measure_univ, one_mul]
    have h := uniform_selected_table_guess (fun i : Fin 256 => (outputCodec.encode m)[i.val]) guess
    norm_num only [Fintype.card_fin, Nat.cast_ofNat] at h
    exact h
  have querying := after_trace_difference_bound m nonce environment coordinates baseline program q bound
  have h := (measure_mono subset).trans ((measure_union_le _ _).trans (add_le_add guessing querying))
  simpa only [add_assoc] using h

def afterReleaseView (m : Message) (nonce : ByteArray) (environment : AfterEnvironment m)
    (coordinates : (SharePosition → Bytes 64) × (CommitmentCell → Label))
    (selected : Fin 256 → Label) : View challenge :=
  ⟨m, keyCodec.encode environment.1 ++ ciphertextBody nonce coordinates.2 coordinates.1,
    signatureBytes (signatureFromVisible m environment.1 environment.2.1),
    pack ((List.finRange 256).map selected)⟩

/-- Concrete finishing phase of the adversary, after message and state have
been selected independently of hidden credentials in the earlier hybrid. -/
theorem after_finish_fiber_bound (m : Message) (nonce : ByteArray) (environment : AfterEnvironment m)
    (coordinates : (SharePosition → Bytes 64) × (CommitmentCell → Label)) (baseline : Hash)
    (finish : View challenge → Program challenge.Claim) (q : Nat) (bound : ROM.Bounded finish q) :
    uniformOn (Set.univ : Set (AfterHiddenSetup m))
      {secret | let selected := fun i => (secret.2 i).get (outputCodec.encode m)[i.val]
        let claim := ROM.run (afterHash m nonce environment secret coordinates baseline)
          (finish (afterReleaseView m nonce environment coordinates selected))
        claim.2 = (secret.2 claim.1).get (!(outputCodec.encode m)[claim.1.val])} ≤
      ((512 : ENNReal)/2^256 + (1501 : ENNReal)*q/2^256) +
        uniformOn (Set.univ : Set (AfterHiddenSetup m))
          {secret | ¬Function.Injective (afterTape m environment secret)} :=
  after_release_fiber_bound m nonce environment coordinates baseline
    (fun selected => finish (afterReleaseView m nonce environment coordinates selected)) q
    (fun selected => bound (afterReleaseView m nonce environment coordinates selected))

end WotsLamport.Submission
