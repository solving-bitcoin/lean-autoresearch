import WotsLamport.Submission.FiniteProgrammingBridge
import WotsLamport.Submission.ProgrammedQueryTrace
import WotsLamport.Submission.SelectedLabelTrace

namespace WotsLamport.Submission
open SecretRelease WotsLamport.Protected MeasureTheory ProbabilityTheory OracleComp

abbrev CiphertextCoordinates := (SharePosition → Bytes 64) × (CommitmentCell → Label)
abbrev BeforeEnvironment (inputs : Finset OracleInput) :=
  Bytes randomnessBytes × PublicKey × CiphertextCoordinates × (inputs → Label)
abbrev RawProgrammedSample (inputs : Finset OracleInput) :=
  (Bytes randomnessBytes × (Fin 256 → Pair)) × CombinedIdeal inputs

/-- A bijection of all randomness, separating the public ciphertext
coordinates from hidden chain nodes and both labels. Coins and public
endpoints remain in the independent environment. -/
noncomputable def beforeReleaseCoordinates (inputs : Finset OracleInput) :
    RawProgrammedSample inputs ≃ BeforeEnvironment inputs × HiddenSetup where
  toFun sample :=
    ((sample.1.1, (chainPartitionEquiv sample.2.1).1,
      artifactCiphertextCoordinates (ByteArray.mk sample.1.1.toArray) sample.1.2 sample.2.2.1,
      sample.2.2.2), (chainPartitionEquiv sample.2.1).2, sample.1.2)
  invFun sample :=
    ((sample.1.1, sample.2.2),
      chainPartitionEquiv.symm (sample.1.2.1,sample.2.1),
      (artifactCiphertextCoordinates (ByteArray.mk sample.1.1.toArray) sample.2.2).symm
        sample.1.2.2.1, sample.1.2.2.2)
  left_inv sample := by
    rcases sample with ⟨⟨coins,labels⟩,tape,answers,baseline⟩
    change ((coins,labels), chainPartitionEquiv.symm (chainPartitionEquiv tape),
      (artifactCiphertextCoordinates (ByteArray.mk coins.toArray) labels).symm
        (artifactCiphertextCoordinates (ByteArray.mk coins.toArray) labels answers), baseline) = _
    rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  right_inv sample := by
    rcases sample with ⟨⟨coins,pk,coordinates,baseline⟩,hidden,labels⟩
    change ((coins,(chainPartitionEquiv (chainPartitionEquiv.symm (pk,hidden))).1,
      artifactCiphertextCoordinates (ByteArray.mk coins.toArray) labels
        ((artifactCiphertextCoordinates (ByteArray.mk coins.toArray) labels).symm coordinates),
      baseline), (chainPartitionEquiv (chainPartitionEquiv.symm (pk,hidden))).2,labels) = _
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]

def beforeArtifact {inputs : Finset OracleInput} (environment : BeforeEnvironment inputs) : ByteArray :=
  keyCodec.encode environment.2.1 ++ ciphertextBody
    ((ByteArray.mk environment.1.toArray).extract 0 32)
    environment.2.2.1.2 environment.2.2.1.1

noncomputable def beforeAnswers {inputs : Finset OracleInput} (environment : BeforeEnvironment inputs)
    (secret : HiddenSetup) : ArtifactAnswers :=
  (artifactCiphertextCoordinates (ByteArray.mk environment.1.toArray) secret.2).symm
    environment.2.2.1

noncomputable def beforeHash {inputs : Finset OracleInput} (environment : BeforeEnvironment inputs)
    (secret : HiddenSetup) : Hash :=
  programmedHash ((ByteArray.mk environment.1.toArray).extract 0 32)
    (chainPartitionEquiv.symm (environment.2.1,secret.1)) secret.2
    (beforeAnswers environment secret) (ROM.hash (extendOracleTable inputs environment.2.2.2))

/-- The attacker may depend arbitrarily on the public environment, but this
pre-release program receives no chain nodes or selected output labels. -/
theorem before_release_fiber_bound (inputs : Finset OracleInput)
    (environment : BeforeEnvironment inputs) (m : Message)
    (a : PreReleaseView challenge → Program challenge.Claim) (q : Nat) (bound : ROM.Bounded a q) :
    uniformOn (Set.univ : Set HiddenSetup)
      {secret | let claim := ROM.run (beforeHash environment secret) (a ⟨m,beforeArtifact environment⟩)
        claim.2 = (secret.2 claim.1).get false ∨ claim.2 = (secret.2 claim.1).get true} ≤
        (4 : ENNReal)/2^256 + (3002 : ENNReal)*q/2^256 := by
  classical
  let baseline := ROM.hash (extendOracleTable inputs environment.2.2.2)
  let program := a ⟨m,beforeArtifact environment⟩
  let guess := ROM.run baseline program
  let baselineWin : Set HiddenSetup :=
    {secret | guess.2 = (secret.2 guess.1).get false ∨ guess.2 = (secret.2 guess.1).get true}
  let changed : Set HiddenSetup :=
    {secret | ROM.run baseline program ≠ ROM.run (beforeHash environment secret) program}
  have subset : {secret : HiddenSetup |
      let claim := ROM.run (beforeHash environment secret) program
      claim.2 = (secret.2 claim.1).get false ∨ claim.2 = (secret.2 claim.1).get true} ⊆
      baselineWin ∪ changed := by
    intro secret win
    by_cases same : ROM.run baseline program = ROM.run (beforeHash environment secret) program
    · apply Or.inl
      change guess.2 = (secret.2 guess.1).get false ∨ guess.2 = (secret.2 guess.1).get true
      simpa only [Set.mem_setOf_eq, ← same, guess] using win
    · exact Or.inr same
  have guessing : uniformOn (Set.univ : Set HiddenSetup) baselineWin ≤ (4 : ENNReal)/2^256 := by
    have event_eq : baselineWin = (Set.univ : Set HiddenChainTape) ×ˢ
        {labels | guess.2 = (labels guess.1).get false ∨ guess.2 = (labels guess.1).get true} := by
      ext secret
      simp only [baselineWin, Set.mem_setOf_eq, Set.mem_prod, Set.mem_univ, true_and]
    rw [event_eq]
    rw [uniform_product, Measure.prod_prod, measure_univ, one_mul]
    exact uniform_no_label_guess guess
  have querying : uniformOn (Set.univ : Set HiddenSetup) changed ≤ (3002 : ENNReal)*q/2^256 :=
    hidden_setup_program_difference environment.2.1 _ (beforeAnswers environment) baseline
      program q (bound ⟨m,beforeArtifact environment⟩)
  exact (measure_mono subset).trans ((measure_union_le _ _).trans (add_le_add guessing querying))

end WotsLamport.Submission
