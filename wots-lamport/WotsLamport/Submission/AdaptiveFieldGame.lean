import WotsLamport.Submission.RawAfterReleaseLaw
import WotsLamport.Protected.Adaptive

namespace WotsLamport.Submission
open SecretRelease WotsLamport.Protected MeasureTheory ProbabilityTheory OracleComp

def ciphertextArtifact (nonce : ByteArray) (pk : PublicKey)
    (coordinates : (SharePosition → Bytes 64) × (CommitmentCell → Label)) : ByteArray :=
  keyCodec.encode pk ++ ciphertextBody nonce coordinates.2 coordinates.1

def innerCoefficientCoordinates : AfterInnerSample ≃ AllocatedCoefficients × HiddenSetup where
  toFun sample := (sample.2.2,sample.1,sample.2.1)
  invFun sample := (sample.2.1,sample.2.2,sample.1)
  left_inv _ := rfl
  right_inv _ := rfl

theorem field_choose_difference_bound {A : Type} (nonce : ByteArray) (pk : PublicKey)
    (coordinates : (SharePosition → Bytes 64) × (CommitmentCell → Label)) (baseline : Hash)
    (program : Program A) (q : Nat) (bound : IsTotalQueryBound program q) :
    uniformOn (Set.univ : Set AfterInnerSample)
      {sample | ROM.run baseline program ≠ ROM.run (rawAfterHash nonce pk sample coordinates baseline) program} ≤
        (3002 : ENNReal)*q/2^256 := by
  classical
  let event : Set (AllocatedCoefficients × HiddenSetup) :=
    {sample | ROM.run baseline program ≠ ROM.run
      (programmedHash nonce (chainPartitionEquiv.symm (pk,sample.2.1)) sample.2.2
        (fieldArtifactAnswers sample.2.2 sample.1 coordinates) baseline) program}
  change uniformOn (Set.univ : Set AfterInnerSample) (innerCoefficientCoordinates ⁻¹' event) ≤ _
  rw [Shamir.uniform_event_equiv, uniform_product]
  apply product_event_constant_bound
  intro coefficients
  exact hidden_setup_program_difference pk nonce
    (fun secret => fieldArtifactAnswers secret.2 coefficients coordinates) baseline program q bound

def fieldAdaptiveEvent (nonce : ByteArray)
    (coordinates : (SharePosition → Bytes 64) × (CommitmentCell → Label)) (baseline : Hash)
    (a : AdaptiveAdversary) : Set (PublicKey × AfterInnerSample) :=
  {sample | let h := rawAfterHash nonce sample.1 sample.2 coordinates baseline
    let chosen := ROM.run h (a.choose (ciphertextArtifact nonce sample.1 coordinates))
    let claim := ROM.run h (a.finish chosen.2 (rawAfterView chosen.1 nonce sample.1 sample.2 coordinates))
    claim.2 = (sample.2.2.1 claim.1).get (!(outputCodec.encode chosen.1)[claim.1.val])}

def baselineChooseFieldEvent (nonce : ByteArray)
    (coordinates : (SharePosition → Bytes 64) × (CommitmentCell → Label)) (baseline : Hash)
    (a : AdaptiveAdversary) : Set (PublicKey × AfterInnerSample) :=
  {sample | let chosen := ROM.run baseline (a.choose (ciphertextArtifact nonce sample.1 coordinates))
    sample.2 ∈ rawAfterEvent chosen.1 nonce sample.1 coordinates baseline (a.finish chosen.2)}

/-- The artifact-first phase is compared before selecting any message-specific
partition. Its complete returned state is coupled together with the message. -/
theorem field_choose_event_comparison (nonce : ByteArray)
    (coordinates : (SharePosition → Bytes 64) × (CommitmentCell → Label)) (baseline : Hash)
    (a : AdaptiveAdversary) (q : Nat) (bound : ROM.Bounded a.choose q) :
    uniformOn (Set.univ : Set (PublicKey × AfterInnerSample)) (fieldAdaptiveEvent nonce coordinates baseline a) ≤
      uniformOn (Set.univ : Set (PublicKey × AfterInnerSample))
        (baselineChooseFieldEvent nonce coordinates baseline a) + (3002 : ENNReal)*q/2^256 := by
  classical
  rw [uniform_product]
  apply product_event_bound
  intro pk
  let program := a.choose (ciphertextArtifact nonce pk coordinates)
  let good : Set AfterInnerSample := {sample |
    ROM.run baseline program = ROM.run (rawAfterHash nonce pk sample coordinates baseline) program}
  have comparison := event_bound_of_agree_on_good (uniformOn (Set.univ : Set AfterInnerSample))
    {sample | (pk,sample) ∈ fieldAdaptiveEvent nonce coordinates baseline a}
    {sample | (pk,sample) ∈ baselineChooseFieldEvent nonce coordinates baseline a}
    good (by
      intro sample same
      change ROM.run baseline program = ROM.run (rawAfterHash nonce pk sample coordinates baseline) program at same
      change
        (let chosen := ROM.run (rawAfterHash nonce pk sample coordinates baseline) program
         let claim := ROM.run (rawAfterHash nonce pk sample coordinates baseline)
           (a.finish chosen.2 (rawAfterView chosen.1 nonce pk sample coordinates))
         claim.2 = (sample.2.1 claim.1).get (!(outputCodec.encode chosen.1)[claim.1.val])) ↔ _
      rw [← same]
      rfl)
  exact comparison.trans (add_le_add le_rfl
    (field_choose_difference_bound nonce pk coordinates baseline program q (bound _)))

/-- Adaptive chosen-message security in the uniform-field programmed game.
This is still an intermediate game; the protected ROM game and actual modular
coefficient sampler must be related to it with their explicit losses. -/
theorem field_adaptive_probability_bound (nonce : ByteArray)
    (coordinates : (SharePosition → Bytes 64) × (CommitmentCell → Label)) (baseline : Hash)
    (a : AdaptiveAdversary) (q₁ q₂ : Nat) (chooseBound : ROM.Bounded a.choose q₁)
    (finishBound : ∀ state, ROM.Bounded (a.finish state) q₂) :
    uniformOn (Set.univ : Set (PublicKey × AfterInnerSample)) (fieldAdaptiveEvent nonce coordinates baseline a) ≤
      ((1056 : ENNReal)^2/2^256 + ((512 : ENNReal)/2^256 + (1501 : ENNReal)*q₂/2^256)) +
        (3002 : ENNReal)*q₁/2^256 := by
  let choice pk := ROM.run baseline (a.choose (ciphertextArtifact nonce pk coordinates))
  have finishing := rawAfterEvent_public_bound nonce coordinates baseline
    (fun pk => (choice pk).1) (fun pk => a.finish (choice pk).2) q₂
    (fun pk => finishBound (choice pk).2)
  exact (field_choose_event_comparison nonce coordinates baseline a q₁ chooseBound).trans
    (add_le_add finishing le_rfl)

end WotsLamport.Submission
