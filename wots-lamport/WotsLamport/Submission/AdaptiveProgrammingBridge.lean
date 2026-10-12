import WotsLamport.Submission.AdaptiveCoinLaw
import WotsLamport.Submission.PreReleaseFiniteGame

namespace WotsLamport.Submission
open SecretRelease WotsLamport.Protected MeasureTheory ProbabilityTheory

def beforeCoinCoordinates (inputs : Finset OracleInput) :
    (BeforeEnvironment inputs × HiddenSetup) ≃ Bytes randomnessBytes × AdaptiveAux inputs where
  toFun sample := (sample.1.1,sample.1.2.1,sample.2.1,sample.2.2,sample.1.2.2.1,sample.1.2.2.2)
  invFun sample := ((sample.1,sample.2.1,sample.2.2.2.2.1,sample.2.2.2.2.2),sample.2.2.1,sample.2.2.2.1)
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable def rawCoinCoordinates (inputs : Finset OracleInput) :
    RawProgrammedSample inputs ≃ Bytes randomnessBytes × AdaptiveAux inputs :=
  (beforeReleaseCoordinates inputs).trans (beforeCoinCoordinates inputs)

theorem actual_field_answers_ciphertext (coins : Bytes randomnessBytes) (labels : Fin 256 → Pair)
    (answers : ArtifactAnswers) :
    fieldArtifactAnswers labels (polynomialTableEquiv (actualFieldTable coins))
      (artifactCiphertextCoordinates (ByteArray.mk coins.toArray) labels answers) = answers := by
  unfold fieldArtifactAnswers
  rw [actual_field_artifact_coordinates, Equiv.symm_apply_apply]

theorem rawCoinCoordinates_tape (inputs : Finset OracleInput) (sample : RawProgrammedSample inputs) :
    chainPartitionEquiv.symm ((rawCoinCoordinates inputs sample).2.1,
      (rawCoinCoordinates inputs sample).2.2.1) = sample.2.1 := by
  change chainPartitionEquiv.symm (chainPartitionEquiv sample.2.1) = _
  exact chainPartitionEquiv.symm_apply_apply sample.2.1

theorem rawCoinCoordinates_hash (inputs : Finset OracleInput) (sample : RawProgrammedSample inputs) :
    let moved := rawCoinCoordinates inputs sample
    rawAfterHash ((ByteArray.mk moved.1.toArray).extract 0 32) moved.2.1
      (moved.2.2.1,moved.2.2.2.1,polynomialTableEquiv (actualFieldTable moved.1)) moved.2.2.2.2.1
      (ROM.hash (extendOracleTable inputs moved.2.2.2.2.2)) =
    programmedHash ((ByteArray.mk sample.1.1.toArray).extract 0 32) sample.2.1 sample.1.2 sample.2.2.1
      (ROM.hash (extendOracleTable inputs sample.2.2.2)) := by
  dsimp only
  unfold rawAfterHash
  rw [rawCoinCoordinates_tape]
  change programmedHash _ _ sample.1.2
      (fieldArtifactAnswers sample.1.2 (polynomialTableEquiv (actualFieldTable sample.1.1))
        (artifactCiphertextCoordinates (ByteArray.mk sample.1.1.toArray) sample.1.2 sample.2.2.1)) _ = _
  rw [actual_field_answers_ciphertext]
  rfl

/-- The protected claim predicate, with the already-created artifact explicit. -/
def adaptiveSuccess (h : Hash) (keys : Keys) (labels : Fin 256 → Pair) (artifact : ByteArray)
    (a : AdaptiveAdversary) : Prop :=
  let chosen := ROM.run h (a.choose artifact)
  let claim := ROM.run h (a.finish chosen.2
    ⟨chosen.1,artifact,signatureBytes (sign h keys chosen.1),selectedOutputBytes labels chosen.1⟩)
  claim.2 = (labels claim.1).get (!(outputCodec.encode chosen.1)[claim.1.val])

def tapeAdaptiveSuccess (h : Hash) (tape : ChainTape) (labels : Fin 256 → Pair) (artifact : ByteArray)
    (a : AdaptiveAdversary) : Prop :=
  let chosen := ROM.run h (a.choose artifact)
  let claim := ROM.run h (a.finish chosen.2
    ⟨chosen.1,artifact,signatureBytes (tapeSignature tape chosen.1),selectedOutputBytes labels chosen.1⟩)
  claim.2 = (labels claim.1).get (!(outputCodec.encode chosen.1)[claim.1.val])

theorem adaptiveSuccess_tape (h : Hash) (tape : ChainTape) (consistent : TapeConsistent h tape)
    (labels : Fin 256 → Pair) (artifact : ByteArray) (a : AdaptiveAdversary) :
    adaptiveSuccess h (tapeKeys tape) labels artifact a ↔ tapeAdaptiveSuccess h tape labels artifact a := by
  simp only [adaptiveSuccess, tapeAdaptiveSuccess, sign_tape h tape consistent]

def finiteAdaptiveEvent (inputs : Finset OracleInput) (coins : Bytes randomnessBytes)
    (labels : Fin 256 → Pair) (a : AdaptiveAdversary) : Set (FiniteChainReal inputs) :=
  {sample | let h := ROM.hash (extendOracleTable inputs sample.2)
    adaptiveSuccess h sample.1 labels (keyCodec.encode (publicKey h sample.1) ++
      prepare h (ByteArray.mk coins.toArray) sample.1 labels) a}

def rawProgrammedAdaptiveEvent (inputs : Finset OracleInput)
    (contains : wotsProgrammingInputs ⊆ inputs) (a : AdaptiveAdversary) : Set (RawProgrammedSample inputs) :=
  {sample | combinedProgram inputs contains ((ByteArray.mk sample.1.1.toArray).extract 0 32)
      (coin_nonce_size sample.1.1) sample.1.2 sample.2 ∈ finiteAdaptiveEvent inputs sample.1.1 sample.1.2 a}

theorem rawCoinCoordinates_event (inputs : Finset OracleInput) (sample : RawProgrammedSample inputs)
    (a : AdaptiveAdversary) :
    rawCoinCoordinates inputs sample ∈ coinAdaptiveEvent inputs a ↔
      tapeAdaptiveSuccess
        (programmedHash ((ByteArray.mk sample.1.1.toArray).extract 0 32) sample.2.1 sample.1.2 sample.2.2.1
          (ROM.hash (extendOracleTable inputs sample.2.2.2))) sample.2.1 sample.1.2
        (keyCodec.encode (tapePublicKey sample.2.1) ++
          ciphertextBody ((ByteArray.mk sample.1.1.toArray).extract 0 32)
            (artifactCiphertextCoordinates (ByteArray.mk sample.1.1.toArray) sample.1.2 sample.2.2.1).2
            (artifactCiphertextCoordinates (ByteArray.mk sample.1.1.toArray) sample.1.2 sample.2.2.1).1) a := by
  change tapeAdaptiveSuccess
    (rawAfterHash ((ByteArray.mk (rawCoinCoordinates inputs sample).1.toArray).extract 0 32)
      (rawCoinCoordinates inputs sample).2.1
      ((rawCoinCoordinates inputs sample).2.2.1,(rawCoinCoordinates inputs sample).2.2.2.1,
        polynomialTableEquiv (actualFieldTable (rawCoinCoordinates inputs sample).1))
      (rawCoinCoordinates inputs sample).2.2.2.2.1
      (ROM.hash (extendOracleTable inputs (rawCoinCoordinates inputs sample).2.2.2.2.2)))
    (chainPartitionEquiv.symm ((rawCoinCoordinates inputs sample).2.1,
      (rawCoinCoordinates inputs sample).2.2.1))
    (rawCoinCoordinates inputs sample).2.2.2.1
    (ciphertextArtifact ((ByteArray.mk (rawCoinCoordinates inputs sample).1.toArray).extract 0 32)
      (rawCoinCoordinates inputs sample).2.1 (rawCoinCoordinates inputs sample).2.2.2.2.1) a ↔ _
  rw [rawCoinCoordinates_hash inputs sample, rawCoinCoordinates_tape inputs sample]
  rfl

theorem programmed_adaptive_event_good (inputs : Finset OracleInput)
    (contains : wotsProgrammingInputs ⊆ inputs) (a : AdaptiveAdversary)
    (sample : RawProgrammedSample inputs) (distinct : Function.Injective sample.2.1) :
    sample ∈ rawProgrammedAdaptiveEvent inputs contains a ↔
      rawCoinCoordinates inputs sample ∈ coinAdaptiveEvent inputs a := by
  let h := programmedHash ((ByteArray.mk sample.1.1.toArray).extract 0 32)
    sample.2.1 sample.1.2 sample.2.2.1 (ROM.hash (extendOracleTable inputs sample.2.2.2))
  have consistent : TapeConsistent h sample.2.1 := programmedHash_consistent _ _ _ _ _ distinct
  unfold rawProgrammedAdaptiveEvent finiteAdaptiveEvent
  simp only [Set.mem_setOf_eq]
  change adaptiveSuccess
    (ROM.hash (extendOracleTable inputs (combinedProgram inputs contains
      ((ByteArray.mk sample.1.1.toArray).extract 0 32) (coin_nonce_size sample.1.1) sample.1.2 sample.2).2))
    (tapeKeys sample.2.1) sample.1.2
    (keyCodec.encode (publicKey
      (ROM.hash (extendOracleTable inputs (combinedProgram inputs contains
        ((ByteArray.mk sample.1.1.toArray).extract 0 32) (coin_nonce_size sample.1.1) sample.1.2 sample.2).2))
      (tapeKeys sample.2.1)) ++ prepare
      (ROM.hash (extendOracleTable inputs (combinedProgram inputs contains
        ((ByteArray.mk sample.1.1.toArray).extract 0 32) (coin_nonce_size sample.1.1) sample.1.2 sample.2).2))
      (ByteArray.mk sample.1.1.toArray) (tapeKeys sample.2.1) sample.1.2) a ↔ _
  rw [combinedProgram_hash inputs contains _ _ sample.1.2 sample.2 distinct]
  rw [publicKey_tape h sample.2.1 consistent, prepare_programmedHash_ciphertext _ _ _ _ _ distinct,
    adaptiveSuccess_tape h sample.2.1 consistent]
  exact (rawCoinCoordinates_event inputs sample a).symm

end WotsLamport.Submission
