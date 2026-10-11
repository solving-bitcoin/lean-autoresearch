import WotsLamport.Submission.ArtifactProgramming
import WotsLamport.Submission.JointLabelGuessing

namespace WotsLamport.Submission
open SecretRelease WotsLamport.Protected MeasureTheory ProbabilityTheory OracleComp

def chainMaskQueryTarget (pk nonce input : ByteArray) : Option Label :=
  if input.size = 32 then chainQueryTarget input else maskQueryTarget pk nonce input

theorem chainMaskQueryTarget_chain (pk nonce : ByteArray) (node : Label) :
    chainMaskQueryTarget pk nonce (ByteArray.mk node.toArray) = some node := by
  rw [chainMaskQueryTarget, if_pos (vectorBytes_size node)]
  exact chainQueryTarget_complete node

theorem chainMaskQueryTarget_mask (pk nonce : ByteArray) (wire : Nat) (value : Bool)
    (point : Nat) (node : Label) (block : Nat) :
    chainMaskQueryTarget pk nonce (maskQuery pk nonce wire value point node block) = some node := by
  have hs : (maskQuery pk nonce wire value point node block).size ≠ 32 := by
    rw [maskQuery_size]
    omega
  rw [chainMaskQueryTarget, if_neg hs]
  exact maskQueryTarget_complete pk nonce wire value point node block

/-- Every changed input contains either a complete nonpublic chain node or a
complete label. The answer values may depend on all sampled secrets. -/
theorem programmedHash_off_targets (nonce : ByteArray) (tape : ChainTape)
    (labels : Fin 256 → Pair) (answers : ArtifactAnswers) (baseline : Hash) (input : ByteArray)
    (nodesMissing : ∀ edge : ChainEdge,
      chainMaskQueryTarget (keyCodec.encode (tapePublicKey tape)) nonce input ≠ some (tape edge.val))
    (labelsMissing : ∀ cell : CommitmentCell,
      commitmentQueryTarget (keyCodec.encode (tapePublicKey tape)) nonce input ≠
        some ((labels cell.1).get cell.2)) :
    programmedHash nonce tape labels answers baseline input = baseline input := by
  have artifactMissing : ∀ cell : ArtifactCell,
      artifactCellAddress (keyCodec.encode (tapePublicKey tape)) nonce
        (sharePositionNode tape) labels cell ≠ input := by
    intro cell he
    cases cell with
    | inl cell =>
      apply nodesMissing (sharePositionEdge cell.1)
      rw [← he]
      exact chainMaskQueryTarget_mask _ _ _ _ _ _ _
    | inr cell =>
      apply labelsMissing cell
      rw [← he]
      exact commitmentQueryTarget_complete _ _ _ _ _
  unfold programmedHash programArtifactOracle
  rw [overlayOracle_off _ _ _ _ artifactMissing]
  apply programChainOracle_off_tape
  intro edge he
  apply nodesMissing edge
  rw [← he]
  exact chainMaskQueryTarget_chain _ _ _

abbrev HiddenSetup := HiddenChainTape × (Fin 256 → Pair)
abbrev SetupTarget := ChainEdge ⊕ CommitmentCell

def setupTarget : SetupTarget → HiddenSetup → Label :=
  Sum.elim (fun edge sample => sample.1 edge) (fun cell sample => (sample.2 cell.1).get cell.2)

theorem uniform_setup_target_mass (index : SetupTarget) (label : Label) :
    uniformOn (Set.univ : Set HiddenSetup) {sample | setupTarget index sample = label} ≤
      (2 : ENNReal)/2^256 := by
  classical
  letI := Fintype.ofFinite Label
  letI := Fintype.ofFinite Pair
  cases index with
  | inl edge =>
    have event_eq : {sample : HiddenSetup | setupTarget (Sum.inl edge) sample = label} =
        {hidden : HiddenChainTape | hidden edge = label} ×ˢ (Set.univ : Set (Fin 256 → Pair)) := by
      ext sample
      simp only [setupTarget, Sum.elim_inl, Set.mem_setOf_eq, Set.mem_prod, Set.mem_univ, and_true]
    rw [event_eq]
    rw [uniform_product, Measure.prod_prod, measure_univ, mul_one,
      uniform_coordinate_mass]
    rw [bytes_card]
    simpa only [one_div] using
      (show (1 : ENNReal)/2^256 ≤ (2 : ENNReal)/2^256 from by gcongr <;> norm_num)
  | inr cell =>
    have event_eq : {sample : HiddenSetup | setupTarget (Sum.inr cell) sample = label} =
        (Set.univ : Set HiddenChainTape) ×ˢ
          {labels : Fin 256 → Pair | (labels cell.1).get cell.2 = label} := by
      ext sample
      simp only [setupTarget, Sum.elim_inr, Set.mem_setOf_eq, Set.mem_prod, Set.mem_univ, true_and]
    rw [event_eq]
    rw [uniform_product, Measure.prod_prod, measure_univ, one_mul]
    have h := uniform_selected_table_guess_fixed (fun _ : Fin 256 => !cell.2)
      (fun _ => (cell.1,label)) cell.1
    simpa only [Bool.not_not, eq_comm] using h

/-- Concrete pre-release oracle comparison after separating ciphertexts from
hidden nodes and labels. The program is fixed given its independent public
environment; this theorem does not assume the real artifact already has that
independence. The latter requires the joint programming and ciphertext laws. -/
theorem hidden_setup_program_difference {A : Type} (pk : PublicKey) (nonce : ByteArray)
    (answers : HiddenSetup → ArtifactAnswers) (baseline : Hash) (p : Program A)
    (q : Nat) (bound : IsTotalQueryBound p q) :
    uniformOn (Set.univ : Set HiddenSetup)
      {sample | ROM.run baseline p ≠ ROM.run
        (programmedHash nonce (chainPartitionEquiv.symm (pk,sample.1))
          sample.2 (answers sample) baseline) p} ≤
      (3002 : ENNReal)*q/2^256 := by
  classical
  let parse : SetupTarget → ByteArray → Option Label := Sum.elim
    (fun _ => chainMaskQueryTarget (keyCodec.encode pk) nonce)
    (fun _ => commitmentQueryTarget (keyCodec.encode pk) nonce)
  have publicEq (hidden : HiddenChainTape) :
      tapePublicKey (chainPartitionEquiv.symm (pk,hidden)) = pk :=
    congrArg Prod.fst (chainPartitionEquiv.apply_symm_apply (pk,hidden))
  have off (sample : HiddenSetup) (input : ByteArray)
      (missing : ∀ i, parse i input ≠ some (setupTarget i sample)) :
      baseline input = programmedHash nonce (chainPartitionEquiv.symm (pk,sample.1))
        sample.2 (answers sample) baseline input := by
    apply (programmedHash_off_targets _ _ _ _ _ input ?_ ?_).symm
    · intro edge
      rw [publicEq, chainPartition_hidden]
      exact missing (Sum.inl edge)
    · intro cell
      rw [publicEq]
      exact missing (Sum.inr cell)
  have h := multi_target_run_difference_bound
    (uniformOn (Set.univ : Set HiddenSetup)) setupTarget ((2 : ENNReal)/2^256)
    uniform_setup_target_mass parse baseline
    (fun sample => programmedHash nonce (chainPartitionEquiv.symm (pk,sample.1))
      sample.2 (answers sample) baseline) off p q bound
  have card : Fintype.card SetupTarget = 1501 := by
    simp only [SetupTarget, CommitmentCell, Fintype.card_sum, Fintype.card_prod,
      Fintype.card_fin, Fintype.card_bool, chainEdge_card]
  calc
    _ ≤ (1501 : ENNReal)*q*((2 : ENNReal)/2^256) := by simpa only [card, Nat.cast_ofNat] using h
    _ = _ := by simp only [div_eq_mul_inv]; ring

end WotsLamport.Submission
