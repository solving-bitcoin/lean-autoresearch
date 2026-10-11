import WotsLamport.Submission.FieldPlaintext
import WotsLamport.Submission.ProgrammedQueryTrace
import WotsLamport.Submission.MessagePartition

namespace WotsLamport.Submission
open SecretRelease WotsLamport.Protected

/-- Removing programmed cells changes the oracle only at removed addresses.
The injectivity premise prevents ambiguous overlapping programmed answers. -/
theorem overlayOracle_restrict {I D R : Type} (address : I → D) (answer : I → R)
    (baseline : D → R) (injective : Function.Injective address) (keep : I → Prop)
    (input : D) (missing : ∀ i, ¬keep i → address i ≠ input) :
    overlayOracle address answer baseline input =
      overlayOracle (fun i : {i // keep i} => address i.val)
        (fun i => answer i.val) baseline input := by
  classical
  by_cases found : ∃ i, address i = input
  · obtain ⟨i,hi⟩ := found
    have kept : keep i := by by_contra absent; exact missing i absent hi
    subst input
    rw [overlayOracle_at address answer baseline injective i]
    exact (overlayOracle_at (fun j : {i // keep i} => address j.val)
      (fun j => answer j.val) baseline (injective.comp Subtype.val_injective) ⟨i,kept⟩).symm
  · have absent : ∀ i, address i ≠ input := by intro i hi; exact found ⟨i,hi⟩
    rw [overlayOracle_off address answer baseline input absent,
      overlayOracle_off _ _ baseline input (fun i => absent i.val)]

theorem overlayOracle_baseline_congr {I D R : Type} (address : I → D) (answer : I → R)
    (a b : D → R) (input : D) (same : a input = b input) :
    overlayOracle address answer a input = overlayOracle address answer b input := by
  classical
  unfold overlayOracle
  split_ifs
  · rfl
  · exact same

def visibleArtifactCell (m : Message) : ArtifactCell → Prop
  | Sum.inl cell => sharePositionVisible m cell.1
  | Sum.inr cell => cell.2 = (outputCodec.encode m)[cell.1.val]

noncomputable def visibleChainOracle (m : Message) (tape : ChainTape) (baseline : Hash) : Hash :=
  overlayOracle
    (fun edge : {edge : ChainEdge // ¬hiddenAfterMessage m edge} =>
      ByteArray.mk (tape edge.val.val).toArray)
    (fun edge => tape (edgeNext edge.val)) baseline

/-- This is a restricted oracle, not yet an independence theorem. Visible
answer independence additionally needs the coefficient/plaintext transport. -/
noncomputable def visibleProgrammedHash (m : Message) (nonce : ByteArray) (tape : ChainTape)
    (labels : Fin 256 → Pair) (answers : ArtifactAnswers) (baseline : Hash) : Hash :=
  overlayOracle
    (fun cell : {cell : ArtifactCell // visibleArtifactCell m cell} =>
      artifactCellAddress (keyCodec.encode (tapePublicKey tape)) nonce
        (sharePositionNode tape) labels cell.val)
    (fun cell => answers cell.val) (visibleChainOracle m tape baseline)

theorem programmedHash_eq_visible_off_targets (m : Message) (nonce : ByteArray)
    (tape : ChainTape) (distinct : Function.Injective tape) (labels : Fin 256 → Pair)
    (answers : ArtifactAnswers) (baseline : Hash) (input : ByteArray)
    (nodesMissing : ∀ edge : {edge : ChainEdge // hiddenAfterMessage m edge},
      chainMaskQueryTarget (keyCodec.encode (tapePublicKey tape)) nonce input ≠
        some (tape edge.val.val))
    (labelsMissing : ∀ i : Fin 256,
      commitmentQueryTarget (keyCodec.encode (tapePublicKey tape)) nonce input ≠
        some ((labels i).get (!(outputCodec.encode m)[i.val]))) :
    programmedHash nonce tape labels answers baseline input =
      visibleProgrammedHash m nonce tape labels answers baseline input := by
  classical
  have chainMissing (edge : ChainEdge) (hidden : ¬¬hiddenAfterMessage m edge) :
      ByteArray.mk (tape edge.val).toArray ≠ input := by
    intro he
    apply nodesMissing ⟨edge,not_not.mp hidden⟩
    rw [← he]
    exact chainMaskQueryTarget_chain _ _ _
  have artifactMissing (cell : ArtifactCell) (hidden : ¬visibleArtifactCell m cell) :
      artifactCellAddress (keyCodec.encode (tapePublicKey tape)) nonce
        (sharePositionNode tape) labels cell ≠ input := by
    intro he
    cases cell with
    | inl cell =>
      have hiddenEdge : hiddenAfterMessage m (sharePositionEdge cell.1) := by
        change ¬(encodeWord m (sharePositionEntry cell.1).1 ≤
          (sharePositionEntry cell.1).2) at hidden
        exact Nat.lt_of_not_ge hidden
      apply nodesMissing ⟨sharePositionEdge cell.1,hiddenEdge⟩
      rw [← he]
      exact chainMaskQueryTarget_mask _ _ _ _ _ _ _
    | inr cell =>
      have opposite : cell.2 = !(outputCodec.encode m)[cell.1.val] := by
        change cell.2 ≠ (outputCodec.encode m)[cell.1.val] at hidden
        cases hb : cell.2 <;> cases hs : (outputCodec.encode m)[cell.1.val] <;> simp_all
      apply labelsMissing cell.1
      rw [← he, ← opposite]
      exact commitmentQueryTarget_complete _ _ _ _ _
  change overlayOracle _ answers (programChainOracle baseline tape) input = _
  rw [overlayOracle_restrict _ answers (programChainOracle baseline tape)
    (artifactCellAddress_injective _ _ _ _) (visibleArtifactCell m) input artifactMissing]
  apply overlayOracle_baseline_congr
  exact overlayOracle_restrict _ _ baseline (chain_address_injective tape distinct)
    (fun edge => ¬hiddenAfterMessage m edge) input chainMissing

end WotsLamport.Submission
