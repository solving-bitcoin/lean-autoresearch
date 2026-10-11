import WotsLamport.Submission.VisibleProgrammedOracle

namespace WotsLamport.Submission
open SecretRelease WotsLamport.Protected

theorem chainTape_visible_eq (m : Message) (a b : ChainTape)
    (endpoints : tapePublicKey a = tapePublicKey b)
    (visible : (messageChainPartition m a).2.2 = (messageChainPartition m b).2.2)
    (position : ChainPosition) (disclosed : encodeWord m position.1 ≤ position.2.val) :
    a position = b position := by
  by_cases edge : position.2.val < maximum position.1
  · exact congrFun visible ⟨⟨position,edge⟩, Nat.not_lt.mpr disclosed⟩
  · have last : position.2 = (⟨maximum position.1, Nat.lt_succ_self _⟩ : Fin (maximum position.1+1)) :=
      Fin.ext (by
        change position.2.val = maximum position.1
        have := position.2.isLt
        omega)
    have he := congrFun endpoints position.1
    change a ⟨position.1, _⟩ = b ⟨position.1, _⟩ at he
    change a ⟨position.1,position.2⟩ = b ⟨position.1,position.2⟩
    rw [last]
    exact he

theorem visibleChainOracle_tape_congr (m : Message) (a b : ChainTape)
    (endpoints : tapePublicKey a = tapePublicKey b)
    (visible : (messageChainPartition m a).2.2 = (messageChainPartition m b).2.2)
    (baseline : Hash) : visibleChainOracle m a baseline = visibleChainOracle m b baseline := by
  have sources :
      (fun edge : {edge : ChainEdge // ¬hiddenAfterMessage m edge} =>
        ByteArray.mk (a edge.val.val).toArray) =
      (fun edge : {edge : ChainEdge // ¬hiddenAfterMessage m edge} =>
        ByteArray.mk (b edge.val.val).toArray) := by
    funext edge
    rw [chainTape_visible_eq m a b endpoints visible edge.val.val
      (Nat.le_of_not_gt edge.property)]
  have outputs :
      (fun edge : {edge : ChainEdge // ¬hiddenAfterMessage m edge} => a (edgeNext edge.val)) =
      (fun edge : {edge : ChainEdge // ¬hiddenAfterMessage m edge} => b (edgeNext edge.val)) := by
    funext edge
    apply chainTape_visible_eq m a b endpoints visible
    have hd := Nat.le_of_not_gt edge.property
    change encodeWord m edge.val.val.1 ≤ edge.val.val.2.val+1
    omega
  unfold visibleChainOracle
  rw [sources, outputs]

/-- A restricted oracle with fixed answer table depends only on the public
endpoints and disclosed suffix nodes, not the undisclosed prefix nodes. -/
theorem visibleProgrammedHash_tape_congr (m : Message) (nonce : ByteArray) (a b : ChainTape)
    (endpoints : tapePublicKey a = tapePublicKey b)
    (visible : (messageChainPartition m a).2.2 = (messageChainPartition m b).2.2)
    (labels : Fin 256 → Pair) (answers : ArtifactAnswers) (baseline : Hash) :
    visibleProgrammedHash m nonce a labels answers baseline =
      visibleProgrammedHash m nonce b labels answers baseline := by
  have addresses :
      (fun cell : {cell : ArtifactCell // visibleArtifactCell m cell} =>
        artifactCellAddress (keyCodec.encode (tapePublicKey a)) nonce (sharePositionNode a) labels cell.val) =
      (fun cell : {cell : ArtifactCell // visibleArtifactCell m cell} =>
        artifactCellAddress (keyCodec.encode (tapePublicKey b)) nonce (sharePositionNode b) labels cell.val) := by
    funext cell
    rw [endpoints]
    rcases cell with ⟨cell,hv⟩
    cases cell with
    | inl cell =>
      have node := chainTape_visible_eq m a b endpoints visible (sharePositionEdge cell.1).val hv
      change maskQuery _ _ _ _ _ (sharePositionNode a cell.1) _ =
        maskQuery _ _ _ _ _ (sharePositionNode b cell.1) _
      rw [show sharePositionNode a cell.1 = sharePositionNode b cell.1 from node]
    | inr cell => rfl
  unfold visibleProgrammedHash
  rw [addresses, visibleChainOracle_tape_congr m a b endpoints visible baseline]

end WotsLamport.Submission
