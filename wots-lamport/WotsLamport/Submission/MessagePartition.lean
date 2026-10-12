import WotsLamport.Submission.ChainPartitionLaw

namespace WotsLamport.Submission
open SecretRelease WotsLamport.Protected MeasureTheory ProbabilityTheory

noncomputable def tablePartitionEquiv {I A : Type} (hidden : I → Prop) :
    (I → A) ≃ ({i : I // hidden i} → A) × ({i : I // ¬hidden i} → A) := by
  classical
  exact {
    toFun := fun table => (fun i => table i.val, fun i => table i.val)
    invFun := fun sample i => if hi : hidden i then sample.1 ⟨i,hi⟩ else sample.2 ⟨i,hi⟩
    left_inv := by intro table; funext i; by_cases hi : hidden i <;> simp [hi]
    right_inv := by
      intro sample
      refine Prod.ext ?_ ?_
      · funext i; simp [i.property]
      · funext i; simp [i.property] }

theorem uniform_table_partition {I A : Type} [Fintype I] [Fintype A] [Nonempty A]
    [MeasurableSpace A] [DiscreteMeasurableSpace A] (hidden : I → Prop) :
    (uniformOn (Set.univ : Set (I → A))).map (tablePartitionEquiv hidden) =
      (uniformOn (Set.univ : Set ({i : I // hidden i} → A))).prod
        (uniformOn (Set.univ : Set ({i : I // ¬hidden i} → A))) := by
  classical
  rw [uniform_map_equiv, uniform_product]

def hiddenAfterMessage (m : Message) (edge : ChainEdge) : Prop :=
  edge.val.2.val < encodeWord m edge.val.1

abbrev MessageHiddenTape (m : Message) := {edge : ChainEdge // hiddenAfterMessage m edge} → Label
abbrev MessageVisibleTape (m : Message) := {edge : ChainEdge // ¬hiddenAfterMessage m edge} → Label

noncomputable def messageChainPartition (m : Message) :
    ChainTape ≃ PublicKey × MessageHiddenTape m × MessageVisibleTape m :=
  chainPartitionEquiv.trans
    (Equiv.prodCongr (Equiv.refl PublicKey) (tablePartitionEquiv (hiddenAfterMessage m)))

def signatureFromVisible (m : Message) (pk : PublicKey) (visible : MessageVisibleTape m) : Signature :=
  fun j => if hd : encodeWord m j < maximum j then
    visible ⟨⟨⟨j, ⟨encodeWord m j, Nat.lt_succ_of_le (encodeWord_le m j)⟩⟩, hd⟩,
      Nat.lt_irrefl _⟩
  else pk j

/-- Every disclosed signature node is determined by endpoints and the visible
suffix table. No hidden prefix node is used to construct the active input. -/
theorem signature_from_visible (m : Message) (tape : ChainTape) :
    signatureFromVisible m (messageChainPartition m tape).1
      (messageChainPartition m tape).2.2 = tapeSignature tape m := by
  funext j
  by_cases hd : encodeWord m j < maximum j
  · simp [signatureFromVisible, hd, messageChainPartition, tablePartitionEquiv,
      chainPartitionEquiv, tapeSignature]
  · have he : encodeWord m j = maximum j := by have := encodeWord_le m j; omega
    simp [signatureFromVisible, hd, messageChainPartition, chainPartitionEquiv,
      tapePublicKey, tapeSignature, he]

theorem messageHidden_card_le (m : Message) :
    Nat.card {edge : ChainEdge // hiddenAfterMessage m edge} ≤ 989 := by
  classical
  rw [Nat.card_eq_fintype_card, ← chainEdge_card]
  exact Fintype.card_subtype_le _

end WotsLamport.Submission
