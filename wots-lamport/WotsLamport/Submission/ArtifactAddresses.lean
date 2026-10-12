import WotsLamport.Submission.ChainTape
import WotsLamport.Submission.DomainInjectivity

namespace WotsLamport.Submission
open SecretRelease WotsLamport.Protected

abbrev SharePosition := {slot : Fin 256 × Bool × Fin 1984 //
  slot.2.2.val < if slot.2.1 then 1982 else 1984}
abbrev MaskCell := SharePosition × Bool
abbrev CommitmentCell := Fin 256 × Bool

def sharePositionEntry (position : SharePosition) : Fin 67 × Nat :=
  (slots position.val.1 position.val.2.1)[position.val.2.2.val]'(by
    rw [slots_length]
    exact position.property)

theorem slot_entry_nonpublic (i : Fin 256) (value : Bool) (entry : Fin 67 × Nat)
    (member : entry ∈ slots i value) : entry.2 < maximum entry.1 := by
  unfold slots at member
  obtain ⟨j, _, hj⟩ := List.mem_flatMap.mp member
  obtain ⟨k, hk, hentry⟩ := List.mem_flatMap.mp hj
  have he := List.eq_of_mem_replicate hentry
  rw [he]
  exact List.mem_range.mp hk

def sharePositionEdge (position : SharePosition) : ChainEdge :=
  let entry := sharePositionEntry position
  have member : entry ∈ slots position.val.1 position.val.2.1 :=
    List.mem_of_getElem (a := entry) rfl
  have bound := slot_entry_nonpublic _ _ entry member
  ⟨⟨entry.1, ⟨entry.2, Nat.lt_succ_of_lt bound⟩⟩, bound⟩

def sharePositionNode (tape : ChainTape) (position : SharePosition) : Label :=
  tape (sharePositionEdge position).val

def artifactMaskAddress (pk nonce : ByteArray) (nodes : SharePosition → Label)
    (cell : MaskCell) : ByteArray :=
  maskQuery pk nonce cell.1.val.1.val cell.1.val.2.1 (cell.1.val.2.2.val+1)
    (nodes cell.1) (if cell.2 then 1 else 0)

def artifactCommitmentAddress (pk nonce : ByteArray) (labels : Fin 256 → Pair)
    (cell : CommitmentCell) : ByteArray :=
  commitmentQuery pk nonce cell.1.val cell.2 ((labels cell.1).get cell.2)

theorem artifactMaskAddress_injective (pk nonce : ByteArray) (nodes : SharePosition → Label) :
    Function.Injective (artifactMaskAddress pk nonce nodes) := by
  intro a b he
  obtain ⟨wire,value,point,_,block⟩ := maskQuery_injective pk nonce he
  exact Prod.ext (Subtype.ext (Prod.ext wire (Prod.ext value point))) block

theorem artifactCommitmentAddress_injective (pk nonce : ByteArray) (labels : Fin 256 → Pair) :
    Function.Injective (artifactCommitmentAddress pk nonce labels) := by
  intro a b he
  obtain ⟨wire,value,_⟩ := commitmentQuery_injective pk nonce he
  exact Prod.ext wire value

abbrev ArtifactCell := MaskCell ⊕ CommitmentCell

def artifactCellAddress (pk nonce : ByteArray) (nodes : SharePosition → Label)
    (labels : Fin 256 → Pair) : ArtifactCell → ByteArray :=
  Sum.elim (artifactMaskAddress pk nonce nodes) (artifactCommitmentAddress pk nonce labels)

theorem artifactCellAddress_injective (pk nonce : ByteArray) (nodes : SharePosition → Label)
    (labels : Fin 256 → Pair) : Function.Injective (artifactCellAddress pk nonce nodes labels) := by
  intro a b he
  cases a with
  | inl a =>
    cases b with
    | inl b => exact congrArg Sum.inl (artifactMaskAddress_injective pk nonce nodes he)
    | inr b => exact False.elim (maskQuery_ne_commitmentQuery pk nonce _ _ _ _ _ _ _ _ he)
  | inr a =>
    cases b with
    | inl b => exact False.elim (maskQuery_ne_commitmentQuery pk nonce _ _ _ _ _ _ _ _ he.symm)
    | inr b => exact congrArg Sum.inr (artifactCommitmentAddress_injective pk nonce labels he)

theorem artifactCellAddress_ne_chain (pk nonce : ByteArray) (nodes : SharePosition → Label)
    (labels : Fin 256 → Pair) (cell : ArtifactCell) (node : Label) :
    artifactCellAddress pk nonce nodes labels cell ≠ ByteArray.mk node.toArray := by
  cases cell with
  | inl cell => exact maskQuery_ne_chain pk nonce _ _ _ _ node _
  | inr cell => exact commitmentQuery_ne_chain pk nonce _ _ _ node

end WotsLamport.Submission
