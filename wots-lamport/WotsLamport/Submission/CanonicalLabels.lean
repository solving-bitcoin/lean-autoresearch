import WotsLamport.Submission.VisibleCoefficientPrivacy

namespace WotsLamport.Submission
open SecretRelease WotsLamport.Protected

/-- A deterministic partner depending only on the authorized label. Choosing
zero alone would violate Pair's distinctness invariant when that label is zero. -/
noncomputable def canonicalPartner (label : Label) : Label := by
  classical
  exact if label = Vector.replicate 32 0 then Vector.replicate 32 1 else Vector.replicate 32 0

theorem canonicalPartner_ne (label : Label) : canonicalPartner label ≠ label := by
  classical
  unfold canonicalPartner
  split_ifs with he
  · subst label
    decide +kernel
  · exact fun equal => he equal.symm

noncomputable def canonicalPair (selected : Label) (bit : Bool) : Pair :=
  if bit then ⟨(canonicalPartner selected, selected), canonicalPartner_ne selected⟩
  else ⟨(selected, canonicalPartner selected), (canonicalPartner_ne selected).symm⟩

theorem canonicalPair_selected (selected : Label) (bit : Bool) :
    (canonicalPair selected bit).get bit = selected := by
  cases bit <;> rfl

noncomputable def canonicalLabelTable (bits : Fin 256 → Bool) (selected : Fin 256 → Label) :
    Fin 256 → Pair := fun i => canonicalPair (selected i) (bits i)

theorem canonicalLabelTable_selected (bits : Fin 256 → Bool) (labels : Fin 256 → Pair) (i : Fin 256) :
    (canonicalLabelTable bits (fun j => (labels j).get (bits j)) i).get (bits i) =
      (labels i).get (bits i) := canonicalPair_selected _ _

theorem canonicalLabelTable_depends_only_selected (bits : Fin 256 → Bool)
    (a b : Fin 256 → Pair) (selected : ∀ i, (a i).get (bits i) = (b i).get (bits i)) :
    canonicalLabelTable bits (fun i => (a i).get (bits i)) =
      canonicalLabelTable bits (fun i => (b i).get (bits i)) := by
  exact congrArg (canonicalLabelTable bits) (funext selected)

end WotsLamport.Submission
