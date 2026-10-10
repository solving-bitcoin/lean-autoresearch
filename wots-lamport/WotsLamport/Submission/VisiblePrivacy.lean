import WotsLamport.Submission.Exposed
import WotsLamport.Submission.InterpolationBridge
import WotsLamport.Submission.ShamirLaw

namespace WotsLamport.Submission
open SecretRelease WotsLamport.Protected

def visibleCoordinates (m : Message) (i : Fin 256) (value : Bool) : Finset (ZMod 65537) :=
  (((visibleSlots m i value).map fun entry => entry.2+1).map
    fun n : Nat => (n : ZMod 65537)).toFinset

theorem visibleCoordinates_card (m : Message) (i : Fin 256) (value : Bool) :
    (visibleCoordinates m i value).card = (visibleSlots m i value).length := by
  have hb : ∀ n ∈ (visibleSlots m i value).map (fun entry => entry.2+1), n < prime := by
    intro n hn
    obtain ⟨entry, he, rfl⟩ := List.mem_map.mp hn
    exact (visibleSlots_bounds m i value entry he).2
  have hd := List.Nodup.map_on (f := fun n : Nat => (n : ZMod 65537))
    (fun a ha b hb' he => by
      by_contra hne
      exact field_coordinate_ne a b (hb a ha) (hb b hb') hne he)
    (visibleSlots_distinct m i value)
  unfold visibleCoordinates
  rw [List.toFinset_card_of_nodup hd]
  simp only [List.length_map]

theorem visibleCoordinates_nonzero (m : Message) (i : Fin 256) (value : Bool) :
    (0 : ZMod 65537) ∉ visibleCoordinates m i value := by
  intro hzero
  unfold visibleCoordinates at hzero
  obtain ⟨n, hn, he⟩ := List.mem_map.mp (List.mem_toFinset.mp hzero)
  obtain ⟨entry, hentry, rfl⟩ := List.mem_map.mp hn
  have hb := visibleSlots_bounds m i value entry hentry
  exact field_coordinate_ne (entry.2+1) 0 hb.2 (by decide) (by omega) he

theorem opposite_visibleCoordinates_few (m : Message) (i : Fin 256) :
    (visibleCoordinates m i (!(outputCodec.encode m)[i.val])).card <
      threshold (!(outputCodec.encode m)[i.val]) := by
  have hc := visibleCoordinates_card m i (!(outputCodec.encode m)[i.val])
  have h := visibleSlots_opposite_length m i
  omega

/-- The actual opposite-label coordinates satisfy the uniform-polynomial
privacy theorem. This does not replace the sampler-distance or ROM coupling
needed to describe the adversary's complete view. -/
theorem opposite_uniform_shares (m : Message) (i : Fin 256) (a b : ZMod 65537)
    (event : Set (visibleCoordinates m i (!(outputCodec.encode m)[i.val]) → ZMod 65537)) :
    ProbabilityTheory.uniformOn
      (Set.univ : Set (Shamir.SecretPolynomials (threshold (!(outputCodec.encode m)[i.val])) a))
      {p | Shamir.observedValues (visibleCoordinates m i (!(outputCodec.encode m)[i.val])) p ∈ event} =
    ProbabilityTheory.uniformOn
      (Set.univ : Set (Shamir.SecretPolynomials (threshold (!(outputCodec.encode m)[i.val])) b))
      {p | Shamir.observedValues (visibleCoordinates m i (!(outputCodec.encode m)[i.val])) p ∈ event} := by
  exact Shamir.uniform_shares_secret_independent _ (visibleCoordinates_nonzero m i _)
    _ (opposite_visibleCoordinates_few m i) a b event

end WotsLamport.Submission
