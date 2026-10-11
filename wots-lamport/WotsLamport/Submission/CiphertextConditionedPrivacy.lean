import WotsLamport.Submission.AdaptiveMaskedView

namespace WotsLamport.Submission
open SecretRelease MeasureTheory ProbabilityTheory

/-- Work in ciphertext/coefficient coordinates. The comparison plaintext may
itself depend on the ciphertext, for example through a later chosen message
and its canonical opposite-label table. This does not require solving a
ciphertext-dependent plaintext equation in the original pad coordinates. -/
def conditionedMaskedView {C I K : Type} {n : Nat}
    (visible : (I → Bytes n) → I → Bool)
    (plain : (I → Bytes n) → C → I → Bytes n)
    (observation : (I → Bytes n) → C → K)
    (sample : (I → Bytes n) × C) :
    (I → Bytes n) × K × (I → Option (Bytes n)) :=
  (sample.1, observation sample.1 sample.2,
    fun i => if visible sample.1 i then
      some (xorVector (sample.1 i) (plain sample.1 sample.2 i)) else none)

theorem conditionedMaskedView_transport {C I K : Type} {n : Nat}
    (e : (I → Bytes n) → C ≃ C)
    (a b : (I → Bytes n) → C → I → Bytes n)
    (visible : (I → Bytes n) → I → Bool)
    (obsA obsB : (I → Bytes n) → C → K)
    (observed : ∀ ciphertext c, obsB ciphertext (e ciphertext c) = obsA ciphertext c)
    (visibleEqual : ∀ ciphertext c i, visible ciphertext i = true →
      b ciphertext (e ciphertext c) i = a ciphertext c i)
    (sample : (I → Bytes n) × C) :
    conditionedMaskedView visible b obsB
        (dependentProductEquiv (Equiv.refl _) e sample) =
      conditionedMaskedView visible a obsA sample := by
  refine Prod.ext rfl (Prod.ext (observed _ _) ?_)
  funext i
  change (if visible sample.1 i then
      some (xorVector (sample.1 i) (b sample.1 (e sample.1 sample.2) i)) else none) = _
  by_cases hv : visible sample.1 i = true
  · simp only [if_pos hv, visibleEqual _ _ i hv]
  · simp only [if_neg hv]

/-- Artifact-dependent message selection is one fiberwise bijection, not a
union over all possible messages. Concrete use must still prove the visible
plaintext and observation identities for that message. -/
theorem uniform_conditioned_masked_view_transport {C I K : Type} {n : Nat}
    [Finite C] [MeasurableSpace C] [DiscreteMeasurableSpace C] [Fintype I]
    (e : (I → Bytes n) → C ≃ C)
    (a b : (I → Bytes n) → C → I → Bytes n)
    (visible : (I → Bytes n) → I → Bool)
    (obsA obsB : (I → Bytes n) → C → K)
    (observed : ∀ ciphertext c, obsB ciphertext (e ciphertext c) = obsA ciphertext c)
    (visibleEqual : ∀ ciphertext c i, visible ciphertext i = true →
      b ciphertext (e ciphertext c) i = a ciphertext c i)
    (event : Set ((I → Bytes n) × K × (I → Option (Bytes n)))) :
    uniformOn (Set.univ : Set ((I → Bytes n) × C))
      {sample | conditionedMaskedView visible a obsA sample ∈ event} =
    uniformOn (Set.univ : Set ((I → Bytes n) × C))
      {sample | conditionedMaskedView visible b obsB sample ∈ event} := by
  have he : {sample | conditionedMaskedView visible a obsA sample ∈ event} =
      (dependentProductEquiv (Equiv.refl _) e) ⁻¹'
        {sample | conditionedMaskedView visible b obsB sample ∈ event} := by
    ext sample
    simp only [Set.mem_setOf_eq, Set.mem_preimage,
      conditionedMaskedView_transport e a b visible obsA obsB observed visibleEqual]
  rw [he]
  exact Shamir.uniform_event_equiv (dependentProductEquiv (Equiv.refl _) e) _

end WotsLamport.Submission
