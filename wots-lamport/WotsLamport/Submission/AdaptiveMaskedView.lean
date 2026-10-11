import WotsLamport.Submission.MaskedViewLaw

namespace WotsLamport.Submission
open SecretRelease MeasureTheory ProbabilityTheory

/-- Reexpress independent coefficients and pads as ciphertexts and
coefficients. XOR cancellation supplies both inverse laws. -/
def ciphertextCoordinateEquiv {C I : Type} {n : Nat} (plain : C → I → Bytes n) :
    C × (I → Bytes n) ≃ (I → Bytes n) × C where
  toFun sample := (ciphertextTable plain sample, sample.1)
  invFun sample := (sample.2, fun i => xorVector (sample.1 i) (plain sample.2 i))
  left_inv sample := by
    apply Prod.ext rfl
    funext i
    exact xorVector_cancel _ _
  right_inv sample := by
    apply Prod.ext _ rfl
    funext i
    exact xorVector_cancel _ _

/-- The coefficient bijection may depend on the complete ciphertext table.
Using ciphertext coordinates makes this dependence triangular and invertible. -/
def adaptiveSharingPadEquiv {C I : Type} {n : Nat}
    (e : (I → Bytes n) → C ≃ C) (a b : C → I → Bytes n) :
    C × (I → Bytes n) ≃ C × (I → Bytes n) :=
  (ciphertextCoordinateEquiv a).trans
    ((dependentProductEquiv (Equiv.refl _) e).trans (ciphertextCoordinateEquiv b).symm)

theorem adaptiveSharingPadEquiv_coefficient {C I : Type} {n : Nat}
    (e : (I → Bytes n) → C ≃ C) (a b : C → I → Bytes n)
    (sample : C × (I → Bytes n)) :
    (adaptiveSharingPadEquiv e a b sample).1 = e (ciphertextTable a sample) sample.1 := rfl

theorem adaptiveSharingPadEquiv_ciphertext {C I : Type} {n : Nat}
    (e : (I → Bytes n) → C ≃ C) (a b : C → I → Bytes n)
    (sample : C × (I → Bytes n)) :
    ciphertextTable b (adaptiveSharingPadEquiv e a b sample) = ciphertextTable a sample := by
  funext i
  exact xorVector_cancel _ _

/-- Visibility and observations can be chosen from the artifact ciphertexts.
An adversary's fixed independent environment can be a further parameter. -/
def adaptiveMaskedView {C I K : Type} {n : Nat}
    (visible : (I → Bytes n) → I → Bool) (plain : C → I → Bytes n)
    (observation : (I → Bytes n) → C → K) (sample : C × (I → Bytes n)) :
    (I → Bytes n) × K × (I → Option (Bytes n)) :=
  let ciphertext := ciphertextTable plain sample
  (ciphertext, observation ciphertext sample.1,
    fun i => if visible ciphertext i then some (sample.2 i) else none)

theorem adaptiveSharingPadEquiv_view {C I K : Type} {n : Nat}
    (e : (I → Bytes n) → C ≃ C) (a b : C → I → Bytes n)
    (visible : (I → Bytes n) → I → Bool) (obsA obsB : (I → Bytes n) → C → K)
    (observed : ∀ ciphertext c, obsB ciphertext (e ciphertext c) = obsA ciphertext c)
    (visibleEqual : ∀ ciphertext c i, visible ciphertext i = true →
      b (e ciphertext c) i = a c i)
    (sample : C × (I → Bytes n)) :
    adaptiveMaskedView visible b obsB (adaptiveSharingPadEquiv e a b sample) =
      adaptiveMaskedView visible a obsA sample := by
  simp only [adaptiveMaskedView, adaptiveSharingPadEquiv_ciphertext,
    adaptiveSharingPadEquiv_coefficient]
  apply Prod.ext rfl
  apply Prod.ext (observed _ _)
  funext i
  by_cases hv : visible (ciphertextTable a sample) i = true
  · simp only [if_pos hv]
    apply congrArg some
    change xorVector (ciphertextTable a sample i)
      (b (e (ciphertextTable a sample) sample.1) i) = sample.2 i
    rw [visibleEqual _ _ i hv]
    exact xorVector_cancel _ _
  · simp only [if_neg hv]

/-- A single product-space bijection handles artifact-dependent visibility.
There is no union bound over message choices and no assumption that actual
oracle outputs already have this independent-pad distribution. -/
theorem uniform_adaptive_masked_view_transport {C I K : Type} {n : Nat}
    [Finite C] [MeasurableSpace C] [DiscreteMeasurableSpace C] [Fintype I]
    (e : (I → Bytes n) → C ≃ C) (a b : C → I → Bytes n)
    (visible : (I → Bytes n) → I → Bool) (obsA obsB : (I → Bytes n) → C → K)
    (observed : ∀ ciphertext c, obsB ciphertext (e ciphertext c) = obsA ciphertext c)
    (visibleEqual : ∀ ciphertext c i, visible ciphertext i = true →
      b (e ciphertext c) i = a c i)
    (event : Set ((I → Bytes n) × K × (I → Option (Bytes n)))) :
    uniformOn (Set.univ : Set (C × (I → Bytes n)))
      {sample | adaptiveMaskedView visible a obsA sample ∈ event} =
    uniformOn (Set.univ : Set (C × (I → Bytes n)))
      {sample | adaptiveMaskedView visible b obsB sample ∈ event} := by
  have he : {sample | adaptiveMaskedView visible a obsA sample ∈ event} =
      (adaptiveSharingPadEquiv e a b) ⁻¹'
        {sample | adaptiveMaskedView visible b obsB sample ∈ event} := by
    ext sample
    simp only [Set.mem_setOf_eq, Set.mem_preimage,
      adaptiveSharingPadEquiv_view e a b visible obsA obsB observed visibleEqual]
  rw [he]
  exact Shamir.uniform_event_equiv (adaptiveSharingPadEquiv e a b) _

end WotsLamport.Submission
