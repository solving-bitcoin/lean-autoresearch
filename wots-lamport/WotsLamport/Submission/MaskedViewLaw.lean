import WotsLamport.Submission.MaskLaw

namespace WotsLamport.Submission
open SecretRelease MeasureTheory ProbabilityTheory

/-- A triangular bijection: first change the coefficient sample, then change
its pad table by a sample-dependent bijection. -/
def dependentProductEquiv {C P : Type} (e : C ≃ C) (pads : C → P ≃ P) : C × P ≃ C × P where
  toFun sample := (e sample.1, pads sample.1 sample.2)
  invFun sample := (e.symm sample.1, (pads (e.symm sample.1)).symm sample.2)
  left_inv sample := by rcases sample with ⟨c,p⟩; simp
  right_inv sample := by rcases sample with ⟨c,p⟩; simp

def ciphertextTable {C I : Type} {n : Nat} (plain : C → I → Bytes n)
    (sample : C × (I → Bytes n)) : I → Bytes n :=
  fun i => xorVector (sample.2 i) (plain sample.1 i)

def maskedView {C I K : Type} {n : Nat} (visible : Set I)
    (plain : C → I → Bytes n) (observation : C → K)
    (sample : C × (I → Bytes n)) : K × (I → Bytes n) × (visible → Bytes n) :=
  (observation sample.1, ciphertextTable plain sample, fun i => sample.2 i.val)

def sharingPadEquiv {C I : Type} {n : Nat} (e : C ≃ C)
    (a b : C → I → Bytes n) : C × (I → Bytes n) ≃ C × (I → Bytes n) :=
  dependentProductEquiv e fun c => Equiv.piCongrRight fun i =>
    (xorVectorEquiv (a c i)).trans (xorVectorEquiv (b (e c) i))

theorem sharingPadEquiv_ciphertext {C I : Type} {n : Nat} (e : C ≃ C)
    (a b : C → I → Bytes n) (sample : C × (I → Bytes n)) :
    ciphertextTable b (sharingPadEquiv e a b sample) = ciphertextTable a sample := by
  funext i
  change xorVector (xorVector (xorVector (sample.2 i) (a sample.1 i))
    (b (e sample.1) i)) (b (e sample.1) i) = _
  exact xorVector_cancel _ _

theorem sharingPadEquiv_view {C I K : Type} {n : Nat} (e : C ≃ C)
    (a b : C → I → Bytes n) (visible : Set I) (obsA obsB : C → K)
    (observed : ∀ c, obsB (e c) = obsA c)
    (visibleEqual : ∀ c i, i ∈ visible → b (e c) i = a c i)
    (sample : C × (I → Bytes n)) :
    maskedView visible b obsB (sharingPadEquiv e a b sample) =
      maskedView visible a obsA sample := by
  apply Prod.ext (observed sample.1)
  apply Prod.ext (sharingPadEquiv_ciphertext e a b sample)
  funext i
  change xorVector (xorVector (sample.2 i.val) (a sample.1 i.val))
    (b (e sample.1) i.val) = sample.2 i.val
  rw [visibleEqual sample.1 i.val i.property]
  exact xorVector_cancel _ _

/-- Joint privacy of ciphertexts, all exposed pads and any preserved
coefficient observations. The hypotheses concern a concrete coefficient
bijection; they do not assert that actual oracle outputs are independent pads. -/
theorem uniform_masked_view_transport {C I K : Type} {n : Nat}
    [Finite C] [MeasurableSpace C] [DiscreteMeasurableSpace C] [Fintype I]
    (e : C ≃ C) (a b : C → I → Bytes n) (visible : Set I) (obsA obsB : C → K)
    (observed : ∀ c, obsB (e c) = obsA c)
    (visibleEqual : ∀ c i, i ∈ visible → b (e c) i = a c i)
    (event : Set (K × (I → Bytes n) × (visible → Bytes n))) :
    uniformOn (Set.univ : Set (C × (I → Bytes n)))
      {sample | maskedView visible a obsA sample ∈ event} =
    uniformOn (Set.univ : Set (C × (I → Bytes n)))
      {sample | maskedView visible b obsB sample ∈ event} := by
  have he : {sample | maskedView visible a obsA sample ∈ event} =
      (sharingPadEquiv e a b) ⁻¹' {sample | maskedView visible b obsB sample ∈ event} := by
    ext sample
    simp only [Set.mem_setOf_eq, Set.mem_preimage,
      sharingPadEquiv_view e a b visible obsA obsB observed visibleEqual]
  rw [he]
  exact Shamir.uniform_event_equiv (sharingPadEquiv e a b) _

end WotsLamport.Submission
