import WotsLamport.Submission.ChainPartitionLaw
import WotsLamport.Submission.FieldTableLaw
import WotsLamport.Submission.ProductEventBounds
import WotsLamport.Submission.ActualPolynomialTable

namespace WotsLamport.Submission
open SecretRelease MeasureTheory ProbabilityTheory

local instance (n : Nat) : MeasurableSpace (Fin n) := ⊤

def headTailTableEquiv (n : Nat) (A : Type) : (Fin (n+1) → A) ≃ A × (Fin n → A) where
  toFun table := (table 0, fun i => table i.succ)
  invFun sample := Fin.cases sample.1 sample.2
  left_inv table := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl
  right_inv sample := rfl

def nonceCoefficientEquiv (n : Nat) :
    Bytes ((n+1)*32) ≃ Bytes 32 × (Fin n → Bytes 32) :=
  (byteBlocksEquiv (n+1)).trans (headTailTableEquiv n (Bytes 32))

theorem nonceCoefficientEquiv_nonce (n : Nat) (coins : Bytes ((n+1)*32)) :
    ByteArray.mk (nonceCoefficientEquiv n coins).1.toArray =
      (ByteArray.mk coins.toArray).extract 0 32 := by
  change ByteArray.mk ((byteBlocksEquiv (n+1) coins) 0).toArray = _
  have h := byteBlocks_extract (n+1) coins 0
  simpa only [Fin.val_zero, Nat.zero_mul, Nat.zero_add, Nat.one_mul] using h

theorem nonceCoefficientEquiv_coefficient (coins : Bytes randomnessBytes) (i : Fin coefficientCount) :
    (nonceCoefficientEquiv coefficientCount coins).2 i = coefficientBlock coins i := rfl

def blockFields (n : Nat) (blocks : Fin n → Bytes 32) : Fin n → Fin 65537 :=
  fun i => fieldBlock (blocks i)

theorem blockFields_event_bounds (n : Nat) (event : Set (Fin n → Fin 65537)) :
    uniformOn (Set.univ : Set (Fin n → Bytes 32)) ((blockFields n) ⁻¹' event) ≤
      uniformOn (Set.univ : Set (Fin n → Fin 65537)) event +
        (n : ENNReal)*Sampler.exceptionWeight ∧
    uniformOn (Set.univ : Set (Fin n → Fin 65537)) event ≤
      uniformOn (Set.univ : Set (Fin n → Bytes 32)) ((blockFields n) ⁻¹' event) +
        (n : ENNReal)*Sampler.exceptionWeight := by
  have h := tableFields_event_bounds n event
  have reindex : (tableFields n) ⁻¹' event =
      (byteBlocksEquiv n) ⁻¹' ((blockFields n) ⁻¹' event) := rfl
  rw [reindex, Shamir.uniform_event_equiv] at h
  have ideal : uniformOn (Set.univ : Set (Fin n → Fin 65537)) =
      Measure.pi (fun _ : Fin n => uniformOn (Set.univ : Set (Fin 65537))) := by
    simpa using (uniformOn_pi (f := fun _ : Fin n => (Set.univ : Set (Fin 65537))))
  rwa [← ideal] at h

/-- Reordering retains independent auxiliary randomness while putting the
nonce in the outer environment and all coefficient blocks in the inner one. -/
def nonceCoefficientEnvironmentEquiv (n : Nat) (Ω : Type) :
    (Bytes ((n+1)*32) × Ω) ≃ (Bytes 32 × Ω) × (Fin n → Bytes 32) where
  toFun sample := (((nonceCoefficientEquiv n sample.1).1,sample.2),
    (nonceCoefficientEquiv n sample.1).2)
  invFun sample := ((nonceCoefficientEquiv n).symm (sample.1.1,sample.2),sample.1.2)
  left_inv sample := by simp only [Prod.eta, Equiv.symm_apply_apply]
  right_inv sample := by simp only [Equiv.apply_symm_apply]

/-- The nonce is exactly uniform and independent; only coefficient blocks
contribute a sampling loss. The event may depend jointly on every coordinate. -/
theorem nonceCoefficient_environment_event_bounds {Ω : Type} [Finite Ω] [Nonempty Ω]
    [MeasurableSpace Ω] [DiscreteMeasurableSpace Ω] (n : Nat)
    (event : Set ((Bytes 32 × Ω) × (Fin n → Fin 65537))) :
    uniformOn (Set.univ : Set (Bytes ((n+1)*32) × Ω))
        {sample | (((nonceCoefficientEquiv n sample.1).1,sample.2),
          blockFields n (nonceCoefficientEquiv n sample.1).2) ∈ event} ≤
      uniformOn (Set.univ : Set ((Bytes 32 × Ω) × (Fin n → Fin 65537))) event +
        (n : ENNReal)*Sampler.exceptionWeight ∧
    uniformOn (Set.univ : Set ((Bytes 32 × Ω) × (Fin n → Fin 65537))) event ≤
      uniformOn (Set.univ : Set (Bytes ((n+1)*32) × Ω))
        {sample | (((nonceCoefficientEquiv n sample.1).1,sample.2),
          blockFields n (nonceCoefficientEquiv n sample.1).2) ∈ event} +
          (n : ENNReal)*Sampler.exceptionWeight := by
  classical
  letI := Fintype.ofFinite (Bytes 32)
  let sampled : Set ((Bytes 32 × Ω) × (Fin n → Bytes 32)) :=
    {sample | (sample.1,blockFields n sample.2) ∈ event}
  have reindex :
      {sample : Bytes ((n+1)*32) × Ω |
        (((nonceCoefficientEquiv n sample.1).1,sample.2),
          blockFields n (nonceCoefficientEquiv n sample.1).2) ∈ event} =
      (nonceCoefficientEnvironmentEquiv n Ω) ⁻¹' sampled := rfl
  rw [reindex, Shamir.uniform_event_equiv]
  simp only [uniform_product]
  constructor
  · apply product_event_bound
    intro environment
    exact (blockFields_event_bounds n {fields | (environment,fields) ∈ event}).1
  · apply product_event_bound
    intro environment
    exact (blockFields_event_bounds n {fields | (environment,fields) ∈ event}).2

end WotsLamport.Submission
