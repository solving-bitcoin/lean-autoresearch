import WotsLamport.Submission.AdaptiveFieldGame
import WotsLamport.Submission.NonceCoefficientCoordinates

namespace WotsLamport.Submission
open SecretRelease WotsLamport.Protected MeasureTheory ProbabilityTheory

local instance AdaptiveCoinLaw.finMeasurable (n : Nat) : MeasurableSpace (Fin n) := ⊤

/-- `ZMod 65537` is the same finite carrier; this reindexing uses its values,
not another reduction or an independent coefficient sampling assumption. -/
noncomputable def allocatedFinEquiv : (Fin coefficientCount → Fin 65537) ≃ AllocatedCoefficients :=
  polynomialTableEquiv

theorem actual_allocated_from_blocks (coins : Bytes randomnessBytes) :
    allocatedFinEquiv (blockFields coefficientCount (nonceCoefficientEquiv coefficientCount coins).2) =
      polynomialTableEquiv (actualFieldTable coins) := by
  apply congrArg polynomialTableEquiv
  funext index
  apply Fin.ext
  change (fieldBlock (coefficientBlock coins index)).val =
    (fieldBlock (coefficientBlock coins index)).val % 65537
  exact (Nat.mod_eq_of_lt (fieldBlock (coefficientBlock coins index)).isLt).symm

abbrev AdaptiveAux (inputs : Finset OracleInput) :=
  PublicKey × HiddenChainTape × (Fin 256 → Pair) ×
    ((SharePosition → Bytes 64) × (CommitmentCell → Label)) × (inputs → Label)
abbrev AdaptiveOuter (inputs : Finset OracleInput) :=
  Bytes 32 × ((SharePosition → Bytes 64) × (CommitmentCell → Label)) × (inputs → Label)
abbrev FlatAdaptiveSample (inputs : Finset OracleInput) :=
  (Bytes 32 × AdaptiveAux inputs) × (Fin coefficientCount → Fin 65537)

noncomputable def uniformFieldCoordinates (inputs : Finset OracleInput) :
    FlatAdaptiveSample inputs ≃ AdaptiveOuter inputs × (PublicKey × AfterInnerSample) where
  toFun sample :=
    ((sample.1.1,sample.1.2.2.2.2.1,sample.1.2.2.2.2.2),
      sample.1.2.1,sample.1.2.2.1,sample.1.2.2.2.1,allocatedFinEquiv sample.2)
  invFun sample :=
    ((sample.1.1,(sample.2.1,sample.2.2.1,sample.2.2.2.1,sample.1.2.1,sample.1.2.2)),
      allocatedFinEquiv.symm sample.2.2.2.2)
  left_inv sample := by simp only [Equiv.symm_apply_apply]
  right_inv sample := by simp only [Equiv.apply_symm_apply]

def flatAdaptiveEvent (inputs : Finset OracleInput) (a : AdaptiveAdversary) : Set (FlatAdaptiveSample inputs) :=
  {sample | (sample.1.2.1,sample.1.2.2.1,sample.1.2.2.2.1,allocatedFinEquiv sample.2) ∈
    fieldAdaptiveEvent (ByteArray.mk sample.1.1.toArray) sample.1.2.2.2.2.1
      (ROM.hash (extendOracleTable inputs sample.1.2.2.2.2.2)) a}

def coinAdaptiveEvent (inputs : Finset OracleInput) (a : AdaptiveAdversary) :
    Set (Bytes randomnessBytes × AdaptiveAux inputs) :=
  {sample | (sample.2.1,sample.2.2.1,sample.2.2.2.1,polynomialTableEquiv (actualFieldTable sample.1)) ∈
    fieldAdaptiveEvent ((ByteArray.mk sample.1.toArray).extract 0 32) sample.2.2.2.2.1
      (ROM.hash (extendOracleTable inputs sample.2.2.2.2.2)) a}

theorem uniform_flat_adaptive_bound (inputs : Finset OracleInput) (a : AdaptiveAdversary)
    (q₁ q₂ : Nat) (chooseBound : ROM.Bounded a.choose q₁)
    (finishBound : ∀ state, ROM.Bounded (a.finish state) q₂) :
    uniformOn (Set.univ : Set (FlatAdaptiveSample inputs)) (flatAdaptiveEvent inputs a) ≤
      ((1056 : ENNReal)^2/2^256 + ((512 : ENNReal)/2^256 + (1501 : ENNReal)*q₂/2^256)) +
        (3002 : ENNReal)*q₁/2^256 := by
  classical
  let event : Set (AdaptiveOuter inputs × (PublicKey × AfterInnerSample)) :=
    {sample | sample.2 ∈ fieldAdaptiveEvent (ByteArray.mk sample.1.1.toArray) sample.1.2.1
      (ROM.hash (extendOracleTable inputs sample.1.2.2)) a}
  change uniformOn (Set.univ : Set (FlatAdaptiveSample inputs))
    ((uniformFieldCoordinates inputs) ⁻¹' event) ≤ _
  rw [Shamir.uniform_event_equiv, uniform_product]
  apply product_event_constant_bound
  intro environment
  exact field_adaptive_probability_bound _ _ _ a q₁ q₂ chooseBound finishBound

/-- Actual packed coins, exact nonce and all allocated coefficients. The
single sampler loss applies to the complete adaptive event jointly with every
key, label, ciphertext and finite-oracle coordinate. -/
theorem coin_adaptive_probability_bound (inputs : Finset OracleInput) (a : AdaptiveAdversary)
    (q₁ q₂ : Nat) (chooseBound : ROM.Bounded a.choose q₁)
    (finishBound : ∀ state, ROM.Bounded (a.finish state) q₂) :
    uniformOn (Set.univ : Set (Bytes randomnessBytes × AdaptiveAux inputs)) (coinAdaptiveEvent inputs a) ≤
      (((1056 : ENNReal)^2/2^256 + ((512 : ENNReal)/2^256 + (1501 : ENNReal)*q₂/2^256)) +
        (3002 : ENNReal)*q₁/2^256) + (coefficientCount : ENNReal)*Sampler.exceptionWeight := by
  classical
  have h := (nonceCoefficient_environment_event_bounds
    coefficientCount (flatAdaptiveEvent inputs a)).1
  have actual :
      {sample : Bytes randomnessBytes × AdaptiveAux inputs |
        (((nonceCoefficientEquiv coefficientCount sample.1).1,sample.2),
          blockFields coefficientCount (nonceCoefficientEquiv coefficientCount sample.1).2) ∈
          flatAdaptiveEvent inputs a} = coinAdaptiveEvent inputs a := by
    ext sample
    change ((sample.2.1,sample.2.2.1,sample.2.2.2.1,
        allocatedFinEquiv (blockFields coefficientCount (nonceCoefficientEquiv coefficientCount sample.1).2)) ∈
      fieldAdaptiveEvent (ByteArray.mk (nonceCoefficientEquiv coefficientCount sample.1).1.toArray)
        sample.2.2.2.2.1 (ROM.hash (extendOracleTable inputs sample.2.2.2.2.2)) a) ↔ _
    rw [actual_allocated_from_blocks, nonceCoefficientEquiv_nonce]
    rfl
  rw [actual] at h
  exact h.trans (add_le_add (uniform_flat_adaptive_bound inputs a q₁ q₂ chooseBound finishBound) le_rfl)

end WotsLamport.Submission
