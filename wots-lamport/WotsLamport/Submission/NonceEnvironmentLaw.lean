import WotsLamport.Submission.NonceTableLaw

namespace WotsLamport.Submission
open SecretRelease MeasureTheory ProbabilityTheory

/-- A shared coefficient submeasure remains shared after adjoining arbitrary
independent randomness, including the infinite random oracle. -/
theorem product_lower_domination {A B : Type} [MeasurableSpace A] [MeasurableSpace B]
    (μ ν : Measure A) (ρ : Measure B) [SFinite ρ]
    (weight : ENNReal) (lower : weight • ν ≤ μ) :
    weight • (ν.prod ρ) ≤ μ.prod ρ := by
  rw [← Measure.prod_smul_left]
  exact Measure.prod_mono lower le_rfl

theorem product_probability_event_bounds {A B : Type}
    [MeasurableSpace A] [MeasurableSpace B]
    (μ ν : Measure A) (ρ : Measure B)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [IsProbabilityMeasure ρ]
    (weight loss : ENNReal) (lower : weight • ν ≤ μ) (cover : 1 ≤ weight+loss)
    (event : Set (A × B)) (measurable : MeasurableSet event) :
    (μ.prod ρ) event ≤ (ν.prod ρ) event+loss ∧
      (ν.prod ρ) event ≤ (μ.prod ρ) event+loss :=
  probability_event_bounds (μ.prod ρ) (ν.prod ρ) weight loss
    (product_lower_domination μ ν ρ weight lower) cover event measurable

local instance NonceEnvironmentLaw.finMeasurable (n : Nat) : MeasurableSpace (Fin n) := ⊤
local instance NonceEnvironmentLaw.nonceBlockMeasurable : MeasurableSpace (Bytes 32 ⊕ Fin 65537) := ⊤

/-- The complete nonce/coefficient sampling error applies to joint events
with all independently sampled keys, labels and oracle randomness. There is
no assumption that the event itself factors into independent events. -/
theorem nonceFieldTable_environment_event_bounds {Ω : Type} [MeasurableSpace Ω]
    (n : Nat) (ρ : Measure Ω) [IsProbabilityMeasure ρ]
    (event : Set ((Fin (n+1) → Bytes 32 ⊕ Fin 65537) × Ω))
    (measurable : MeasurableSet event) :
    (((uniformOn (Set.univ : Set (Bytes ((n+1)*32)))).map (nonceFieldTable n)).prod ρ) event ≤
        ((Measure.pi (fun index : Fin (n+1) => idealNonceFieldLaw index)).prod ρ) event +
          ((n+1 : Nat) : ENNReal)*Sampler.exceptionWeight ∧
    ((Measure.pi (fun index : Fin (n+1) => idealNonceFieldLaw index)).prod ρ) event ≤
        (((uniformOn (Set.univ : Set (Bytes ((n+1)*32)))).map (nonceFieldTable n)).prod ρ) event +
          ((n+1 : Nat) : ENNReal)*Sampler.exceptionWeight := by
  classical
  letI := Fintype.ofFinite (Bytes 32 ⊕ Fin 65537)
  rw [nonceFieldTable_law]
  exact product_probability_event_bounds _ _ ρ (Sampler.ordinaryWeight^(n+1))
    (((n+1 : Nat) : ENNReal)*Sampler.exceptionWeight)
    (finite_family_domination (n+1) _ _ Sampler.ordinaryWeight nonceFieldLaw_lower)
    (bernoulli_mixture_bound _ _ Sampler.mixture_weights (n+1)) event measurable

end WotsLamport.Submission
