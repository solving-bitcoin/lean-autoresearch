import WotsLamport.Submission.SamplerMixture
import WotsLamport.Submission.CoinBlocks

namespace WotsLamport.Submission
open MeasureTheory ProbabilityTheory

/-- Lower domination tensorizes over a finite sample space. -/
theorem finite_family_domination {A : Type} [Fintype A] [MeasurableSpace A]
    [MeasurableSingletonClass A] (n : Nat) (μ ν : Fin n → Measure A)
    [∀ j, IsProbabilityMeasure (μ j)] [∀ j, IsProbabilityMeasure (ν j)]
    (weight : ENNReal) (lower : ∀ j, weight • ν j ≤ μ j) :
    weight^n • Measure.pi ν ≤ Measure.pi μ := by
  classical
  intro event
  lift event to Finset (Fin n → A) using Set.toFinite event
  rw [← sum_measure_singleton (μ := weight^n • Measure.pi ν) (s := event),
    ← sum_measure_singleton (μ := Measure.pi μ) (s := event)]
  apply Finset.sum_le_sum
  intro x _
  simp only [Measure.smul_apply, smul_eq_mul, Measure.pi_singleton]
  calc
    weight^n * (∏ j : Fin n, ν j {x j}) = ∏ j : Fin n, weight * ν j {x j} := by
      simp [Finset.prod_mul_distrib]
    _ ≤ ∏ j : Fin n, μ j {x j} := Finset.prod_le_prod' (fun j _ => by
      simpa only [Measure.smul_apply, smul_eq_mul] using lower j {x j})

/-- Lower domination tensorizes over a finite sample space. -/
theorem finite_product_domination {A : Type} [Fintype A] [MeasurableSpace A]
    [MeasurableSingletonClass A] (μ ν : Measure A)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (weight : ENNReal) (lower : weight • ν ≤ μ) (n : Nat) :
    weight^n • Measure.pi (fun _ : Fin n => ν) ≤ Measure.pi (fun _ : Fin n => μ) := by
  classical
  intro event
  lift event to Finset (Fin n → A) using Set.toFinite event
  rw [← sum_measure_singleton (μ := weight^n • Measure.pi (fun _ : Fin n => ν)) (s := event),
    ← sum_measure_singleton (μ := Measure.pi (fun _ : Fin n => μ)) (s := event)]
  apply Finset.sum_le_sum
  intro x _
  simp only [Measure.smul_apply, smul_eq_mul, Measure.pi_singleton]
  calc
    weight^n * (∏ j : Fin n, ν {x j}) = ∏ j : Fin n, weight * ν {x j} := by
      simp [Finset.prod_mul_distrib]
    _ ≤ ∏ j : Fin n, μ {x j} := Finset.prod_le_prod' (fun j _ => by
      simpa only [Measure.smul_apply, smul_eq_mul] using lower {x j})

theorem bernoulli_mixture_bound (ordinary exceptional : ENNReal)
    (weights : ordinary+exceptional = 1) (n : Nat) :
    1 ≤ ordinary^n + (n : ENNReal)*exceptional := by
  have ho : ordinary ≤ 1 := (le_add_right le_rfl).trans_eq weights
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      1 = ordinary+exceptional := weights.symm
      _ ≤ ordinary*(ordinary^n+(n : ENNReal)*exceptional)+exceptional :=
        Sampler.add_right_mono (by simpa only [mul_one] using Sampler.mul_left_mono ih ordinary) _
      _ = ordinary^(n+1)+ordinary*((n : ENNReal)*exceptional)+exceptional := by
        rw [pow_succ]
        ring
      _ ≤ ordinary^(n+1)+(n : ENNReal)*exceptional+exceptional :=
        Sampler.add_right_mono (Sampler.add_left_mono
          ((Sampler.mul_right_mono ho _).trans_eq (one_mul _)) _) _
      _ = ordinary^(n+1)+((n+1 : Nat) : ENNReal)*exceptional := by
        rw [Nat.cast_add, Nat.cast_one]
        ring

/-- A shared probability submeasure yields two-sided event bounds. -/
theorem probability_event_bounds {A : Type} [MeasurableSpace A]
    (μ ν : Measure A) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (weight loss : ENNReal) (lower : weight • ν ≤ μ) (cover : 1 ≤ weight+loss)
    (event : Set A) (measurable : MeasurableSet event) :
    μ event ≤ ν event+loss ∧ ν event ≤ μ event+loss := by
  have hunit (s : Set A) : ν s ≤ 1 := by
    simpa using measure_mono (μ := ν) (Set.subset_univ s)
  have hlow (s : Set A) : weight*ν s ≤ μ s := by
    simpa only [Measure.smul_apply, smul_eq_mul] using lower s
  constructor
  · have hfinite : weight*ν eventᶜ ≠ ⊤ :=
      (lt_of_le_of_lt (hlow eventᶜ) (measure_lt_top μ eventᶜ)).ne
    apply ENNReal.le_of_Sampler.add_left_mono hfinite
    calc
      weight*ν eventᶜ+μ event ≤ μ eventᶜ+μ event := Sampler.add_right_mono (hlow eventᶜ) _
      _ = 1 := by rw [add_comm, prob_add_prob_compl measurable]
      _ = ν event+ν eventᶜ := (prob_add_prob_compl measurable).symm
      _ ≤ ν event+(weight+loss)*ν eventᶜ :=
        Sampler.add_left_mono (by simpa only [one_mul] using Sampler.mul_right_mono cover (ν eventᶜ)) _
      _ = weight*ν eventᶜ+(ν event+loss*ν eventᶜ) := by ring
      _ ≤ weight*ν eventᶜ+(ν event+loss) := Sampler.add_left_mono
        (Sampler.add_left_mono ((Sampler.mul_left_mono (hunit eventᶜ) loss).trans_eq (mul_one _)) _) _
  · calc
      ν event ≤ (weight+loss)*ν event := by
        simpa only [one_mul] using Sampler.mul_right_mono cover (ν event)
      _ = weight*ν event+loss*ν event := add_mul _ _ _
      _ ≤ μ event+loss := add_le_add (hlow event)
        ((Sampler.mul_left_mono (hunit event) loss).trans_eq (mul_one _))

namespace Sampler
local instance (n : Nat) : MeasurableSpace (Fin n) := ⊤

noncomputable def fieldLaw : Measure (Fin 65537) :=
  (uniformOn (Set.univ : Set (Fin sampleSize))).map reduceInteger

instance : IsProbabilityMeasure fieldLaw :=
  Measure.isProbabilityMeasure_map Measurable.of_discrete.aemeasurable

/-- All coordinates are handled jointly. The loss is at most n/2^256 for
every event in the complete field table, in both directions. -/
theorem joint_field_event_bounds (n : Nat) (event : Set (Fin n → Fin 65537)) :
    (Measure.pi (fun _ : Fin n => fieldLaw)) event ≤
        (Measure.pi (fun _ : Fin n => uniformOn (Set.univ : Set (Fin 65537)))) event +
          (n : ENNReal)*exceptionWeight ∧
    (Measure.pi (fun _ : Fin n => uniformOn (Set.univ : Set (Fin 65537)))) event ≤
        (Measure.pi (fun _ : Fin n => fieldLaw)) event + (n : ENNReal)*exceptionWeight := by
  have hscalar : ordinaryWeight • uniformOn (Set.univ : Set (Fin 65537)) ≤ fieldLaw := by
    rw [fieldLaw, reduced_integer_mixture]
    exact le_add_right le_rfl
  exact probability_event_bounds _ _ (ordinaryWeight^n) ((n : ENNReal)*exceptionWeight)
    (finite_product_domination _ _ ordinaryWeight hscalar n)
    (bernoulli_mixture_bound ordinaryWeight exceptionWeight mixture_weights n)
    event MeasurableSet.of_discrete

theorem allocated_joint_loss :
    (coefficientCount : ENNReal)*exceptionWeight < 1/(2 : ENNReal)^233 := by
  norm_num [coefficientCount, exceptionWeight, sampleSize] <;>
    apply (ENNReal.toReal_lt_toReal (by finiteness) (by finiteness)).mp <;> norm_num

end Sampler
end WotsLamport.Submission
