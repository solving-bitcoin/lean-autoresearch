import WotsLamport.Submission.UniformGoodFiber

namespace WotsLamport.Submission
open MeasureTheory

theorem event_bound_of_agree_on_good {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) (a b good : Set Ω) (agrees : ∀ x ∈ good, x ∈ a ↔ x ∈ b) :
    μ a ≤ μ b + μ goodᶜ := by
  classical
  have subset : a ⊆ b ∪ goodᶜ := by
    intro x hx
    by_cases hg : x ∈ good
    · exact Or.inl ((agrees x hg).mp hx)
    · exact Or.inr hg
  exact (measure_mono subset).trans (measure_union_le _ _)

/-- Pointwise comparison of conditional output events integrates to the full
joint event without assuming that the event factors into independent pieces. -/
theorem product_event_bound {T A B : Type} [Finite T] [Finite A] [Finite B]
    [MeasurableSpace T] [MeasurableSpace A] [MeasurableSpace B]
    [DiscreteMeasurableSpace T] [DiscreteMeasurableSpace A] [DiscreteMeasurableSpace B]
    (μ : Measure T) (ν : Measure A) (ρ : Measure B)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [IsProbabilityMeasure ρ]
    (a : Set (T × A)) (b : Set (T × B)) (loss : ENNReal)
    (bound : ∀ t, ν {x | (t,x) ∈ a} ≤ ρ {y | (t,y) ∈ b} + loss) :
    (μ.prod ν) a ≤ (μ.prod ρ) b + loss := by
  rw [Measure.prod_apply MeasurableSet.of_discrete,
    Measure.prod_apply MeasurableSet.of_discrete]
  change (∫⁻ t, ν {x | (t,x) ∈ a} ∂μ) ≤ (∫⁻ t, ρ {y | (t,y) ∈ b} ∂μ) + loss
  calc
    _ ≤ ∫⁻ t, ρ {y | (t,y) ∈ b} + loss ∂μ := lintegral_mono bound
    _ = _ := by rw [lintegral_add_left Measurable.of_discrete]; simp

theorem product_event_constant_bound {T A : Type} [Finite T] [Finite A]
    [MeasurableSpace T] [MeasurableSpace A]
    [DiscreteMeasurableSpace T] [DiscreteMeasurableSpace A]
    (μ : Measure T) (ν : Measure A) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (event : Set (T × A)) (bound : ENNReal)
    (fibers : ∀ t, ν {x | (t,x) ∈ event} ≤ bound) :
    (μ.prod ν) event ≤ bound := by
  rw [Measure.prod_apply MeasurableSet.of_discrete]
  calc
    _ ≤ ∫⁻ _ : T, bound ∂μ := lintegral_mono fibers
    _ = bound := by simp

end WotsLamport.Submission
