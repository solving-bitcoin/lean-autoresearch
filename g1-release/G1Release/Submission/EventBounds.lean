import G1Release.Submission.FiniteProbability

namespace G1Release.Submission.EventBounds
open MeasureTheory

def Le {α : Type*} [MeasurableSpace α] (μ ν : Measure α) (error : ENNReal) : Prop :=
  ∀ event, MeasurableSet event → μ event ≤ ν event + error

theorem of_toReal {α : Type*} [MeasurableSpace α] (μ ν : Measure α)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (error : ℝ) (he : 0 ≤ error)
    (h : ∀ event, MeasurableSet event → (μ event).toReal ≤ (ν event).toReal + error) :
    Le μ ν (ENNReal.ofReal error) := by
  intro event hm
  apply (ENNReal.toReal_le_toReal (measure_ne_top _ _)
    (ENNReal.add_ne_top.mpr ⟨measure_ne_top _ _, ENNReal.ofReal_ne_top⟩)).mp
  rw [ENNReal.toReal_add (measure_ne_top _ _) ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal he]
  exact h event hm

theorem map {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ ν : Measure α} {error : ENNReal} (h : Le μ ν error)
    (f : α → β) (hf : Measurable f) : Le (μ.map f) (ν.map f) error := by
  intro event hm
  rw [Measure.map_apply hf hm, Measure.map_apply hf hm]
  exact h (f ⁻¹' event) (hf hm)

/-- An independent common context preserves the event-distance bound. -/
theorem prod_right {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ ν : Measure α} [SFinite μ] [SFinite ν] {error : ENNReal} (h : Le μ ν error)
    (context : Measure β) [IsProbabilityMeasure context] :
    Le (μ.prod context) (ν.prod context) error := by
  intro event hm
  rw [Measure.prod_apply_symm hm, Measure.prod_apply_symm hm]
  calc
    (∫⁻ b, μ ((fun a => (a,b)) ⁻¹' event) ∂context) ≤
        ∫⁻ b, ν ((fun a => (a,b)) ⁻¹' event) + error ∂context := by
      apply lintegral_mono
      intro b
      exact h _ (measurable_prodMk_right hm)
    _ = (∫⁻ b, ν ((fun a => (a,b)) ⁻¹' event) ∂context) + error := by
      rw [lintegral_add_right _ measurable_const]
      simp

theorem prod_left {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ ν : Measure β} [SFinite μ] [SFinite ν] {error : ENNReal} (h : Le μ ν error)
    (context : Measure α) [IsProbabilityMeasure context] :
    Le (context.prod μ) (context.prod ν) error := by
  have ht := map (prod_right h context) Prod.swap measurable_swap
  simpa only [Measure.prod_swap] using ht

theorem trans {α : Type*} [MeasurableSpace α] {μ ν ξ : Measure α} {e₀ e₁ : ENNReal}
    (h₀ : Le μ ν e₀) (h₁ : Le ν ξ e₁) : Le μ ξ (e₀+e₁) := by
  intro event hm
  calc
    μ event ≤ ν event + e₀ := h₀ event hm
    _ ≤ (ξ event + e₁) + e₀ := add_le_add (h₁ event hm) le_rfl
    _ = ξ event + (e₀+e₁) := by ac_rfl

theorem event_le_add_bad {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (left right bad : Set α) (h : ∀ x ∈ left, x ∉ bad → x ∈ right) :
    μ left ≤ μ right + μ bad := by
  apply (measure_mono (show left ⊆ right ∪ bad from ?_)).trans (measure_union_le _ _)
  intro x hx
  by_cases hb : x ∈ bad
  · exact Or.inr hb
  · exact Or.inl (h x hx hb)

end G1Release.Submission.EventBounds
