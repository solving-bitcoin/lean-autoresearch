import WotsLamport.Submission.UniformGoodFiber

namespace WotsLamport.Submission
open MeasureTheory

/-- Replace a conditional sampling kernel on the good outer samples. Both
complete output laws are retained, including any oracle table in the output. -/
theorem good_kernel_substitution {T B C Y : Type} [Finite T] [Finite B] [Finite C]
    [MeasurableSpace T] [MeasurableSpace B] [MeasurableSpace C] [MeasurableSpace Y]
    [DiscreteMeasurableSpace T] [DiscreteMeasurableSpace B]
    [DiscreteMeasurableSpace C] [DiscreteMeasurableSpace Y]
    (μ : Measure T) (ν : Measure B) (ρ : Measure C)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [IsProbabilityMeasure ρ]
    (good : Set T) (f : T × B → Y) (g : T × C → Y)
    (same : ∀ t ∈ good, ∀ event : Set Y,
      ν {b | f (t,b) ∈ event} = ρ {c | g (t,c) ∈ event}) :
    ((μ.prod ν).restrict {sample | sample.1 ∈ good}).map f =
      ((μ.prod ρ).restrict {sample | sample.1 ∈ good}).map g := by
  apply Measure.ext
  intro event measurable
  rw [Measure.map_apply Measurable.of_discrete measurable,
    Measure.map_apply Measurable.of_discrete measurable,
    Measure.restrict_apply MeasurableSet.of_discrete,
    Measure.restrict_apply MeasurableSet.of_discrete,
    Measure.prod_apply MeasurableSet.of_discrete,
    Measure.prod_apply MeasurableSet.of_discrete]
  apply lintegral_congr
  intro t
  change ν {b | f (t,b) ∈ event ∧ t ∈ good} = ρ {c | g (t,c) ∈ event ∧ t ∈ good}
  by_cases ht : t ∈ good
  · simpa only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_setOf_eq, ht, and_true]
      using same t ht event
  · simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_setOf_eq, ht, and_false,
      Set.setOf_false, measure_empty]

end WotsLamport.Submission
