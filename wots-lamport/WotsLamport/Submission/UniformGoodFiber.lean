import WotsLamport.Submission.FiniteOracleLaw

namespace WotsLamport.Submission
open MeasureTheory ProbabilityTheory

theorem uniform_set_mass {X : Type} [Fintype X] [MeasurableSpace X]
    [DiscreteMeasurableSpace X] (s : Set X) :
    uniformOn (Set.univ : Set X) s = (Nat.card s : ENNReal) / Fintype.card X := by
  classical
  rw [uniformOn_univ, Measure.count_apply MeasurableSet.of_discrete,
    Set.encard, ENat.card_eq_coe_fintype_card, Nat.card_eq_fintype_card]

/-- Counting a joint programming map on its good samples gives equality of
restricted laws, provided the fiber count and sample-space ratio are proved.
The hypotheses remain explicit: this generic statement is not the actual
chain/mask/commitment distribution theorem. -/
theorem uniform_good_fiber_law {X Y : Type} [Fintype X] [Fintype Y]
    [MeasurableSpace X] [MeasurableSpace Y]
    [DiscreteMeasurableSpace X] [DiscreteMeasurableSpace Y]
    (f : X → Y) (goodX : Set X) (goodY : Set Y) (k : Nat) (hk : k ≠ 0)
    (stays : ∀ x ∈ goodX, f x ∈ goodY)
    (fibers : ∀ y ∈ goodY, Nat.card {x : X // x ∈ goodX ∧ f x = y} = k)
    (ratio : Fintype.card X = k * Fintype.card Y) :
    ((uniformOn (Set.univ : Set X)).restrict goodX).map f =
      (uniformOn (Set.univ : Set Y)).restrict goodY := by
  classical
  apply Measure.ext_of_singleton
  intro y
  rw [Measure.map_apply Measurable.of_discrete (measurableSet_singleton y)]
  simp only [Measure.restrict_apply MeasurableSet.of_discrete]
  have hpre : f ⁻¹' {y} ∩ goodX = {x | x ∈ goodX ∧ f x = y} := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq]
    exact and_comm
  rw [hpre]
  by_cases hy : y ∈ goodY
  · have hout : ({y} ∩ goodY : Set Y) = {y} := by
      ext z
      simp only [Set.mem_inter_iff, Set.mem_singleton_iff]
      constructor
      · exact And.left
      · rintro rfl
        exact ⟨rfl,hy⟩
    rw [hout, uniform_set_mass, fibers y hy, ratio, Nat.cast_mul,
      uniformOn_univ, Measure.count_singleton]
    simpa only [mul_one] using ENNReal.mul_div_mul_left 1 (Fintype.card Y : ENNReal)
      (c := (k : ENNReal)) (by exact_mod_cast hk) (by simp)
  · have hin : {x : X | x ∈ goodX ∧ f x = y} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro x ⟨hx,he⟩
      exact hy (he ▸ stays x hx)
    have hout : ({y} ∩ goodY : Set Y) = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro z ⟨hz,hzgood⟩
      have he : z = y := hz
      exact hy (he ▸ hzgood)
    rw [hin,hout]
    simp

/-- Equality of the good submeasures bounds both directions of every event
comparison by the ideal bad mass. No independence of the event is assumed. -/
theorem good_law_event_bounds {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y]
    [DiscreteMeasurableSpace X] [DiscreteMeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (f : X → Y) (goodX : Set X) (goodY : Set Y)
    (law : (μ.restrict goodX).map f = ν.restrict goodY) (event : Set Y) :
    μ (f ⁻¹' event) ≤ ν event + μ goodXᶜ ∧
      ν event ≤ μ (f ⁻¹' event) + μ goodXᶜ := by
  classical
  have good (s : Set Y) : μ (f ⁻¹' s ∩ goodX) = ν (s ∩ goodY) := by
    have he := congrArg (fun ρ : Measure Y => ρ s) law
    simpa only [Measure.map_apply Measurable.of_discrete MeasurableSet.of_discrete,
      Measure.restrict_apply MeasurableSet.of_discrete] using he
  have sameGood : μ goodX = ν goodY := by simpa using good Set.univ
  have sameBad : μ goodXᶜ = ν goodYᶜ := by
    rw [prob_compl_eq_one_sub MeasurableSet.of_discrete,
      prob_compl_eq_one_sub MeasurableSet.of_discrete, sameGood]
  have splitBound {A : Type} [MeasurableSpace A] (ρ : Measure A) (s g : Set A) :
      ρ s ≤ ρ (s ∩ g) + ρ gᶜ := by
    have hs : s ⊆ (s ∩ g) ∪ gᶜ := by
      intro x hx
      by_cases hg : x ∈ g
      · exact Or.inl ⟨hx,hg⟩
      · exact Or.inr hg
    exact (measure_mono hs).trans (measure_union_le _ _)
  constructor
  · calc
      μ (f ⁻¹' event) ≤ μ (f ⁻¹' event ∩ goodX) + μ goodXᶜ := splitBound μ _ _
      _ = ν (event ∩ goodY) + μ goodXᶜ := by rw [good]
      _ ≤ ν event + μ goodXᶜ := add_le_add_right (measure_mono Set.inter_subset_left) _
  · calc
      ν event ≤ ν (event ∩ goodY) + ν goodYᶜ := splitBound ν _ _
      _ = μ (f ⁻¹' event ∩ goodX) + μ goodXᶜ := by rw [← good, ← sameBad]
      _ ≤ μ (f ⁻¹' event) + μ goodXᶜ := add_le_add_right (measure_mono Set.inter_subset_left) _

end WotsLamport.Submission
