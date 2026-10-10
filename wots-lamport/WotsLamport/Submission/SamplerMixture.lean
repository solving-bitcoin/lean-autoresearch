import WotsLamport.Submission.SamplerLaw

namespace WotsLamport.Submission.Sampler
open MeasureTheory ProbabilityTheory

local instance (n : Nat) : MeasurableSpace (Fin n) := ⊤

def reduceInteger (n : Fin sampleSize) : Fin 65537 := ⟨n.val % 65537, Nat.mod_lt _ (by decide)⟩

noncomputable def exceptionWeight : ENNReal := 1 / (sampleSize : ENNReal)
noncomputable def ordinaryWeight : ENNReal := ((sampleSize-1 : Nat) : ENNReal) / sampleSize

/-- The exact reduced-integer law is a mixture: an ordinary uniform field
sample with weight 1-2^-256 and one exceptional zero with weight 2^-256.
This supplies an explicit coupling interpretation of the modular bias. -/
theorem reduced_integer_mixture :
    (uniformOn (Set.univ : Set (Fin sampleSize))).map reduceInteger =
      ordinaryWeight • uniformOn (Set.univ : Set (Fin 65537)) +
        exceptionWeight • Measure.dirac (0 : Fin 65537) := by
  apply Measure.ext_of_singleton
  intro r
  rw [Measure.map_apply measurable_of_discrete (measurableSet_singleton r)]
  have hs : reduceInteger ⁻¹' {r} = {n : Fin sampleSize | n.val % 65537 = r.val} := by
    ext n
    simp [reduceInteger, Fin.ext_iff]
  rw [hs, residue_probability]
  simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul,
    uniformOn_univ, Measure.count_singleton, Fintype.card_fin]
  by_cases hz : r = 0
  · subst r
    norm_num [residueCount, quotient, sampleSize, ordinaryWeight, exceptionWeight]
  · have hv : r.val ≠ 0 := fun h => hz (Fin.ext h)
    norm_num [residueCount, quotient, sampleSize, ordinaryWeight, exceptionWeight,
      Measure.dirac_apply, hz, hv, Ne.symm hz]

theorem mixture_weights : ordinaryWeight + exceptionWeight = 1 := by
  norm_num [ordinaryWeight, exceptionWeight, sampleSize]

theorem ordinaryWeight_le_one : ordinaryWeight ≤ 1 := by
  norm_num [ordinaryWeight, sampleSize]

/-- Every measurable event differs from its uniform probability by at most
one exceptional sample. Both directions are available for later hybrids. -/
theorem reduced_integer_event_bound (event : Set (Fin 65537)) :
    ((uniformOn (Set.univ : Set (Fin sampleSize))).map reduceInteger) event ≤
      uniformOn (Set.univ : Set (Fin 65537)) event + exceptionWeight := by
  rw [reduced_integer_mixture]
  simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul]
  apply add_le_add
  · exact (mul_le_mul_right' ordinaryWeight_le_one _).trans_eq (one_mul _)
  · have hd : (Measure.dirac (0 : Fin 65537)) event ≤ 1 := by
      simpa using measure_mono (μ := Measure.dirac (0 : Fin 65537)) (Set.subset_univ event)
    exact (mul_le_mul_left' hd _).trans_eq (mul_one _)

theorem uniform_event_bound (event : Set (Fin 65537)) :
    uniformOn (Set.univ : Set (Fin 65537)) event ≤
      ((uniformOn (Set.univ : Set (Fin sampleSize))).map reduceInteger) event + exceptionWeight := by
  let u := uniformOn (Set.univ : Set (Fin 65537)) event
  have hu : u ≤ 1 := by
    simpa [u] using measure_mono (μ := uniformOn (Set.univ : Set (Fin 65537))) (Set.subset_univ event)
  have hu' : exceptionWeight*u ≤ exceptionWeight :=
    (mul_le_mul_left' hu exceptionWeight).trans_eq (mul_one _)
  rw [reduced_integer_mixture]
  simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul]
  calc
    u = (ordinaryWeight+exceptionWeight)*u := by rw [mixture_weights, one_mul]
    _ = ordinaryWeight*u+exceptionWeight*u := add_mul _ _ _
    _ ≤ ordinaryWeight*u+exceptionWeight := add_le_add_left hu' _
    _ ≤ (ordinaryWeight*u+exceptionWeight*(Measure.dirac (0 : Fin 65537)) event)+exceptionWeight :=
      add_le_add_right (le_add_right le_rfl) _

end WotsLamport.Submission.Sampler
