import WotsLamport.Submission.SamplerLaw
import Mathlib.Tactic.Finiteness

namespace WotsLamport.Submission.Sampler
open MeasureTheory ProbabilityTheory

local instance (n : Nat) : MeasurableSpace (Fin n) := ⊤

theorem mul_right_mono {a b : ENNReal} (h : a ≤ b) (c : ENNReal) : a*c ≤ b*c := by gcongr
theorem mul_left_mono {a b : ENNReal} (h : a ≤ b) (c : ENNReal) : c*a ≤ c*b := by gcongr
theorem add_right_mono {a b : ENNReal} (h : a ≤ b) (c : ENNReal) : a+c ≤ b+c := by gcongr
theorem add_left_mono {a b : ENNReal} (h : a ≤ b) (c : ENNReal) : c+a ≤ c+b := by gcongr

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
  rw [Measure.map_apply Measurable.of_discrete (measurableSet_singleton r)]
  have hs : reduceInteger ⁻¹' {r} = {n : Fin sampleSize | n.val % 65537 = r.val} := by
    ext n
    simp [reduceInteger, Fin.ext_iff]
  rw [hs, residue_probability]
  simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul,
    uniformOn_univ, Measure.count_singleton, Fintype.card_fin]
  by_cases hz : r = 0
  · subst r
    norm_num [residueCount, quotient, sampleSize, ordinaryWeight, exceptionWeight] <;>
      apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp <;>
      (try rw [ENNReal.toReal_add (by finiteness) (by finiteness)]) <;>
      norm_num [ENNReal.toReal_mul]
  · have hv : r.val ≠ 0 := fun h => hz (Fin.ext h)
    norm_num [residueCount, quotient, sampleSize, ordinaryWeight, exceptionWeight,
      Measure.dirac_apply, hz, hv, Ne.symm hz] <;>
      apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp <;>
      (try rw [ENNReal.toReal_add (by finiteness) (by finiteness)]) <;>
      norm_num [ENNReal.toReal_mul]

theorem mixture_weights : ordinaryWeight + exceptionWeight = 1 := by
  unfold ordinaryWeight exceptionWeight
  rw [ENNReal.div_add_div_same]
  have hn : ((sampleSize-1 : Nat) : ENNReal)+1 = sampleSize := by norm_num [sampleSize]
  rw [hn, ENNReal.div_self (by norm_num [sampleSize]) (by simp)]

theorem ordinaryWeight_le_one : ordinaryWeight ≤ 1 := by
  exact (le_add_right (le_refl ordinaryWeight)).trans_eq mixture_weights

/-- Every measurable event differs from its uniform probability by at most
one exceptional sample. Both directions are available for later hybrids. -/
theorem reduced_integer_event_bound (event : Set (Fin 65537)) :
    ((uniformOn (Set.univ : Set (Fin sampleSize))).map reduceInteger) event ≤
      uniformOn (Set.univ : Set (Fin 65537)) event + exceptionWeight := by
  rw [reduced_integer_mixture]
  simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul]
  apply add_le_add
  · exact (Sampler.mul_right_mono ordinaryWeight_le_one _).trans_eq (one_mul _)
  · have hd : (Measure.dirac (0 : Fin 65537)) event ≤ 1 := by
      simpa using measure_mono (μ := Measure.dirac (0 : Fin 65537)) (Set.subset_univ event)
    exact (Sampler.mul_left_mono hd _).trans_eq (mul_one _)

theorem uniform_event_bound (event : Set (Fin 65537)) :
    uniformOn (Set.univ : Set (Fin 65537)) event ≤
      ((uniformOn (Set.univ : Set (Fin sampleSize))).map reduceInteger) event + exceptionWeight := by
  let u := uniformOn (Set.univ : Set (Fin 65537)) event
  have hu : u ≤ 1 := by
    simpa [u] using measure_mono (μ := uniformOn (Set.univ : Set (Fin 65537))) (Set.subset_univ event)
  have hu' : exceptionWeight*u ≤ exceptionWeight :=
    (Sampler.mul_left_mono hu exceptionWeight).trans_eq (mul_one _)
  rw [reduced_integer_mixture]
  simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul]
  calc
    u = (ordinaryWeight+exceptionWeight)*u := by rw [mixture_weights, one_mul]
    _ = ordinaryWeight*u+exceptionWeight*u := add_mul _ _ _
    _ ≤ ordinaryWeight*u+exceptionWeight := Sampler.add_left_mono hu' _
    _ ≤ (ordinaryWeight*u+exceptionWeight*(Measure.dirac (0 : Fin 65537)) event)+exceptionWeight :=
      Sampler.add_right_mono (le_add_right le_rfl) _

end WotsLamport.Submission.Sampler
