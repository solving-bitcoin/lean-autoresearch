import G1Release.Submission.FiniteApproximation

/-! Joint modulo sampling from independent fixed-width blocks. The proof
counts a common uniform component; it does not assume exact uniformity. -/
namespace G1Release.Submission.ProductSampling
open scoped BigOperators

def sample {ι : Type*} (N : Nat) (m : ι → Nat) (hm : ∀ i, 0 < m i)
    (tape : ι → Fin N) : (i : ι) → Fin (m i) :=
  fun i => ModuloSampling.sample N (m i) (hm i) (tape i)

def fiberEquiv {ι : Type*} (N : Nat) (m : ι → Nat) (hm : ∀ i, 0 < m i)
    (y : (i : ι) → Fin (m i)) :
    {x : ι → Fin N // sample N m hm x = y} ≃
      ((i : ι) → ModuloSampling.Fiber N (m i) (hm i) (y i)) where
  toFun x i := ⟨x.val i, congrFun x.property i⟩
  invFun x := ⟨fun i => (x i).val, funext fun i => (x i).property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem fiber_card_lower {ι : Type*} [Fintype ι]
    (N : Nat) (m : ι → Nat) (hm : ∀ i, 0 < m i) (y : (i : ι) → Fin (m i)) :
    (∏ i, N / m i) ≤ Nat.card {x : ι → Fin N // sample N m hm x = y} := by
  classical
  rw [Nat.card_congr (fiberEquiv N m hm y)]
  simp only [Nat.card_eq_fintype_card, Fintype.card_pi]
  exact Finset.prod_le_prod' fun i _ => by
    simpa using ModuloSampling.le_fiber_card N (m i) (hm i) (y i)

theorem coordinate_mass_bounds (N m : Nat) (hN : 0 < N) (hm : 0 < m) :
    0 ≤ (m : ℝ) * (N / m : Nat) / N ∧
    (m : ℝ) * (N / m : Nat) / N ≤ 1 ∧
    1 - (m : ℝ) * (N / m : Nat) / N ≤ (m : ℝ) / N := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hlo : (m : ℝ) * (N / m : Nat) ≤ N := by
    exact_mod_cast Nat.mul_div_le N m
  have hhi : (N : ℝ) ≤ m * (N / m : Nat) + m := by
    have hrem := Nat.mod_lt N hm
    have hdiv := Nat.mod_add_div N m
    exact_mod_cast (by omega : N ≤ m * (N / m) + m)
  refine ⟨by positivity, (div_le_one hNr).2 hlo, ?_⟩
  apply (le_div_iff₀ hNr).2
  calc
    (1 - (m : ℝ) * (N / m : Nat) / N) * N = N - m * (N / m : Nat) := by field_simp
    _ ≤ m := by linarith

/-- The whole tuple has statistical error at most the sum m_i/N.
The conclusion covers every event, including events chosen after arbitrary
deterministic processing of the sampled randomness. -/
theorem event_probability_bounds {ι : Type*} [Fintype ι]
    (N : Nat) (m : ι → Nat) (hN : 0 < N) (hm : ∀ i, 0 < m i)
    (s : Set ((i : ι) → Fin (m i))) :
    (Nat.card (sample N m hm ⁻¹' s) : ℝ) / Nat.card (ι → Fin N) ≤
      (Nat.card s : ℝ) / Nat.card ((i : ι) → Fin (m i)) + ∑ i, (m i : ℝ) / N ∧
    (Nat.card s : ℝ) / Nat.card ((i : ι) → Fin (m i)) ≤
      (Nat.card (sample N m hm ⁻¹' s) : ℝ) / Nat.card (ι → Fin N) + ∑ i, (m i : ℝ) / N := by
  classical
  letI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  letI (i : ι) : Nonempty (Fin (m i)) := ⟨⟨0, hm i⟩⟩
  apply FiniteApproximation.event_probability_bounds (sample N m hm) (∏ i, N / m i)
    (fiber_card_lower N m hm)
  have hmass :
      (Nat.card ((i : ι) → Fin (m i)) : ℝ) * (∏ i, N / m i : Nat) /
        Nat.card (ι → Fin N) = ∏ i, ((m i : ℝ) * (N / m i : Nat) / N) := by
    simp only [Nat.card_eq_fintype_card, Fintype.card_pi, Fintype.card_fin,
      Nat.cast_prod, Finset.prod_div_distrib, Finset.prod_mul_distrib]
  rw [hmass]
  calc
    1 - ∏ i, ((m i : ℝ) * (N / m i : Nat) / N) ≤
        ∑ i, (1 - (m i : ℝ) * (N / m i : Nat) / N) :=
      FiniteApproximation.product_deficit Finset.univ _
        (fun i _ => (coordinate_mass_bounds N (m i) hN (hm i)).1)
        (fun i _ => (coordinate_mass_bounds N (m i) hN (hm i)).2.1)
    _ ≤ ∑ i, (m i : ℝ) / N := Finset.sum_le_sum fun i _ =>
      (coordinate_mass_bounds N (m i) hN (hm i)).2.2

end G1Release.Submission.ProductSampling
