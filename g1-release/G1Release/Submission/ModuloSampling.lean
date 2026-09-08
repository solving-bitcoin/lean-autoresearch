import G1Release.Submission.FiniteProbability
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! Counting bounds for finite byte-tape sampling. Reduction modulo an odd
field size is not exactly uniform; each residue has floor(N/m) or ceil(N/m)
preimages among N equally likely tape values. -/
namespace G1Release.Submission.ModuloSampling
open scoped BigOperators

def sample (N m : Nat) (hm : 0 < m) (x : Fin N) : Fin m :=
  ⟨x.val % m, Nat.mod_lt _ hm⟩

abbrev Fiber (N m : Nat) (hm : 0 < m) (y : Fin m) :=
  { x : Fin N // sample N m hm x = y }

private def quotient (N m : Nat) (hm : 0 < m) (y : Fin m) :
    Fiber N m hm y → Fin (N / m + 1) := fun x =>
  ⟨x.val.val / m, Nat.lt_succ_of_le (Nat.div_le_div_right (Nat.le_of_lt x.val.isLt))⟩

private theorem quotient_injective (N m : Nat) (hm : 0 < m) (y : Fin m) :
    Function.Injective (quotient N m hm y) := by
  intro a b h
  apply Subtype.ext
  apply Fin.ext
  have hd : a.val.val / m = b.val.val / m := congrArg Fin.val h
  have ha : a.val.val % m = y.val := congrArg Fin.val a.property
  have hb : b.val.val % m = y.val := congrArg Fin.val b.property
  calc
    a.val.val = a.val.val % m + m * (a.val.val / m) := (Nat.mod_add_div _ _).symm
    _ = b.val.val % m + m * (b.val.val / m) := by rw [ha, hb, hd]
    _ = b.val.val := Nat.mod_add_div _ _

theorem fiber_card_le (N m : Nat) (hm : 0 < m) (y : Fin m) :
    Nat.card (Fiber N m hm y) ≤ N / m + 1 := by
  simpa using Nat.card_le_card_of_injective (quotient N m hm y)
    (quotient_injective N m hm y)

private theorem residue_lt (N m : Nat) (y : Fin m) (x : Fin (N / m)) :
    x.val * m + y.val < N := by
  calc
    x.val * m + y.val < x.val * m + m := Nat.add_lt_add_left y.isLt _
    _ = (x.val + 1) * m := by simp [Nat.add_mul]
    _ ≤ (N / m) * m := Nat.mul_le_mul_right _ x.isLt
    _ ≤ N := Nat.div_mul_le_self _ _

private def residue (N m : Nat) (hm : 0 < m) (y : Fin m) :
    Fin (N / m) → Fiber N m hm y := fun x =>
  ⟨⟨x.val * m + y.val, residue_lt N m y x⟩, by
    apply Fin.ext
    simp [sample, Nat.mod_eq_of_lt y.isLt]⟩

private theorem residue_injective (N m : Nat) (hm : 0 < m) (y : Fin m) :
    Function.Injective (residue N m hm y) := by
  intro a b h
  apply Fin.ext
  have h' : a.val * m + y.val = b.val * m + y.val :=
    congrArg (fun x : Fiber N m hm y => x.val.val) h
  exact Nat.eq_of_mul_eq_mul_right hm (Nat.add_right_cancel h')

theorem le_fiber_card (N m : Nat) (hm : 0 < m) (y : Fin m) :
    N / m ≤ Nat.card (Fiber N m hm y) := by
  simpa using Nat.card_le_card_of_injective (residue N m hm y)
    (residue_injective N m hm y)

private def eventEquiv (N m : Nat) (hm : 0 < m) (s : Set (Fin m)) :
    (sample N m hm ⁻¹' s) ≃ (Σ y : s, Fiber N m hm y.val) where
  toFun x := ⟨⟨sample N m hm x.val, x.property⟩, ⟨x.val, rfl⟩⟩
  invFun p := ⟨p.2.val, by
    change sample N m hm p.2.val ∈ s
    rw [p.2.property]
    exact p.1.property⟩
  left_inv _ := rfl
  right_inv p := by
    rcases p with ⟨⟨y, hy⟩, ⟨x, hx⟩⟩
    cases hx
    rfl

theorem event_card_bounds (N m : Nat) (hm : 0 < m) (s : Set (Fin m)) :
    (N / m) * Nat.card s ≤ Nat.card (sample N m hm ⁻¹' s) ∧
      Nat.card (sample N m hm ⁻¹' s) ≤ (N / m + 1) * Nat.card s := by
  classical
  letI : Fintype s := Fintype.ofFinite s
  have hsum : Nat.card (sample N m hm ⁻¹' s) =
      ∑ y : s, Nat.card (Fiber N m hm y.val) := by
    rw [Nat.card_congr (eventEquiv N m hm s)]
    simp [Nat.card_eq_fintype_card, Fintype.card_sigma]
  rw [hsum]
  constructor
  · calc
      (N / m) * Nat.card s = ∑ _ : s, N / m := by simp [Nat.mul_comm]
      _ ≤ ∑ y : s, Nat.card (Fiber N m hm y.val) :=
        Finset.sum_le_sum fun y _ => le_fiber_card N m hm y.val
  · calc
      (∑ y : s, Nat.card (Fiber N m hm y.val)) ≤ ∑ _ : s, (N / m + 1) :=
        Finset.sum_le_sum fun y _ => fiber_card_le N m hm y.val
      _ = (N / m + 1) * Nat.card s := by simp [Nat.mul_comm]

theorem event_cross_bounds (N m : Nat) (hm : 0 < m) (s : Set (Fin m)) :
    Nat.card (sample N m hm ⁻¹' s) * m ≤ N * Nat.card s + m*m ∧
      N * Nat.card s ≤ Nat.card (sample N m hm ⁻¹' s) * m + m*m := by
  have hc : Nat.card s ≤ m := by
    simpa using Nat.card_le_card_of_injective (fun x : s => x.val) Subtype.val_injective
  have hb := event_card_bounds N m hm s
  have hq := Nat.div_mul_le_self N m
  have hq' : N ≤ (N / m + 1) * m := by
    have hrem := Nat.mod_lt N hm
    have hdiv := Nat.mod_add_div N m
    nlinarith
  have hcm := Nat.mul_le_mul_right m hc
  constructor
  · nlinarith only [Nat.mul_le_mul_right m hb.2, Nat.mul_le_mul_right (Nat.card s) hq, hcm]
  · nlinarith only [Nat.mul_le_mul_right m hb.1, Nat.mul_le_mul_right (Nat.card s) hq', hcm]

/-- Additive error for every event, in both directions. This includes N not
divisible by m, and makes no exact-uniformity claim for the residue sampler. -/
theorem event_probability_bounds (N m : Nat) (hN : 0 < N) (hm : 0 < m)
    (s : Set (Fin m)) :
    (Nat.card (sample N m hm ⁻¹' s) : ℝ) / N ≤ (Nat.card s : ℝ) / m + (m : ℝ) / N ∧
      (Nat.card s : ℝ) / m ≤ (Nat.card (sample N m hm ⁻¹' s) : ℝ) / N + (m : ℝ) / N := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hmr : (0 : ℝ) < m := by exact_mod_cast hm
  have hcross := event_cross_bounds N m hm s
  have hu : (Nat.card (sample N m hm ⁻¹' s) : ℝ) * m ≤
      N * (Nat.card s : ℝ) + m*m := by exact_mod_cast hcross.1
  have hl : (N : ℝ) * (Nat.card s : ℝ) ≤
      (Nat.card (sample N m hm ⁻¹' s) : ℝ) * m + m*m := by exact_mod_cast hcross.2
  constructor
  · apply (div_le_iff₀ hNr).2
    apply (mul_le_mul_iff_right₀ hmr).1
    calc
      (m : ℝ) * Nat.card (sample N m hm ⁻¹' s) ≤ N * (Nat.card s : ℝ) + m*m := by
        nlinarith only [hu]
      _ = m * (((Nat.card s : ℝ) / m + (m : ℝ) / N) * N) := by field_simp
  · rw [← add_div]
    apply (div_le_div_iff₀ hmr hNr).2
    nlinarith only [hl]

end G1Release.Submission.ModuloSampling
