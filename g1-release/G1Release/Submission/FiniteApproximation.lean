import G1Release.Submission.ModuloSampling

/-! A lower bound shared by every fiber gives a common uniform component.
The remaining mass bounds every event in both directions. -/
namespace G1Release.Submission.FiniteApproximation
open scoped BigOperators

def eventEquiv {α β : Type*} (f : α → β) (s : Set β) :
    (f ⁻¹' s) ≃ (Σ y : s, {x : α // f x = y.val}) where
  toFun x := ⟨⟨f x.val, x.property⟩, ⟨x.val, rfl⟩⟩
  invFun p := ⟨p.2.val, by change f p.2.val ∈ s; rw [p.2.property]; exact p.1.property⟩
  left_inv _ := rfl
  right_inv p := by rcases p with ⟨⟨y, hy⟩, ⟨x, hx⟩⟩; cases hx; rfl

theorem event_card_lower {α β : Type*} [Finite α] [Finite β]
    (f : α → β) (L : Nat) (hL : ∀ y, L ≤ Nat.card {x : α // f x = y})
    (s : Set β) : L * Nat.card s ≤ Nat.card (f ⁻¹' s) := by
  classical
  letI := Fintype.ofFinite α
  letI := Fintype.ofFinite β
  letI : Fintype s := Fintype.ofFinite s
  letI (y : β) : Fintype {x : α // f x = y} := Fintype.ofFinite _
  rw [Nat.card_congr (eventEquiv f s)]
  simp only [Nat.card_eq_fintype_card, Fintype.card_sigma]
  calc
    L * Fintype.card s = ∑ _ : s, L := by simp [Nat.mul_comm]
    _ ≤ ∑ y : s, Fintype.card {x : α // f x = y.val} :=
      Finset.sum_le_sum fun y _ => by simpa using hL y.val

theorem card_compl_add {α : Type*} [Finite α] (s : Set α) :
    Nat.card (sᶜ : Set α) + Nat.card s = Nat.card α := by
  classical
  letI := Fintype.ofFinite α
  simp only [Nat.card_eq_fintype_card, Fintype.card_compl_set]
  exact Nat.sub_add_cancel (Fintype.card_subtype_le _)

/-- A fiber lower bound is enough: excess probability is controlled by
applying the same lower bound to the complementary event. -/
theorem event_probability_bounds {α β : Type*} [Finite α] [Finite β]
    [Nonempty α] [Nonempty β] (f : α → β) (L : Nat)
    (hL : ∀ y, L ≤ Nat.card {x : α // f x = y}) (ε : ℝ)
    (hε : 1 - (Nat.card β : ℝ) * L / Nat.card α ≤ ε) (s : Set β) :
    (Nat.card (f ⁻¹' s) : ℝ) / Nat.card α ≤ (Nat.card s : ℝ) / Nat.card β + ε ∧
      (Nat.card s : ℝ) / Nat.card β ≤ (Nat.card (f ⁻¹' s) : ℝ) / Nat.card α + ε := by
  have hα : (0 : ℝ) < Nat.card α := by exact_mod_cast Nat.card_pos
  have hβ : (0 : ℝ) < Nat.card β := by exact_mod_cast Nat.card_pos
  have htotal : (L : ℝ) * Nat.card β ≤ Nat.card α := by
    exact_mod_cast (by simpa using event_card_lower f L hL Set.univ)
  have lower (t : Set β) :
      (Nat.card t : ℝ) / Nat.card β ≤ (Nat.card (f ⁻¹' t) : ℝ) / Nat.card α + ε := by
    have ht : (Nat.card t : ℝ) ≤ Nat.card β := by
      exact_mod_cast Nat.card_le_card_of_injective (fun x : t => x.val) Subtype.val_injective
    have hf : (L : ℝ) * Nat.card t ≤ Nat.card (f ⁻¹' t) := by
      exact_mod_cast event_card_lower f L hL t
    have hmul := mul_nonneg (sub_nonneg.mpr ht) (sub_nonneg.mpr htotal)
    have hslack : (Nat.card α : ℝ) - Nat.card β * L ≤ ε * Nat.card α := by
      exact (div_le_iff₀ hα).1 (by simpa [sub_div] using hε)
    apply (div_le_iff₀ hβ).2
    apply (mul_le_mul_iff_left₀ hα).1
    calc
      (Nat.card t : ℝ) * Nat.card α ≤
          (Nat.card (f ⁻¹' t) : ℝ) * Nat.card β + ε * Nat.card α * Nat.card β := by
        nlinarith [mul_le_mul_of_nonneg_right hf (le_of_lt hβ),
          mul_le_mul_of_nonneg_right hslack (le_of_lt hβ)]
      _ = ((Nat.card (f ⁻¹' t) : ℝ) / Nat.card α + ε) * Nat.card β * Nat.card α := by
        field_simp
  refine ⟨?_, lower s⟩
  have hc := lower sᶜ
  have hs : (Nat.card (sᶜ : Set β) : ℝ) + Nat.card s = Nat.card β := by
    exact_mod_cast card_compl_add s
  have hp : (Nat.card (f ⁻¹' sᶜ) : ℝ) + Nat.card (f ⁻¹' s) = Nat.card α := by
    exact_mod_cast card_compl_add (f ⁻¹' s)
  have hs' : (Nat.card (sᶜ : Set β) : ℝ) / Nat.card β + Nat.card s / Nat.card β = 1 := by
    rw [← add_div, hs, div_self (ne_of_gt hβ)]
  have hp' : (Nat.card (f ⁻¹' sᶜ) : ℝ) / Nat.card α +
      Nat.card (f ⁻¹' s) / Nat.card α = 1 := by
    rw [← add_div, hp, div_self (ne_of_gt hα)]
  linarith

/-- Product loss is at most the sum of the coordinate losses. -/
theorem product_deficit {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (h0 : ∀ i ∈ s, 0 ≤ f i) (h1 : ∀ i ∈ s, f i ≤ 1) :
    1 - ∏ i ∈ s, f i ≤ ∑ i ∈ s, (1 - f i) := by
  letI : DecidableEq ι := Classical.decEq ι
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have ha0 := h0 a (Finset.mem_insert_self _ _)
    have ha1 := h1 a (Finset.mem_insert_self _ _)
    have hs0 : ∀ i ∈ s, 0 ≤ f i := fun i hi => h0 i (Finset.mem_insert_of_mem hi)
    have hs1 : ∀ i ∈ s, f i ≤ 1 := fun i hi => h1 i (Finset.mem_insert_of_mem hi)
    have hp : ∏ i ∈ s, f i ≤ 1 := Finset.prod_le_one hs0 hs1
    have hmul := mul_nonneg (sub_nonneg.mpr ha1) (sub_nonneg.mpr hp)
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    linarith [ih hs0 hs1]

end G1Release.Submission.FiniteApproximation
