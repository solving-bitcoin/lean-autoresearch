import G1Release.Submission.FiniteProbability
import Mathlib.Data.Set.Card
import Mathlib.Tactic.Positivity
import Mathlib.Logic.Equiv.Fin.Basic

/-! A finite-oracle pad cannot be declared exactly uniform modulo an arbitrary
CRT-vector cardinality. Permute complete blocks and leave the final incomplete
block fixed. The resulting map is an actual permutation of raw oracle answers;
outside a tail of size N mod m, it realizes any requested residue permutation.
This is the arithmetic bridge needed by a bounded-query ROM coupling. -/
namespace G1Release.Submission.DutyFreeModularCoupling

def coordinates (N m : Nat) : Fin N ≃ (Fin (N/m) × Fin m) ⊕ Fin (N%m) :=
  (finCongr (show N/m*m + N%m = N by
    simpa only [Nat.mul_comm] using Nat.div_add_mod N m).symm).trans
    (finSumFinEquiv.symm.trans
      (Equiv.sumCongr finProdFinEquiv.symm (Equiv.refl _)))

theorem coordinates_full (N m : Nat) (q : Fin (N/m)) (r : Fin m) :
    ((coordinates N m).symm (Sum.inl (q,r))).val = r.val + m*q.val := rfl

theorem coordinates_tail (N m : Nat) (r : Fin (N%m)) :
    ((coordinates N m).symm (Sum.inr r)).val = N/m*m + r.val := rfl

def transport (N m : Nat) (permutation : Equiv.Perm (Fin m)) : Equiv.Perm (Fin N) :=
  (coordinates N m).trans
    ((Equiv.sumCongr (Equiv.prodCongr (Equiv.refl _) permutation) (Equiv.refl _)).trans
      (coordinates N m).symm)

def bad (N m : Nat) : Set (Fin N) :=
  Set.range fun r : Fin (N%m) => (coordinates N m).symm (Sum.inr r)

theorem bad_card (N m : Nat) : Nat.card (bad N m) = N%m := by
  let f : Fin (N%m) → Fin N := fun r => (coordinates N m).symm (Sum.inr r)
  have hf : Function.Injective f := (coordinates N m).symm.injective.comp Sum.inr_injective
  simpa [bad, f] using (Nat.card_congr (Equiv.ofInjective f hf)).symm

theorem bad_card_lt (N m : Nat) (hm : 0 < m) : Nat.card (bad N m) < m := by
  rw [bad_card]
  exact Nat.mod_lt _ hm

theorem fixes_tail (N m : Nat) (permutation : Equiv.Perm (Fin m)) (x : Fin N)
    (hx : x ∈ bad N m) : transport N m permutation x = x := by
  obtain ⟨r,rfl⟩ := hx
  simp [transport]

theorem transports_residue (N m : Nat) (hm : 0 < m)
    (permutation : Equiv.Perm (Fin m)) (x : Fin N) (hx : x ∉ bad N m) :
    ((transport N m permutation x).val % m) =
      (permutation ⟨x.val % m, Nat.mod_lt _ hm⟩).val := by
  cases he : coordinates N m x with
  | inr r =>
    apply False.elim
    apply hx
    refine ⟨r, ?_⟩
    simpa only [Equiv.symm_apply_apply] using (congrArg (coordinates N m).symm he).symm
  | inl pair =>
    have hxi : x = (coordinates N m).symm (Sum.inl pair) := by rw [← he]; simp
    rw [hxi]
    simp only [transport, Equiv.trans_apply, Equiv.apply_symm_apply,
      Equiv.sumCongr_apply, Equiv.prodCongr_apply, Equiv.refl_apply]
    change ((coordinates N m).symm (Sum.inl (pair.1, permutation pair.2))).val % m =
      (permutation ⟨((coordinates N m).symm (Sum.inl pair)).val % m, _⟩).val
    rw [coordinates_full, coordinates_full]
    have hr : (pair.2.val + m*pair.1.val)%m = pair.2.val := by
      simp [Nat.mod_eq_of_lt pair.2.isLt]
    have hrf : (⟨(pair.2.val + m*pair.1.val)%m, Nat.mod_lt _ hm⟩ : Fin m) = pair.2 :=
      Fin.ext hr
    rw [hrf]
    have hp : (permutation pair.2).val < m := (permutation pair.2).isLt
    simp [Nat.mod_eq_of_lt hp]

theorem tail_probability (N m : Nat) [NeZero N] (hm : 0 < m) :
    (Nat.card (bad N m) : ℝ) / N ≤ (m : ℝ) / N := by
  rw [bad_card]
  apply div_le_div_of_nonneg_right
  · exact_mod_cast (Nat.mod_lt N hm).le
  · positivity

end G1Release.Submission.DutyFreeModularCoupling
