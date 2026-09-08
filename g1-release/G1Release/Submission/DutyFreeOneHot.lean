import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.Fintype.Fin
import Mathlib.Algebra.Group.Basic
import Mathlib.Tactic.Abel

/-! The plain-label scale-hot operation from ePrint 2026/476, Lemma 6.2.
All zero slots are opened by switches. A single additive join recovers the
remaining slot. The affine output needs one further decoding group element.
These algebraic statements hold for every pad family and do not assume an
idealized oracle or a security conclusion. -/
namespace G1Release.Submission.DutyFreeOneHot
open scoped BigOperators

variable {G : Type*} [AddCommGroup G] {n : Nat}

def without (values : Fin n → G) (missing : Fin n) : G :=
  ∑ i ∈ Finset.univ.erase missing, values i

theorem without_add (values : Fin n → G) (missing : Fin n) :
    without values missing + values missing = ∑ i, values i := by
  exact Finset.sum_erase_add _ _ (Finset.mem_univ missing)

def selected (masks : Fin n → G) (missing : Fin n) (payload : G) : Fin n → G :=
  fun i => masks i + if i = missing then payload else 0

def join (masks : Fin n → G) (payload : G) : G := (∑ i, masks i) + payload

def recover (available : Fin n → G) (missing : Fin n) (material : G) : Fin n → G :=
  fun i => if i = missing then material - without available missing else available i

theorem recover_join (masks : Fin n → G) (missing : Fin n) (payload : G) :
    recover masks missing (join masks payload) = selected masks missing payload := by
  funext i
  by_cases hi : i = missing
  · subst i
    simp only [recover, selected, join, ite_true]
    rw [← without_add masks missing]
    abel
  · simp [recover, selected, hi]

/-- No knowledge of the missing pad is required to evaluate the join. -/
theorem recover_of_available (available masks : Fin n → G) (missing : Fin n) (payload : G)
    (h : ∀ i, i ≠ missing → available i = masks i) :
    recover available missing (join masks payload) = selected masks missing payload := by
  have hs : without available missing = without masks missing := by
    apply Finset.sum_congr rfl
    intro i hi
    exact h i (Finset.mem_erase.mp hi).1
  rw [← recover_join masks missing payload]
  funext i
  by_cases hi : i = missing
  · simp [recover, hi, hs]
  · simp [recover, hi, h i hi]

def weighted (weights : Fin n → Nat) (values : Fin n → G) : G :=
  ∑ i, weights i • values i

theorem weighted_selected (weights : Fin n → Nat) (masks : Fin n → G)
    (missing : Fin n) (payload : G) :
    weighted weights (selected masks missing payload) =
      weighted weights masks + weights missing • payload := by
  simp [weighted, selected, nsmul_add, Finset.sum_add_distrib]

def decoding (weights : Fin n → Nat) (masks : Fin n → G) (constant : G) : G :=
  weighted weights masks - constant

theorem affine_correct (weights : Fin n → Nat) (available masks : Fin n → G)
    (missing : Fin n) (coefficient constant : G)
    (h : ∀ i, i ≠ missing → available i = masks i) :
    weighted weights (recover available missing (join masks coefficient)) -
      decoding weights masks constant = weights missing • coefficient + constant := by
  rw [recover_of_available available masks missing coefficient h, weighted_selected]
  unfold decoding
  abel

end G1Release.Submission.DutyFreeOneHot
