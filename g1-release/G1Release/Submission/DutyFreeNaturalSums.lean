import G1Release.Submission.DutyFreeOneHot
import G1Release.Math.G1
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! Arbitrary-precision integer accumulation followed by one field reduction
is exactly the same ring sum. It avoids reducing every intermediate addend
in the concrete duty-free tables. There is no machine-word overflow premise. -/
namespace G1Release.Submission.DutyFreeNaturalSums
open G1Release.Math
open scoped BigOperators

abbrev Word := BN254.Fq

def sum (values : Fin n → Word) : Word := ((∑ i, (values i).val : Nat) : Word)

theorem sum_eq (values : Fin n → Word) : sum values = ∑ i, values i := by
  simp only [sum, Nat.cast_sum, ZMod.natCast_zmod_val]

theorem without_eq (values : Fin n → Word) (missing : Fin n) :
    sum values - values missing = DutyFreeOneHot.without values missing := by
  rw [sum_eq, ← DutyFreeOneHot.without_add values missing]
  exact add_sub_cancel_right _ _

def weighted (values : Fin n → Word) : Word := ((∑ i, i.val * (values i).val : Nat) : Word)

theorem weighted_eq (values : Fin n → Word) :
    weighted values = DutyFreeOneHot.weighted Fin.val values := by
  simp only [weighted, DutyFreeOneHot.weighted, Nat.cast_sum, Nat.cast_mul,
    ZMod.natCast_zmod_val, nsmul_eq_mul]

end G1Release.Submission.DutyFreeNaturalSums
