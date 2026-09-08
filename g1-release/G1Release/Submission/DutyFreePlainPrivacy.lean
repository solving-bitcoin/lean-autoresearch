import G1Release.Submission.DutyFreeOneHot
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Algebra.Group.Units.Equiv

/-! The exact information-theoretic part of the duty-free release. Changing
only the pad at the unopened hot slot couples any two affine maps with the
same selected output. This is a finite permutation, not a ROM assumption. -/
namespace G1Release.Submission.DutyFreePlainPrivacy
open scoped BigOperators
open DutyFreeOneHot

variable {G : Type*} [AddCommGroup G] {n : Nat}

def translate (missing : Fin n) (difference : G) : Equiv.Perm (Fin n → G) :=
  Equiv.addRight (fun i => if i = missing then difference else 0)

theorem translate_apply (missing : Fin n) (difference : G) (masks : Fin n → G) :
    translate missing difference masks = selected masks missing difference := rfl

theorem untouched (missing : Fin n) (difference : G) (masks : Fin n → G)
    (i : Fin n) (hi : i ≠ missing) : translate missing difference masks i = masks i := by
  simp [translate_apply, selected, hi]

theorem join_preserved (missing : Fin n) (source target : G) (masks : Fin n → G) :
    join (translate missing (source-target) masks) target = join masks source := by
  simp only [translate_apply, join, selected, Finset.sum_add_distrib]
  simp
  abel

theorem decoding_preserved (weights : Fin n → Nat) (missing : Fin n)
    (source target constantSource constantTarget : G) (masks : Fin n → G)
    (he : weights missing • source + constantSource =
      weights missing • target + constantTarget) :
    decoding weights (translate missing (source-target) masks) constantTarget =
      decoding weights masks constantSource := by
  rw [translate_apply]
  unfold decoding
  rw [weighted_selected, nsmul_sub]
  have hc : weights missing • source - weights missing • target =
      constantTarget - constantSource := by
    apply (sub_eq_sub_iff_add_eq_add).mpr
    simpa only [add_comm] using he
  rw [hc]
  abel

end G1Release.Submission.DutyFreePlainPrivacy
