import G1Release.Submission.DutyFreePlainPrivacy
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

/-! Many small one-hot releases share one final decoding word. Publishing
the intermediate decoding masks would double the field communication and
expose individual affine chunks. Only the sum is decoded here. -/
namespace G1Release.Submission.DutyFreeChunkAffine
open scoped BigOperators
open DutyFreeOneHot

variable {F : Type*} [CommRing F] {c n : Nat}

abbrev Masks (F : Type*) (c n : Nat) := Fin c → Fin n → F

structure Artifact (F : Type*) (c : Nat) where
  joins : Fin c → F
  decoding : F

def decodeInput (weights : Fin c → F) (input : Fin c → Fin n) : F :=
  ∑ chunk, weights chunk * (input chunk).val

def garble (weights : Fin c → F) (masks : Masks F c n)
    (coefficient constant : F) : Artifact F c :=
  ⟨fun chunk => join (masks chunk) (weights chunk * coefficient),
    (∑ chunk, weighted Fin.val (masks chunk)) - constant⟩

def evaluate (artifact : Artifact F c) (input : Fin c → Fin n) (available : Masks F c n) : F :=
  (∑ chunk, weighted Fin.val (recover (available chunk) (input chunk) (artifact.joins chunk))) -
    artifact.decoding

theorem correct (weights : Fin c → F) (masks available : Masks F c n)
    (coefficient constant : F) (input : Fin c → Fin n)
    (h : ∀ chunk cell, cell ≠ input chunk → available chunk cell = masks chunk cell) :
    evaluate (garble weights masks coefficient constant) input available =
      coefficient * decodeInput weights input + constant := by
  unfold evaluate garble
  simp only [recover_of_available _ _ _ _ (h _), weighted_selected,
    Finset.sum_add_distrib, nsmul_eq_mul]
  have hs : (∑ chunk, (input chunk).val * (weights chunk * coefficient)) =
      coefficient * decodeInput weights input := by
    unfold decodeInput
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro chunk _
    ring
  rw [hs]
  ring

def transport (weights : Fin c → F) (input : Fin c → Fin n) (source target : F) :
    Equiv.Perm (Masks F c n) :=
  Equiv.piCongrRight fun chunk => DutyFreePlainPrivacy.translate (input chunk)
    (weights chunk * (source-target))

theorem transport_apply (weights : Fin c → F) (input : Fin c → Fin n) (source target : F)
    (masks : Masks F c n) (chunk : Fin c) :
    transport weights input source target masks chunk =
      selected (masks chunk) (input chunk) (weights chunk * (source-target)) := rfl

theorem untouched (weights : Fin c → F) (input : Fin c → Fin n) (source target : F)
    (masks : Masks F c n) (chunk : Fin c) (cell : Fin n) (h : cell ≠ input chunk) :
    transport weights input source target masks chunk cell = masks chunk cell := by
  rw [transport_apply]
  simp [selected, h]

theorem artifact_preserved (weights : Fin c → F) (input : Fin c → Fin n)
    (source target constantSource constantTarget : F) (masks : Masks F c n)
    (he : source * decodeInput weights input + constantSource =
      target * decodeInput weights input + constantTarget) :
    garble weights (transport weights input source target masks) target constantTarget =
      garble weights masks source constantSource := by
  have hj (chunk : Fin c) :
      join (transport weights input source target masks chunk) (weights chunk * target) =
        join (masks chunk) (weights chunk * source) := by
    rw [transport_apply, mul_sub]
    exact DutyFreePlainPrivacy.join_preserved (input chunk) (weights chunk * source)
      (weights chunk * target) (masks chunk)
  have hs : (∑ chunk, (input chunk).val • (weights chunk * (source-target))) =
      (source-target) * decodeInput weights input := by
    unfold decodeInput
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro chunk _
    rw [nsmul_eq_mul]
    ring
  have hc : (source-target) * decodeInput weights input = constantTarget - constantSource := by
    rw [sub_mul]
    exact sub_eq_sub_iff_add_eq_add.mpr (by simpa only [add_comm] using he)
  unfold garble
  congr 1
  · exact funext hj
  · simp only [transport_apply, weighted_selected, Finset.sum_add_distrib]
    rw [hs, hc]
    ring

end G1Release.Submission.DutyFreeChunkAffine
