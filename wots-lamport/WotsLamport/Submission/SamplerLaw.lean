import WotsLamport.Submission.Sharing
import Mathlib.Probability.UniformOn
import Mathlib.Data.Set.Card

namespace WotsLamport.Submission.Sampler
open MeasureTheory ProbabilityTheory

def sampleSize : Nat := 2^256
def quotient : Nat := sampleSize / 65537

theorem sampleSize_decomposition : sampleSize = 65537*quotient+1 := by
  decide +kernel

def residueCount (r : Fin 65537) : Nat := quotient + if r.val = 0 then 1 else 0

/-- Count residue fibers without enumerating the 2^256 sample space. There
is one extra preimage for residue zero and exactly quotient for every other. -/
def residueFiberEquiv (r : Fin 65537) :
    {n : Fin sampleSize // n.val % 65537 = r.val} ≃ Fin (residueCount r) where
  toFun n := ⟨n.val.val / 65537, by
    have hn := n.val.isLt
    have hr := r.isLt
    have he := n.property
    have hN := sampleSize_decomposition
    unfold residueCount
    split_ifs <;> omega⟩
  invFun j := ⟨⟨j.val*65537+r.val, by
    have hj := j.isLt
    have hr := r.isLt
    have hN := sampleSize_decomposition
    unfold residueCount at hj
    split_ifs at hj <;> omega⟩, by
      have hr := r.isLt
      omega⟩
  left_inv n := by
    apply Subtype.ext
    apply Fin.ext
    have he := n.property
    dsimp
    omega
  right_inv j := by
    apply Fin.ext
    have hr := r.isLt
    dsimp
    omega

theorem residueFiber_card (r : Fin 65537) :
    Fintype.card {n : Fin sampleSize // n.val % 65537 = r.val} = residueCount r := by
  simpa only [Fintype.card_fin] using Fintype.card_congr (residueFiberEquiv r)

local instance (n : Nat) : MeasurableSpace (Fin n) := ⊤

/-- Exact marginal law for reduction of a uniform 256-bit integer. A separate
byte-codec/bijection argument must connect the implementation's coin blocks
to this sample space; this theorem does not assume that connection. -/
theorem residue_probability (r : Fin 65537) :
    uniformOn (Set.univ : Set (Fin sampleSize)) {n | n.val % 65537 = r.val} =
      (residueCount r : ENNReal) / sampleSize := by
  rw [uniformOn_univ, Measure.count_apply MeasurableSet.of_discrete]
  simp [Set.encard, ENat.card_eq_coe_fintype_card, residueFiber_card]

/-- The rational expression corresponding to the exact marginal distance is
small enough for all used blocks. This arithmetic lemma alone does not prove
joint independence or total-variation composition. -/
theorem marginal_distance_arithmetic :
    (8376320 : ℚ) * (65536 / (65537 * 2^256)) < 1 / 2^233 := by
  norm_num

end WotsLamport.Submission.Sampler
