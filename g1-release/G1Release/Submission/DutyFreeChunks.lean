import G1Release.Submission.DutyFreeBridge
import G1Release.Submission.DutyFreeChunkAffine
import G1Release.Submission.BoundaryFacts

/-! The 64 little-endian nibbles preserve the challenge's existing byte and
label-bit order, including the two zero padding bits of each Fp coordinate. -/
namespace G1Release.Submission.DutyFreeChunks
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
set_option exponentiation.threshold 1024
open scoped BigOperators
open GarblingPrize.Protected

abbrev Chunk := Fin 64
abbrev Cell := DutyFreeBridge.Cell
abbrev Word := BN254.Fq

def value (coordinate : Nat) (chunk : Chunk) : Cell :=
  ⟨coordinate / 16^chunk.val % 16, Nat.mod_lt _ (by decide)⟩

def weight (chunk : Chunk) : Word := 16^chunk.val

theorem reconstruct_nat (count coordinate : Nat) (h : coordinate < 16^count) :
    (∑ i : Fin count, 16^i.val * (coordinate / 16^i.val % 16)) = coordinate := by
  induction count generalizing coordinate with
  | zero =>
    have : coordinate = 0 := by simpa using h
    simp [this]
  | succ count ih =>
    have hd : coordinate / 16 < 16^count := by
      apply (Nat.div_lt_iff_lt_mul (by decide : 0 < 16)).mpr
      simpa only [pow_succ] using h
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, pow_zero, Nat.div_one, Nat.one_mul, Fin.val_succ]
    have hs : (∑ i : Fin count, 16^(i.val+1) * (coordinate / 16^(i.val+1) % 16)) =
        16 * ∑ i : Fin count, 16^i.val * ((coordinate/16) / 16^i.val % 16) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      simp only [pow_succ, Nat.div_div_eq_div_mul, Nat.mul_comm, Nat.mul_left_comm,
        Nat.mul_assoc]
    rw [hs, ih _ hd]
    exact Nat.mod_add_div coordinate 16

theorem reconstruct (coordinate : Word) :
    DutyFreeChunkAffine.decodeInput weight (value coordinate.val) = coordinate := by
  have hp : coordinate.val < 16^64 := coordinate.val_lt.trans
    (by decide : baseFieldModulus < 16^64)
  have h := congrArg (fun n : Nat => (n : Word)) (reconstruct_nat 64 coordinate.val hp)
  change (∑ i : Fin 64, (16 : Word)^i.val *
    ((coordinate.val / 16^i.val % 16 : Nat) : Word)) = coordinate
  rw [Nat.cast_sum] at h
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, ZMod.natCast_zmod_val] at h
  exact h

theorem bit_order (coordinate : Nat) (chunk : Chunk) (bit : DutyFreeBridge.Bit) :
    DutyFreeBridge.bit (value coordinate chunk) bit = coordinate.testBit (4*chunk.val+bit.val) := by
  change (coordinate / 16^chunk.val % 16).testBit bit.val = _
  have hp : 16^chunk.val = 2^(4*chunk.val) := by rw [Nat.pow_mul]
  rw [hp]
  change (coordinate / 2^(4*chunk.val) % 2^4).testBit bit.val = _
  rw [Nat.testBit_mod_two_pow]
  simp only [bit.isLt, decide_true, Bool.true_and]
  rw [← Nat.shiftRight_eq_div_pow, Nat.testBit_shiftRight]

end G1Release.Submission.DutyFreeChunks
