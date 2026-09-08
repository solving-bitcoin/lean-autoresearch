import Blake3Prize.Submission.HalfGatesMorphism
import Blake3Prize.Submission.RomArithmetic

/-! Reuse the already checked, operation-parametric BLAKE3 program. This
file connects its BitVec specialization to Clean's Nat specification. -/
namespace Blake3Prize.Submission.RomWordSemantics
open HalfGates Blake3Prize.Protected

def ops : WordProgram.Ops (BitVec 32) := ⟨(·+·),(·^^^·),BitVec.rotateRight⟩

theorem rotate_nat (x : BitVec 32) (offset : Nat) :
    (x.rotateRight offset).toNat = rotRight32 x.toNat offset := by
  let k := offset % 32
  have hk : k ≤ 32 := Nat.le_of_lt (Nat.mod_lt offset (by decide))
  have hp : 2^32 = 2^k * 2^(32-k) := by
    rw [← Nat.pow_add,Nat.add_sub_of_le hk]
  have hm : (x.toNat * 2^(32-k)) % 2^32 = (x.toNat % 2^k) * 2^(32-k) := by
    rw [hp,Nat.mul_mod_mul_right]
  have hh : x.toNat / 2^k < 2^(32-k) := by
    apply (Nat.div_lt_iff_lt_mul (by positivity : 0 < 2^k)).mpr
    rw [Nat.mul_comm,← hp]
    exact x.isLt
  rw [BitVec.toNat_rotateRight]
  change (x.toNat >>> k) ||| (x.toNat <<< (32-k)) % 2^32 =
    (x.toNat % 2^k) * 2^(32-k) + x.toNat / 2^k
  rw [Nat.shiftRight_eq_div_pow,Nat.shiftLeft_eq,hm,Nat.mul_comm (x.toNat % 2^k),
    Nat.two_pow_add_eq_or_of_lt hh,Nat.or_comm]

def natHom : WordHom ops WordProgram.natOps where
  apply := BitVec.toNat
  add x y := BitVec.toNat_add x y
  xor x y := BitVec.toNat_xor x y
  rotate := rotate_nat

def initial : Vector (BitVec 32) 16 := WordProgram.initialWords.map (BitVec.ofNat 32)

theorem initial_nat : initial.map BitVec.toNat = WordProgram.initialWords := by
  apply Vector.ext
  intro i hi
  have h : WordProgram.initialWords[i] < 2^32 := by
    delta WordProgram.initialWords chainingValue Specs.BLAKE3.iv
    interval_cases i <;> norm_num
    all_goals exact UInt32.toNat_lt _
  simpa only [initial,Vector.getElem_map,BitVec.toNat_ofNat] using Nat.mod_eq_of_lt h

def message (input : Input) : Vector (BitVec 32) 16 :=
  (inputWords input).map (BitVec.ofNat 32)

theorem inputWords_lt (input : Input) (i : Fin 16) : (inputWords input).get i < 2^32 := by
  exact ReferenceEncoding.word_lt input i

theorem message_nat (input : Input) : (message input).map BitVec.toNat = inputWords input := by
  ext i hi
  simp only [message,Vector.getElem_map,BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (inputWords_lt input ⟨i,hi⟩)

def digest (input : Input) : Vector (BitVec 32) 8 :=
  WordProgram.digest ops initial (message input)

theorem digest_nat (input : Input) : (digest input).map BitVec.toNat = referenceWords (inputWords input) := by
  have h := natHom.digest initial (message input)
  change (digest input).map BitVec.toNat =
    WordProgram.digest WordProgram.natOps (initial.map BitVec.toNat)
      ((message input).map BitVec.toNat) at h
  simpa only [initial_nat,message_nat,WordProgram.digest_nat] using h

end Blake3Prize.Submission.RomWordSemantics
