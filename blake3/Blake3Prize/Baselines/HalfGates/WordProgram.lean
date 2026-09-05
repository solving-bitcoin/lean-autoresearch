import Blake3Prize.Baselines.HalfGates.WordExpression
import Mathlib.Tactic.IntervalCases

/- The operation-parametric program below follows Clean/Specs/BLAKE3.lean
at the pinned revision. See THIRD_PARTY_NOTICES.md for its MIT notice.
The Nat specialization is proved equal to Clean's actual imported compress. -/
namespace Blake3Prize.Baselines.HalfGates.WordProgram
open Blake3Prize.Protected

structure Ops (α : Type) where
  add : α → α → α
  xor : α → α → α
  rotate : α → Nat → α

def natOps : Ops Nat := ⟨add32, Nat.xor, rotRight32⟩
def symbolicOps : Ops WordExpr := ⟨WordExpr.add, WordExpr.xor, WordExpr.rotate⟩

def mix (ops : Ops α) (v : Vector α 16) (a b c d : Fin 16) (mx my : α) : Vector α 16 :=
  let va := ops.add (ops.add v[a] v[b]) mx
  let vd := ops.rotate (ops.xor v[d] va) 16
  let vc := ops.add v[c] vd
  let vb := ops.rotate (ops.xor v[b] vc) 12
  let va := ops.add (ops.add va vb) my
  let vd := ops.rotate (ops.xor vd va) 8
  let vc := ops.add vc vd
  let vb := ops.rotate (ops.xor vb vc) 7
  v.set a va |>.set b vb |>.set c vc |>.set d vd

def round (ops : Ops α) (v m : Vector α 16) : Vector α 16 :=
  Specs.BLAKE3.roundConstants.foldl (fun v (a,b,c,d,i,j) => mix ops v a b c d m[i] m[j]) v

def permute (m : Vector α 16) : Vector α 16 :=
  Vector.ofFn fun i => m[Specs.BLAKE3.msgPermutation[i]]

def rounds (ops : Ops α) (v m : Vector α 16) : Vector α 16 :=
  let v := round ops v m
  let m := permute m
  let v := round ops v m
  let m := permute m
  let v := round ops v m
  let m := permute m
  let v := round ops v m
  let m := permute m
  let v := round ops v m
  let m := permute m
  let v := round ops v m
  let m := permute m
  round ops v m

def finish (ops : Ops α) (v : Vector α 16) : Vector α 8 :=
  Vector.ofFn fun i => ops.xor v[i.val] v[i.val + 8]

def digest (ops : Ops α) (v m : Vector α 16) : Vector α 8 := finish ops (rounds ops v m)

def initialWords : Vector Nat 16 := #v[
  chainingValue[0], chainingValue[1], chainingValue[2], chainingValue[3],
  chainingValue[4], chainingValue[5], chainingValue[6], chainingValue[7],
  Specs.BLAKE3.iv[0].toNat, Specs.BLAKE3.iv[1].toNat,
  Specs.BLAKE3.iv[2].toNat, Specs.BLAKE3.iv[3].toNat,
  0, 0, 64, 11]

/-- Reassociate modular sums to retain the existing circuit's constant folding.
This is an algebraic equality for all Nat operands, including overflow. -/
theorem add32_assoc (x y z : Nat) : add32 (add32 x y) z = add32 x (add32 y z) := by
  simp [add32, Nat.add_assoc]

theorem mix_nat (v : Vector Nat 16) (a b c d : Fin 16) (mx my : Nat) :
    mix natOps v a b c d mx my = Specs.BLAKE3.g v a b c d mx my := by
  simp only [mix, Specs.BLAKE3.g, natOps, add32_assoc]
  rfl

theorem round_nat (v m : Vector Nat 16) :
    round natOps v m = Specs.BLAKE3.round v m := by
  simp only [round, Specs.BLAKE3.round, mix_nat]

theorem rounds_nat (m : Vector Nat 16) :
    rounds natOps initialWords m = Specs.BLAKE3.applyRounds chainingValue m 0 64 11 := by
  simp only [rounds, round_nat]
  rfl

theorem finish_nat (v : Vector Nat 16) (cv : Vector Nat 8) :
    finish natOps v = (Specs.BLAKE3.finalStateUpdate v cv).take 8 := by
  apply Vector.ext
  intro i hi
  interval_cases i <;> rfl

/-- The challenge's word program is connected to the imported Clean spec,
not accepted as an independent replacement specification. -/
theorem digest_nat (m : Vector Nat 16) :
    digest natOps initialWords m = referenceWords m := by
  unfold digest
  rw [rounds_nat, finish_nat _ chainingValue]
  rfl

end Blake3Prize.Baselines.HalfGates.WordProgram
