import G1Release.Protected.Target
import G1Release.Submission.BoundaryFacts
import G1Release.Math.Bytes

set_option maxRecDepth 4096
set_option maxHeartbeats 200000

namespace G1Release.Submission.FixedBase
open G1Release.Math

/-- Consecutive powers reuse four doublings per window. -/
def rows (base : BN254.G1) : Nat → List (Vector BN254.G1 16)
  | 0 => []
  | count+1 => (Vector.ofFn fun digit => digit.val • base) :: rows (16 • base) count

theorem rows_length (base : BN254.G1) (count : Nat) : (rows base count).length = count := by
  induction count generalizing base with
  | zero => rfl
  | succ count ih => simp only [rows,List.length_cons,ih]

theorem rows_get (count : Nat) (base : BN254.G1) (index : Nat) (h : index < count) (digit : Fin 16) :
    ((rows base count)[index]'(by rw [rows_length];exact h)).get digit =
      digit.val • ((16^index : Nat) • base) := by
  induction count generalizing base index with
  | zero => omega
  | succ count ih =>
    cases index with
    | zero => simp only [rows,List.getElem_cons_zero,Vector.get_ofFn,pow_zero,one_nsmul]
    | succ index =>
      change ((rows (16 • base) count)[index]'(by rw [rows_length];omega)).get digit = _
      rw [ih (16 • base) index (by omega)]
      congr 1
      rw [← mul_nsmul, Nat.mul_comm (16 : Nat), ← Nat.pow_succ]

/-- The base is a parameter, so the garbler pays initialization once. -/
def table (base : BN254.G1) : Vector (Vector BN254.G1 16) 64 :=
  let values := rows base 64
  Vector.ofFn fun i => values[i.val]'(by rw [rows_length];exact i.isLt)

theorem table_get (base : BN254.G1) (i : Fin 64) (digit : Fin 16) :
    ((table base).get i).get digit = digit.val • ((16^i.val : Nat) • base) := by
  simp only [table,Vector.get_ofFn]
  exact rows_get 64 base i.val i.isLt digit

def accumulate (tables : Vector (Vector BN254.G1 16) 64) (scalar : Nat) :
    (count : Nat) → count ≤ 64 → BN254.G1
  | 0, _ => 0
  | count+1, hc =>
    (tables.get ⟨count,hc⟩).get ⟨(scalar >>> (4*count))%16,Nat.mod_lt _ (by decide)⟩ +
      accumulate tables scalar count (Nat.le_of_succ_le hc)

theorem mod_step (scalar count : Nat) :
    (scalar/16^count%16)*16^count + scalar%16^count = scalar%16^(count+1) := by
  have h := Nat.mod_add_div (scalar%(16^count*16)) (16^count)
  rw [Nat.mod_mod_of_dvd _ (dvd_mul_right _ _), Nat.mod_mul_right_div_self] at h
  simpa only [Nat.pow_succ, Nat.mul_comm, Nat.add_comm] using h

theorem accumulate_eq (base : BN254.G1) (scalar count : Nat) (hc : count ≤ 64) :
    accumulate (table base) scalar count hc = (scalar%16^count) • base := by
  induction count with
  | zero => simp only [accumulate, pow_zero, Nat.mod_one, zero_nsmul]
  | succ count ih =>
    rw [accumulate, table_get, ih]
    have hp : (2 : Nat)^(4*count) = 16^count := by rw [pow_mul]; norm_num
    simp only [Nat.shiftRight_eq_div_pow, hp]
    rw [← mul_nsmul, ← add_nsmul, Nat.mul_comm (16^count), mod_step]

def multiply (tables : Vector (Vector BN254.G1 16) 64) (scalar : Nat) : BN254.G1 :=
  accumulate tables scalar 64 (Nat.le_refl 64)

theorem multiply_eq (base : BN254.G1) (scalar : Fin scalarFieldModulus) :
    multiply (table base) scalar.val = scalar.val • base := by
  have hs : scalar.val < 16^64 := scalar.isLt.trans_le (by norm_num [BoundaryFacts.scalar_modulus])
  exact (accumulate_eq base scalar.val 64 (Nat.le_refl 64)).trans
    (congrArg (fun n : Nat => n • base) (Nat.mod_eq_of_lt hs))

end G1Release.Submission.FixedBase
