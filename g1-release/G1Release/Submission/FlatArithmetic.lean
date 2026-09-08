import G1Release.Submission.PackedArithmetic

set_option maxRecDepth 4096
set_option maxHeartbeats 300000

namespace G1Release.Submission.FlatArithmetic
open SecretRelease

/-- Read a small slice through a function, without allocating its vector. -/
@[specialize] def read (byte : Fin n → UInt8) : (count : Nat) → count ≤ n → Nat
  | 0, _ => 0
  | count+1, h =>
    ((byte ⟨count,h⟩).toNat <<< (count*8)) + read byte count (Nat.le_of_succ_le h)

theorem read_ofFn (byte : Fin n → UInt8) (count : Nat) (h : count ≤ n) :
    read byte count h = ByteArithmetic.read (Vector.ofFn byte) count h := by
  induction count with
  | zero => rfl
  | succ count ih => simp only [read,ByteArithmetic.read,ih,Vector.get_ofFn,Nat.mul_comm]

@[specialize] def chunks (byte : Fin (n*8) → UInt8) : (count : Nat) → count ≤ n → Nat
  | 0, _ => 0
  | count+1, h =>
    (read (fun i : Fin 8 => byte ⟨count*8+i.val,by omega⟩) 8 (Nat.le_refl 8) <<< (count*64)) +
      chunks byte count (Nat.le_of_succ_le h)

theorem chunks_ofFn (byte : Fin (n*8) → UInt8) (count : Nat) (h : count ≤ n) :
    chunks byte count h = PackedArithmetic.read (Vector.ofFn byte) count h := by
  induction count with
  | zero => rfl
  | succ count ih =>
    simp only [chunks,PackedArithmetic.read,ih,read_ofFn,PackedArithmetic.slice,Vector.get_ofFn]

@[inline] def toFin (byte : Fin (n*8) → UInt8) : Fin (2^((n*8)*8)) :=
  ⟨chunks byte n (Nat.le_refl n),by
    rw [chunks_ofFn,PackedArithmetic.read_eq]
    exact ByteArithmetic.read_lt (Vector.ofFn byte)⟩

theorem toFin_eq (byte : Fin (n*8) → UInt8) :
    toFin byte = FiniteProbability.bytesFinEquiv (n*8) (Vector.ofFn byte) := by
  apply Fin.ext
  change chunks byte n (Nat.le_refl n) = _
  rw [chunks_ofFn,PackedArithmetic.read_eq,ByteArithmetic.read_eq,ByteArithmetic.bitNat_eq]

end G1Release.Submission.FlatArithmetic
