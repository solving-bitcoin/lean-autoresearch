import G1Release.Submission.WordReader

namespace G1Release.Submission.WordChunks
open SecretRelease

@[specialize] def read (byte : Fin (n*8) → UInt8) : (count : Nat) → count ≤ n → Nat
  | 0, _ => 0
  | count+1, h =>
    ((WordReader.word (fun i : Fin 8 => byte ⟨count*8+i.val,by omega⟩)).toNat <<< (count*64)) +
      read byte count (Nat.le_of_succ_le h)

theorem read_eq (byte : Fin (n*8) → UInt8) (count : Nat) (h : count ≤ n) :
    read byte count h = FlatArithmetic.chunks byte count h := by
  induction count with
  | zero => rfl
  | succ count ih => simp only [read,FlatArithmetic.chunks,WordReader.word_nat,ih]

@[inline] def toFin (byte : Fin (n*8) → UInt8) : Fin (2^((n*8)*8)) :=
  ⟨read byte n (Nat.le_refl n),by
    rw [read_eq]
    exact (FlatArithmetic.toFin byte).isLt⟩

theorem toFin_eq (byte : Fin (n*8) → UInt8) : toFin byte = FlatArithmetic.toFin byte := by
  apply Fin.ext
  exact read_eq byte n (Nat.le_refl n)

end G1Release.Submission.WordChunks
