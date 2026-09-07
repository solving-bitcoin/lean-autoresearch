import G1Release.Submission.ByteArithmetic

set_option maxRecDepth 4096
set_option maxHeartbeats 300000

namespace G1Release.Submission.PackedArithmetic
open SecretRelease

def slice (bytes : Bytes width) (offset count : Nat) (h : offset+count ≤ width) : Bytes count :=
  Vector.ofFn fun i => bytes.get ⟨offset+i.val,by omega⟩

theorem read_add (bytes : Bytes width) (m n : Nat) (h : m+n ≤ width) :
    ByteArithmetic.read bytes (m+n) h =
      (ByteArithmetic.read (slice bytes m n h) n (Nat.le_refl n) <<< (m*8)) +
        ByteArithmetic.read bytes m (by omega) := by
  simp only [ByteArithmetic.read_eq, ByteArithmetic.bitNat]
  rw [ByteArithmetic.ofBits_split (m*8) (n*8) ((m+n)*8) (by omega)]
  have hh :
      (fun i : Fin (n*8) => (bytes.get ⟨(m*8+i.val)/8,by omega⟩).toNat.testBit ((m*8+i.val)%8)) =
      (fun i : Fin (n*8) => ((slice bytes m n h).get ⟨i.val/8,by omega⟩).toNat.testBit (i.val%8)) := by
    funext i
    simp only [slice, Vector.get_ofFn]
    have hd : (m*8+i.val)/8 = m+i.val/8 := by omega
    have hm : (m*8+i.val)%8 = i.val%8 := by omega
    simp only [hd,hm]
  rw [hh, Nat.shiftLeft_eq]
  ac_rfl

/-- Accumulate eight-byte machine-sized chunks before shifting into the
large integer. This avoids allocating a large integer for every byte. -/
def read (bytes : Bytes (n*8)) : (count : Nat) → count ≤ n → Nat
  | 0, _ => 0
  | count+1, h =>
    let chunk := slice bytes (count*8) 8 (by omega)
    (ByteArithmetic.read chunk 8 (Nat.le_refl 8) <<< (count*64)) +
      read bytes count (Nat.le_of_succ_le h)

theorem read_eq (bytes : Bytes (n*8)) (count : Nat) (h : count ≤ n) :
    read bytes count h = ByteArithmetic.read bytes (count*8) (by omega) := by
  induction count with
  | zero => rfl
  | succ count ih =>
    rw [read, ih]
    have hs := read_add bytes (count*8) 8 (by omega)
    have hc : (count+1)*8 = count*8+8 := by omega
    simpa only [hc, Nat.mul_assoc] using hs.symm

def toFin (bytes : Bytes (n*8)) : Fin (2^((n*8)*8)) :=
  ⟨read bytes n (Nat.le_refl n),by rw [read_eq]; exact ByteArithmetic.read_lt bytes⟩

theorem toFin_eq (bytes : Bytes (n*8)) : toFin bytes = ByteArithmetic.toFin bytes := by
  apply Fin.ext
  exact read_eq bytes n (Nat.le_refl n)

end G1Release.Submission.PackedArithmetic
