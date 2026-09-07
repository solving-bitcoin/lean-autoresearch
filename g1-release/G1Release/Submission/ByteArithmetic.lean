import G1Release.Submission.FiniteProbability
import G1Release.Protected.Codecs

set_option maxRecDepth 4096
set_option maxHeartbeats 200000

namespace G1Release.Submission.ByteArithmetic
open SecretRelease G1Release.Protected

/-- Split a little-endian bit string into its low and high portions. -/
theorem ofBits_append (m n : Nat) (bits : Fin (m+n) → Bool) :
    Nat.ofBits bits = 2^m * Nat.ofBits (fun i : Fin n => bits ⟨m+i.val,by omega⟩) +
      Nat.ofBits (fun i : Fin m => bits ⟨i.val,by omega⟩) := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_two_pow_mul_add _ (Nat.ofBits_lt_two_pow _)]
  by_cases hj : j < m
  · rw [if_pos hj, Nat.testBit_ofBits_lt bits j (by omega), Nat.testBit_ofBits_lt _ j hj]
  · rw [if_neg hj]
    by_cases ht : j < m+n
    · rw [Nat.testBit_ofBits_lt bits j ht, Nat.testBit_ofBits_lt _ (j-m) (by omega)]
      apply congrArg bits
      apply Fin.ext
      dsimp only
      omega
    · rw [Nat.testBit_ofBits_ge bits j (by omega), Nat.testBit_ofBits_ge _ (j-m) (by omega)]

theorem ofBits_split (m n width : Nat) (hlen : width = m+n) (bits : Fin width → Bool) :
    Nat.ofBits bits = 2^m * Nat.ofBits (fun i : Fin n => bits ⟨m+i.val,by omega⟩) +
      Nat.ofBits (fun i : Fin m => bits ⟨i.val,by omega⟩) := by
  subst width
  exact ofBits_append m n bits

/-- Read one byte per step, without expanding a block into 512 booleans. -/
def read (bytes : SecretRelease.Bytes n) : (count : Nat) → count ≤ n → Nat
  | 0, _ => 0
  | count+1, h =>
      ((bytes.get ⟨count,h⟩).toNat <<< (8*count)) + read bytes count (Nat.le_of_succ_le h)

def bitNat (bytes : SecretRelease.Bytes n) (count : Nat) (h : count ≤ n) : Nat :=
  Nat.ofBits fun i : Fin (count*8) =>
    (bytes.get ⟨i.val/8,by omega⟩).toNat.testBit (i.val%8)

theorem read_eq (bytes : SecretRelease.Bytes n) (count : Nat) (h : count ≤ n) :
    read bytes count h = bitNat bytes count h := by
  induction count with
  | zero => rfl
  | succ count ih =>
    rw [read, ih]
    unfold bitNat
    conv_rhs => rw [ofBits_split (count*8) 8 ((count+1)*8) (by omega)]
    dsimp only
    have hh :
        (fun i : Fin 8 => (bytes.get ⟨(count*8+i.val)/8,by omega⟩).toNat.testBit ((count*8+i.val)%8)) =
        (fun i : Fin 8 => (bytes.get ⟨count,h⟩).toNat.testBit i.val) := by
      funext i
      have hd : (count*8+i.val)/8 = count := by omega
      have hm : (count*8+i.val)%8 = i.val := by omega
      simp only [hd,hm]
    rw [hh, Nat.ofBits_testBit, Nat.mod_eq_of_lt (show (bytes.get ⟨count,h⟩).toNat < 2^8 from
      (bytes.get ⟨count,h⟩).toFin.isLt)]
    rw [Nat.shiftLeft_eq]
    ac_rfl

theorem bitNat_eq (bytes : SecretRelease.Bytes n) :
    bitNat bytes n (Nat.le_refl n) = (FiniteProbability.bytesFinEquiv n bytes).val := by
  change Nat.ofBits _ = Nat.ofBits (Vector.ofFn _).get
  have hf {width : Nat} (f : Fin width → Bool) : (Vector.ofFn f).get = f := by
    funext i
    simp only [Vector.get_ofFn]
  rw [hf]
  rfl

theorem read_lt (bytes : SecretRelease.Bytes n) : read bytes n (Nat.le_refl n) < 2^(n*8) := by
  rw [read_eq, bitNat_eq]
  exact (FiniteProbability.bytesFinEquiv n bytes).isLt

def toFin (bytes : SecretRelease.Bytes n) : Fin (2^(n*8)) :=
  ⟨read bytes n (Nat.le_refl n),read_lt bytes⟩

theorem toFin_eq (bytes : SecretRelease.Bytes n) : toFin bytes = FiniteProbability.bytesFinEquiv n bytes := by
  apply Fin.ext
  exact (read_eq bytes n (Nat.le_refl n)).trans (bitNat_eq bytes)

end G1Release.Submission.ByteArithmetic
