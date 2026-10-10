import WotsLamport.Submission.Sharing

namespace WotsLamport.Submission

/-- Fermat-prime reduction using two power-of-two operations and subtraction.
It is proposed separately from the current executable pending kernel checking. -/
def reduceMachineField (x : UInt32) : UInt32 :=
  let low := x % 65536
  let high := x / 65536
  if low < high then low + 65537 - high else low - high

theorem fermat_reduction_nat (n : Nat) (bound : n < 4294967296) :
    (if n % 65536 < n / 65536 then n % 65536 + 65537 - n / 65536
      else n % 65536 - n / 65536) = n % 65537 := by
  split
  next h =>
    have hb : n % 65536 + 65537 - n / 65536 < 65537 := by omega
    have he : n = (n / 65536 - 1)*65537 + (n % 65536 + 65537 - n / 65536) := by omega
    calc
      _ = ((n / 65536 - 1)*65537 + (n % 65536 + 65537 - n / 65536)) % 65537 := by
        simp [Nat.add_mod, Nat.mod_eq_of_lt hb]
      _ = n % 65537 := congrArg (fun a => a % 65537) he.symm
  next h =>
    have hb : n % 65536 - n / 65536 < 65537 := by omega
    have he : n = (n / 65536)*65537 + (n % 65536 - n / 65536) := by omega
    calc
      _ = ((n / 65536)*65537 + (n % 65536 - n / 65536)) % 65537 := by
        simp [Nat.add_mod, Nat.mod_eq_of_lt hb]
      _ = n % 65537 := congrArg (fun a => a % 65537) he.symm

theorem reduceMachineField_toNat (x : UInt32) :
    (reduceMachineField x).toNat = x.toNat % prime := by
  have lowNat : (x % 65536).toNat = x.toNat % 65536 := by rw [UInt32.toNat_mod]; rfl
  have highNat : (x / 65536).toNat = x.toNat / 65536 := by rw [UInt32.toNat_div]; rfl
  have bound : x.toNat < 4294967296 := x.toNat_lt_size
  have hn := fermat_reduction_nat x.toNat bound
  dsimp only [reduceMachineField]
  by_cases h : x % 65536 < x / 65536
  · have hnat : x.toNat % 65536 < x.toNat / 65536 := by
      simpa only [UInt32.lt_iff_toNat_lt, lowNat, highNat] using h
    rw [if_pos h, UInt32.toNat_sub, UInt32.toNat_add, lowNat, highNat]
    rw [if_pos hnat] at hn
    change (4294967296 - x.toNat / 65536 +
      ((x.toNat % 65536 + 65537) % 4294967296)) % 4294967296 = x.toNat % 65537
    rw [← hn]
    omega
  · have hnat : ¬ x.toNat % 65536 < x.toNat / 65536 := by
      simpa only [UInt32.lt_iff_toNat_lt, lowNat, highNat] using h
    rw [if_neg h, UInt32.toNat_sub, lowNat, highNat]
    rw [if_neg hnat] at hn
    change (4294967296 - x.toNat / 65536 + x.toNat % 65536) % 4294967296 = x.toNat % 65537
    rw [← hn]
    omega

end WotsLamport.Submission
