import WotsLamport.Submission.Sharing

namespace WotsLamport.Submission
open SecretRelease WotsLamport.Protected

-- Keep unfolding equations owned by the submission namespace.
theorem digitBit_eq (i : Fin 256) (d : Nat) :
    digitBit i d = d.testBit (bitInNibble i) := rfl

theorem bitInNibble_eq (i : Fin 256) : bitInNibble i = i.val % 4 := rfl

theorem bitChain_val_eq (i : Fin 256) :
    (bitChain i).val = 2*(i.val/8) + (if i.val%8 < 4 then 1 else 0) := rfl

/-- Low and high nibbles preserve the corresponding little-endian bit index. -/
theorem nibble_bit (n r : Nat) (hr : r < 8) :
    (if r < 4 then n % 16 else n / 16).testBit (r % 4) = n.testBit r := by
  by_cases h : r < 4
  · simpa [h, Nat.mod_eq_of_lt h] using Nat.testBit_mod_two_pow n 4 r
  · have hm : r % 4 + 4 = r := by omega
    simpa [h, hm] using Nat.testBit_div_two_pow (n := 4) n (r % 4)

/-- The WOTS high-then-low digit order agrees with the Lamport output codec's
byte-major, least-significant-bit-first ordering for every message and wire. -/
theorem message_digit_bit (m : Message) (i : Fin 256) :
    digitBit i (messageDigit m (bitChain i)) = (outputCodec.encode m)[i.val] := by
  change digitBit i (messageDigit m (bitChain i)) =
    (Vector.ofFn (fun j : Fin 256 => m[j.val/8].toNat.testBit (j.val%8)))[i.val]
  simp only [Vector.getElem_ofFn]
  conv_rhs => rw [← nibble_bit _ _ (Nat.mod_lt i.val (by decide : 0 < 8))]
  have hm : i.val % 8 % 4 = i.val % 4 := by omega
  have hl : (2 * (i.val / 8) + 1) / 2 = i.val / 8 := by omega
  have hh : (2 * (i.val / 8)) / 2 = i.val / 8 := by omega
  have pl : (2 * (i.val / 8) + 1) % 2 = 1 := by omega
  have ph : (2 * (i.val / 8)) % 2 = 0 := by omega
  by_cases h : i.val % 8 < 4 <;>
    simp [digitBit_eq, bitInNibble_eq, messageDigit, bitChain_val_eq, h, hm, hl, hh, pl, ph]

theorem target_digit_bit (m : Message) (i : Fin 256) :
    digitBit i (encodeWord m (targetChain i)) = (outputCodec.encode m)[i.val] := by
  unfold encodeWord
  split
  · exact message_digit_bit m i
  · next h => exact False.elim (h (bitChain i).isLt)

theorem selected_holds (m : Message) (i : Fin 256) :
    holds i (outputCodec.encode m)[i.val] (encodeWord m (targetChain i)) = true := by
  simp [holds, target_digit_bit]

theorem opposite_does_not_hold (m : Message) (i : Fin 256) :
    holds i (!(outputCodec.encode m)[i.val]) (encodeWord m (targetChain i)) = false := by
  simp [holds, target_digit_bit]

end WotsLamport.Submission
