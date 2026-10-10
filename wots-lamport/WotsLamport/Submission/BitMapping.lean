import WotsLamport.Submission.Sharing

namespace WotsLamport.Submission
open SecretRelease WotsLamport.Protected

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
  simp only [outputCodec, Codec.byteVector, Vector.getElem_ofFn]
  conv_rhs => rw [← nibble_bit _ _ (Nat.mod_lt i.val (by decide : 0 < 8))]
  have hm : i.val % 8 % 4 = i.val % 4 := by omega
  have hl : (2 * (i.val / 8) + 1) / 2 = i.val / 8 := by omega
  have hh : (2 * (i.val / 8)) / 2 = i.val / 8 := by omega
  have pl : (2 * (i.val / 8) + 1) % 2 = 1 := by omega
  have ph : (2 * (i.val / 8)) % 2 = 0 := by omega
  by_cases h : i.val % 8 < 4 <;>
    simp [digitBit, bitInNibble, messageDigit, bitChain, h, hm, hl, hh, pl, ph]

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
