import WotsLamport.Submission.BitMapping
import Mathlib.Algebra.BigOperators.Fin

namespace WotsLamport.Submission
open WotsLamport.Protected

/-- Direct data digits contribute their ordinary sum; checksum digits use
weights 1, 8, and 64. The complete weighted codeword sum is always 960. -/
theorem encoded_weighted_sum (m : Message) :
    (∑ j : Fin 67, weight j * encodeWord m j) = 960 := by
  have first : (∑ j : Fin 64,
      weight (Fin.castAdd 3 j) * encodeWord m (Fin.castAdd 3 j)) = messageSum m := by
    unfold messageSum
    apply Finset.sum_congr rfl
    intro j _
    have h64 : (Fin.castAdd 3 j).val < 64 := j.isLt
    have h65 : (Fin.castAdd 3 j).val ≠ 65 := by omega
    have h66 : (Fin.castAdd 3 j).val ≠ 66 := by omega
    simp [weight, encodeWord, h64, h65, h66]
  have last : (∑ j : Fin 3,
      weight (Fin.natAdd 64 j) * encodeWord m (Fin.natAdd 64 j)) =
      checksum m % 8 + 8 * ((checksum m / 8) % 8) + 64 * (checksum m / 64) := by
    simp [Fin.sum_univ_succ, weight, encodeWord, Nat.add_assoc]
  change (∑ j : Fin (64+3), weight j * encodeWord m j) = 960
  rw [Fin.sum_univ_add, first, last]
  simpa [Nat.add_assoc] using checksum_weighted m

set_option maxRecDepth 8192 in
theorem maximum_weighted_sum : (∑ j : Fin 67, weight j * maximum j) = 1983 := by
  decide

/-- The exact T used by the sharing construction, for all 256-bit messages.
This is a weighted remaining-depth identity, not a fixed ordinary digit sum. -/
theorem remaining_weighted_sum (m : Message) :
    (∑ j : Fin 67, weight j * (maximum j - encodeWord m j)) = 1023 := by
  have he : (∑ j : Fin 67, weight j * (maximum j - encodeWord m j)) +
      (∑ j : Fin 67, weight j * encodeWord m j) =
      (∑ j : Fin 67, weight j * maximum j) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [← Nat.mul_add, Nat.sub_add_cancel (encodeWord_le m j)]
  rw [encoded_weighted_sum, maximum_weighted_sum] at he
  omega

end WotsLamport.Submission
