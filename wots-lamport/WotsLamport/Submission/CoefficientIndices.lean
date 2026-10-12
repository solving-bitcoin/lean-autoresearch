import WotsLamport.Submission.CoinBlocks

namespace WotsLamport.Submission
open SecretRelease

abbrev CoefficientSlot := Fin 512 × Fin 16 × Fin 1023

def coefficientIndex (slot : CoefficientSlot) : Fin coefficientCount :=
  ⟨(slot.1.val*16+slot.2.1.val)*1023+slot.2.2.val, by
    have hi := slot.1.isLt
    have hl := slot.2.1.isLt
    have hd := slot.2.2.isLt
    unfold coefficientCount
    omega⟩

/-- Different label/limb/degree addresses use different 32-byte coin blocks. -/
theorem coefficientIndex_injective : Function.Injective coefficientIndex := by
  intro a b he
  have hai := a.1.isLt
  have hal := a.2.1.isLt
  have had := a.2.2.isLt
  have hbi := b.1.isLt
  have hbl := b.2.1.isLt
  have hbd := b.2.2.isLt
  have hv := congrArg Fin.val he
  change (a.1.val*16+a.2.1.val)*1023+a.2.2.val =
    (b.1.val*16+b.2.1.val)*1023+b.2.2.val at hv
  apply Prod.ext
  · apply Fin.ext
    omega
  · apply Prod.ext <;> apply Fin.ext <;> omega

def labelIndex (wire : Fin 256) (value : Bool) : Fin 512 :=
  ⟨2*wire.val+(if value then 1 else 0), by
    have hw := wire.isLt
    cases value <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;> omega⟩

theorem labelIndex_injective : Function.Injective (fun p : Fin 256 × Bool => labelIndex p.1 p.2) := by
  intro a b he
  rcases a with ⟨a, av⟩
  rcases b with ⟨b, bv⟩
  have hv := congrArg Fin.val he
  cases av <;> cases bv <;> simp only [labelIndex, Bool.false_eq_true, ite_false, ite_true] at hv
  · have hab : a = b := Fin.ext (by omega)
    rw [hab]
  · omega
  · omega
  · have hab : a = b := Fin.ext (by omega)
    rw [hab]

def nonconstantDegree (value : Bool) (degree : Fin (threshold value-1)) : Fin 1023 :=
  ⟨degree.val, by
    have hd := degree.isLt
    cases value <;> simp [threshold] at hd <;> omega⟩

theorem polynomial_coefficient_block (coins : Bytes randomnessBytes) (label : Label)
    (wire : Fin 256) (limb : Fin 16) (value : Bool) (degree : Fin (threshold value-1)) :
    (polynomial (ByteArray.mk coins.toArray) label wire.val limb.val value)[degree.val+1]! =
      readLE (ByteArray.mk (coefficientBlock coins
        (coefficientIndex (labelIndex wire value, limb, nonconstantDegree value degree))).toArray)
        0 32 % prime := by
  have hbelow : degree.val+1 < threshold value := by have hd := degree.isLt; omega
  let slot : CoefficientSlot := (labelIndex wire value, limb, nonconstantDegree value degree)
  rw [getElem!_pos _ (degree.val+1) (by rw [polynomial_length]; exact hbelow)]
  simp only [polynomial, List.getElem_map, List.getElem_range,
    if_neg (by omega : degree.val+1 ≠ 0)]
  have hread := coefficient_block_read coins (coefficientIndex slot)
  simpa only [slot, coefficientIndex, labelIndex, nonconstantDegree,
    Nat.add_sub_assoc (by omega : 1 ≤ degree.val+1), Nat.add_sub_cancel] using
    congrArg (fun n : Nat => n % prime) hread.symm

theorem allocated_coefficient_bias_arithmetic :
    (coefficientCount : ℚ) / 2^256 < 1 / 2^233 := by
  norm_num [coefficientCount]

end WotsLamport.Submission
