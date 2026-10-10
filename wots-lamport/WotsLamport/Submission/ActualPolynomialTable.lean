import WotsLamport.Submission.PolynomialTableLaw
import WotsLamport.Submission.PolynomialEncoding
import WotsLamport.Submission.FieldTableLaw

namespace WotsLamport.Submission
open SecretRelease

def actualFieldTable (coins : Bytes randomnessBytes) : Fin coefficientCount → ZMod 65537 :=
  fun index => fieldBlock (coefficientBlock coins index)

/-- The coefficient list used by the executable is exactly the corresponding
prefix of the globally indexed, independently allocated field table. -/
theorem actual_polynomial_table (coins : Bytes randomnessBytes) (labels : Fin 256 → Pair)
    (slot : PolynomialSlot) :
    fieldPolynomial (polynomial (ByteArray.mk coins.toArray)
      ((labels slot.1).get slot.2.1) slot.1.val slot.2.2.val slot.2.1) =
    Shamir.coefficientPolynomial (labelLimb labels slot)
      (Shamir.coefficientPrefix (nonconstant_count_bound slot.2.1)
        (polynomialTableEquiv (actualFieldTable coins) slot)) := by
  rw [actual_polynomial_as_coefficients]
  congr 1
  funext degree
  rw [polynomial_coefficient_block coins ((labels slot.1).get slot.2.1)
    slot.1 slot.2.2 slot.2.1 degree]
  change ((readLE (ByteArray.mk (coefficientBlock coins
      (coefficientIndex (labelIndex slot.1 slot.2.1, slot.2.2,
        nonconstantDegree slot.2.1 degree))).toArray) 0 32 % prime : Nat) : ZMod 65537) =
    fieldBlock (coefficientBlock coins
      (coefficientIndex (labelIndex slot.1 slot.2.1, slot.2.2,
        nonconstantDegree slot.2.1 degree)))
  apply Fin.ext
  change (_ % prime) % 65537 = _ % 65537
  simp only [prime, Nat.mod_mod]

end WotsLamport.Submission
