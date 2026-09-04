import CompPoly.Fields.PrattCertificate
import GarblingPrize.Protected.BN254

namespace GarblingPrize.Protected.BN254Certificates

/-!
# BN254 base-field certificate

CompPoly's Pratt tactic generates a kernel-checked Lucas/Pratt certificate for
the base modulus. This protected module establishes only the primality needed
to give the concrete `ZMod` target its field structure. Character facts used
by one particular projective formula belong to that submission.
-/

theorem baseFieldModulus_prime : baseFieldModulus.Prime := by
  unfold baseFieldModulus
  pratt
end GarblingPrize.Protected.BN254Certificates
