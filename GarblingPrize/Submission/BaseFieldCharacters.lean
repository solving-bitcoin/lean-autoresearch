import GarblingPrize.Protected.Target
import GarblingPrize.Submission.PowCertificate

namespace GarblingPrize.Submission.BaseFieldCharacters

/-!
# Character certificates for the official RCB solution

These are not properties required by the challenge contract. They are
submission-owned facts used to prove totality of the official projective map.
-/

open GarblingPrize.Protected
open PowCertificate

def modulus : Nat := baseFieldModulus

def witness : Nat := 3

namespace Q2

set_option maxRecDepth 3072 in
theorem properPower :
    (witness : ZMod modulus) ^ ((modulus - 1) / 2) ≠ 1 := by
  let bits := binaryDigits ((modulus - 1) / 2)
  apply pow_ne_one_of_certificate modulus witness ((modulus - 1) / 2)
    (residue modulus witness bits) bits
  · decide
  · rfl
  · decide

end Q2

namespace Q3

set_option maxRecDepth 3072 in
theorem properPower :
    (witness : ZMod modulus) ^ ((modulus - 1) / 3) ≠ 1 := by
  let bits := binaryDigits ((modulus - 1) / 3)
  apply pow_ne_one_of_certificate modulus witness ((modulus - 1) / 3)
    (residue modulus witness bits) bits
  · decide
  · rfl
  · decide

end Q3

end GarblingPrize.Submission.BaseFieldCharacters
