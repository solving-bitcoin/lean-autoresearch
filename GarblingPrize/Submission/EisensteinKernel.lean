import GarblingPrize.Submission.G1Endomorphism

namespace GarblingPrize.Submission.EisensteinKernel

open GarblingPrize.Protected

/-!
# Checked constants behind the 7-ary BN254 GLV decomposition

The endomorphism eigenvalue is a root of `X² + X + 1` modulo the scalar
order.  The two short integers below generate its Eisenstein kernel: their
Eisenstein norm is exactly the BN254 scalar modulus, and `a + b * lambda`
vanishes modulo that modulus.
-/

def lambda : Nat :=
  4407920970296243842393367215006156084916469457145843978461

def kernelA : Nat :=
  147946756881789319010696353538189108491

def kernelB : Nat :=
  9931322734385697763

abbrev ScalarRing := ZMod scalarFieldModulus

/-- The GLV eigenvalue is a nontrivial cube root of unity modulo `r`. -/
theorem lambda_root :
    (lambda : ScalarRing) ^ 2 + (lambda : ScalarRing) + 1 = 0 := by
  decide

/-- The short Eisenstein vector is in the kernel of evaluation at `lambda`. -/
theorem kernel_relation :
    (kernelA : ScalarRing) + (kernelB : ScalarRing) * (lambda : ScalarRing) = 0 := by
  decide

/-- Its norm is exactly the scalar modulus, so the kernel has the required
index rather than merely containing a convenient relation. -/
theorem kernel_norm :
    kernelA * kernelA - kernelA * kernelB + kernelB * kernelB =
      scalarFieldModulus := by
  norm_num [kernelA, kernelB, scalarFieldModulus]

/-- Ninety norm-seven digits cannot name every scalar residue. -/
theorem ninety_digits_insufficient :
    7 ^ 90 < scalarFieldModulus := by
  norm_num [scalarFieldModulus]

/-- Ninety-one norm-seven digits have enough raw cardinality. -/
theorem ninety_one_digits_sufficient :
    scalarFieldModulus ≤ 7 ^ 91 := by
  norm_num [scalarFieldModulus]

end GarblingPrize.Submission.EisensteinKernel
