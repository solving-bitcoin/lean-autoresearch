import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import GarblingPrize.Submission.G1GeneratorCertificates
import GarblingPrize.Submission.G1Cardinality
import GarblingPrize.Submission.G1Endomorphism
import GarblingPrize.Submission.EisensteinKernel

namespace GarblingPrize.Submission.G1Eigenvalue

open GarblingPrize.Protected

noncomputable section

abbrev Point := BN254.G1

private theorem scalarFieldModulus_prime : scalarFieldModulus.Prime := by
  simpa [scalarFieldModulus, _root_.BN254.scalarFieldSize] using
    _root_.BN254.ScalarField_is_prime

local instance scalarPrimeFact : Fact scalarFieldModulus.Prime :=
  ⟨scalarFieldModulus_prime⟩

/-- Every protected G1 point is an integral multiple of the checked
standard generator. -/
theorem exists_generator_zsmul (point : Point) :
    ∃ multiplier : Int,
      multiplier • G1GeneratorCertificateBase.generatorPoint = point := by
  have hmem := mem_zmultiples_of_prime_card
    G1Cardinality.pointCardinality
    G1GeneratorCertificateBase.generatorPoint_ne_zero (g' := point)
  exact AddSubgroup.mem_zmultiples_iff.mp hmem

/-- The coordinate automorphism `(x,y) |-> (beta*x,y)` is scalar
multiplication by the certified GLV eigenvalue on every G1 point. -/
theorem phi_eq_lambda_nsmul (point : Point) :
    G1Endomorphism.phi point = EisensteinKernel.lambda • point := by
  obtain ⟨multiplier, hpoint⟩ := exists_generator_zsmul point
  rw [← hpoint]
  change G1Endomorphism.phiHom
      (multiplier • G1GeneratorCertificateBase.generatorPoint) = _
  rw [G1Endomorphism.phiHom.map_zsmul]
  change multiplier • G1Endomorphism.phi
      G1GeneratorCertificateBase.generatorPoint = _
  rw [← G1GeneratorCertificates.generator_nsmul_lambda]
  rw [← natCast_zsmul G1GeneratorCertificateBase.generatorPoint
      EisensteinKernel.lambda,
    ← natCast_zsmul
      (multiplier • G1GeneratorCertificateBase.generatorPoint)
      EisensteinKernel.lambda,
    ← mul_zsmul, ← mul_zsmul, Int.mul_comm]

/-- The scalar modulus annihilates every protected G1 point. -/
theorem scalarFieldModulus_nsmul (point : Point) :
    scalarFieldModulus • point = 0 := by
  rw [← G1Cardinality.pointCardinality]
  exact card_nsmul_eq_zero'

end

end GarblingPrize.Submission.G1Eigenvalue
