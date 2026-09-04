import GarblingPrize.Submission.G1OrderCertShard15
import GarblingPrize.Submission.G1LambdaCertShard11
import GarblingPrize.Submission.G1Endomorphism
import GarblingPrize.Submission.EisensteinKernel

namespace GarblingPrize.Submission.G1GeneratorCertificates

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

open GarblingPrize.Protected
open G1CertificateBase
open G1GeneratorCertificateBase

noncomputable section

def orderTail : List Bool :=
  G1OrderCertShard00.bits ++
    G1OrderCertShard01.bits ++
    G1OrderCertShard02.bits ++
    G1OrderCertShard03.bits ++
    G1OrderCertShard04.bits ++
    G1OrderCertShard05.bits ++
    G1OrderCertShard06.bits ++
    G1OrderCertShard07.bits ++
    G1OrderCertShard08.bits ++
    G1OrderCertShard09.bits ++
    G1OrderCertShard10.bits ++
    G1OrderCertShard11.bits ++
    G1OrderCertShard12.bits ++
    G1OrderCertShard13.bits ++
    G1OrderCertShard14.bits ++
    G1OrderCertShard15.bits

theorem orderTail_exponent :
    orderTail.foldl exponentStep 1 = scalarFieldModulus := by
  decide

theorem orderTail_point :
    orderTail.foldl (pointStep generatorPoint) generatorPoint = 0 := by
  unfold orderTail
  simp only [List.foldl_append]
  rw [G1OrderCertShard00.transition,
    G1OrderCertShard01.transition,
    G1OrderCertShard02.transition,
    G1OrderCertShard03.transition,
    G1OrderCertShard04.transition,
    G1OrderCertShard05.transition,
    G1OrderCertShard06.transition,
    G1OrderCertShard07.transition,
    G1OrderCertShard08.transition,
    G1OrderCertShard09.transition,
    G1OrderCertShard10.transition,
    G1OrderCertShard11.transition,
    G1OrderCertShard12.transition,
    G1OrderCertShard13.transition,
    G1OrderCertShard14.transition,
    G1OrderCertShard15.transition]
  rfl

/-- The standard point `(1,2)` is killed by the BN254 scalar modulus. -/
theorem generator_nsmul_scalarFieldModulus :
    scalarFieldModulus • generatorPoint = 0 := by
  calc
    scalarFieldModulus • generatorPoint =
        orderTail.foldl exponentStep 1 • generatorPoint := by
      rw [orderTail_exponent]
    _ = orderTail.foldl (pointStep generatorPoint) generatorPoint := by
      exact (fold_pointStep_eq_nsmul generatorPoint orderTail 1).symm
    _ = 0 := orderTail_point

def lambdaTail : List Bool :=
  G1LambdaCertShard00.bits ++
    G1LambdaCertShard01.bits ++
    G1LambdaCertShard02.bits ++
    G1LambdaCertShard03.bits ++
    G1LambdaCertShard04.bits ++
    G1LambdaCertShard05.bits ++
    G1LambdaCertShard06.bits ++
    G1LambdaCertShard07.bits ++
    G1LambdaCertShard08.bits ++
    G1LambdaCertShard09.bits ++
    G1LambdaCertShard10.bits ++
    G1LambdaCertShard11.bits

theorem lambdaTail_exponent :
    lambdaTail.foldl exponentStep 1 = EisensteinKernel.lambda := by
  decide

theorem lambdaTail_point :
    lambdaTail.foldl (pointStep generatorPoint) generatorPoint =
      semantic G1LambdaCertShard11.endpoint := by
  unfold lambdaTail
  simp only [List.foldl_append]
  rw [G1LambdaCertShard00.transition,
    G1LambdaCertShard01.transition,
    G1LambdaCertShard02.transition,
    G1LambdaCertShard03.transition,
    G1LambdaCertShard04.transition,
    G1LambdaCertShard05.transition,
    G1LambdaCertShard06.transition,
    G1LambdaCertShard07.transition,
    G1LambdaCertShard08.transition,
    G1LambdaCertShard09.transition,
    G1LambdaCertShard10.transition,
    G1LambdaCertShard11.transition]

theorem lambda_endpoint_eq_phi_generator :
    semantic G1LambdaCertShard11.endpoint =
      G1Endomorphism.phi generatorPoint := by
  simp [G1LambdaCertShard11.endpoint, semantic, affine,
    generatorPoint, generator,
    G1Endomorphism.phi, G1Endomorphism.beta]
  congr 1 <;> norm_num

/-- The coordinate endomorphism has eigenvalue `lambda` on `(1,2)`. -/
theorem generator_nsmul_lambda :
    EisensteinKernel.lambda • generatorPoint =
      G1Endomorphism.phi generatorPoint := by
  calc
    EisensteinKernel.lambda • generatorPoint =
        lambdaTail.foldl exponentStep 1 • generatorPoint := by
      rw [lambdaTail_exponent]
    _ = lambdaTail.foldl (pointStep generatorPoint) generatorPoint := by
      exact (fold_pointStep_eq_nsmul generatorPoint lambdaTail 1).symm
    _ = semantic G1LambdaCertShard11.endpoint :=
      lambdaTail_point
    _ = G1Endomorphism.phi generatorPoint := lambda_endpoint_eq_phi_generator

end

end GarblingPrize.Submission.G1GeneratorCertificates
