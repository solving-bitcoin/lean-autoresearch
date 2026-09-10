import G1Release.Submission.G1CertificateBase

namespace G1Release.Submission.G1GeneratorCertificateBase

open G1Release.Math
open G1CertificateBase

noncomputable section

/-- Standard BN254 G1 generator `(1,2)`. -/
def generator : Checkpoint := affine 1 2 (by decide)

def generatorPoint : BN254.G1 := semantic generator

theorem generatorPoint_ne_zero : generatorPoint ≠ 0 := by
  unfold generatorPoint semantic generator affine
  exact WeierstrassCurve.Affine.Point.some_ne_zero _

end

end G1Release.Submission.G1GeneratorCertificateBase
