import Blake3Prize.Tests.HalfGates.Runner

open Blake3Prize.Tests.HalfGates Blake3Prize.Submission.HalfGates in
def main : IO Unit :=
  exportCircuit referenceExpressions (artifactBytes (Lowering.compile referenceExpressions))
