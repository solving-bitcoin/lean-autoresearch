import Blake3Prize.Baselines.HalfGates.Runner

open Blake3Prize.Baselines.HalfGates in
def main : IO Unit :=
  exportCircuit referenceExpressions (artifactBytes (Lowering.compile referenceExpressions))
