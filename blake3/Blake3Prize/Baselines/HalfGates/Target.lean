import Blake3Prize.Baselines.HalfGates.Morphism
import Blake3Prize.Baselines.HalfGates.Lowering
import Blake3Prize.Baselines.HalfGates.HalfGate
import Blake3Prize.Baselines.HalfGates.Codec

namespace Blake3Prize.Baselines.HalfGates
open Blake3Prize.Protected

abbrev Candidate := Vector BitExpr 256

def Correct (candidate : Candidate) : Prop :=
  ∀ input : Input, candidate.map (BitExpr.eval input) = reference input

/-- An optional expression-level certificate, not the challenge acceptance claim.
Cryptographic security relies on its documented random-oracle assumptions;
it is not an exact information-theoretic theorem about 32-byte keys. -/
structure ExpressionCertificate (candidate : Candidate) (maxBytes : Nat) : Prop where
  correct : Correct candidate
  artifact_bound : artifactBytes (Lowering.compile candidate) ≤ maxBytes

end Blake3Prize.Baselines.HalfGates
