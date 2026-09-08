import Blake3Prize.Submission.HalfGatesMorphism
import Blake3Prize.Submission.HalfGatesLowering
import Blake3Prize.Submission.HalfGatesHalfGate
import Blake3Prize.Submission.HalfGatesCodec

namespace Blake3Prize.Submission.HalfGates
open Blake3Prize.Protected

abbrev Candidate := Vector BitExpr 256

def Correct (candidate : Candidate) : Prop :=
  ∀ input : Input, candidate.map (BitExpr.eval input) =
    ((SecretRelease.Codec.byteVector 32).encode (reference input)).map bitOfBool

/-- An optional expression-level certificate, not the challenge acceptance claim.
Cryptographic security relies on its documented random-oracle assumptions;
it is not an exact information-theoretic theorem about 32-byte keys. -/
structure ExpressionCertificate (candidate : Candidate) (maxBytes : Nat) : Prop where
  correct : Correct candidate
  artifact_bound : artifactBytes (Lowering.compile candidate) ≤ maxBytes

end Blake3Prize.Submission.HalfGates
