import Blake3Prize.Protected.Target

namespace Blake3Prize.Submission
open Protected

/-- Clean's word-level compression specialized to one unkeyed 64-byte root.
The protected lowerer shares identical expressions and propagates constants. -/
def candidate : Candidate := referenceExpressions

def claimedBytes : Nat := artifactBytes (Lowering.compile candidate)

theorem validClaimed : ValidCandidate candidate claimedBytes where
  correct := referenceExpressions_correct
  artifact_bound := Nat.le_refl _

end Blake3Prize.Submission
