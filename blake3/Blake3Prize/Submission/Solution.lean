import Blake3Prize.Submission.HalfGatesScheme

namespace Blake3Prize.Submission
/-- Runnable baseline. A complete shared ROM certificate is still absent. -/
def entry : Option Blake3Prize.Protected.Candidate :=
  some Blake3Prize.Submission.HalfGates.Executable.candidate
end Blake3Prize.Submission
