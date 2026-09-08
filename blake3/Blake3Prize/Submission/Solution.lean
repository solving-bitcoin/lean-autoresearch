import Blake3Prize.Submission.RomSecurity

namespace Blake3Prize.Submission
/-- Four-row construction with exact correctness and a bounded-query ROM certificate. -/
def entry : Option Blake3Prize.Protected.Candidate :=
  some Blake3Prize.Submission.RomSecurity.candidate
end Blake3Prize.Submission
