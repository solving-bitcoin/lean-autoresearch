import G1Release.Submission.CosetROMSecurity
import G1Release.Submission.CosetFastGarble

namespace G1Release.Submission.CosetFastCertified

abbrev scheme := CosetFastGarble.scheme

def certificate : SecretRelease.Certificate scheme CosetScheme.claimedBytes := by
  change SecretRelease.Certificate CosetFastGarble.scheme CosetScheme.claimedBytes
  rw [CosetFastGarble.scheme_eq, CosetFastSampler.scheme_eq]
  exact CosetROMSecurity.certificate

end G1Release.Submission.CosetFastCertified
