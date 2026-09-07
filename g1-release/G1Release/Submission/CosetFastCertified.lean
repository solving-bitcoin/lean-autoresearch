import G1Release.Submission.CosetROMSecurity
import G1Release.Submission.CosetFastSampler

namespace G1Release.Submission.CosetFastCertified

abbrev scheme := CosetFastSampler.scheme

def certificate : SecretRelease.Certificate scheme CosetScheme.claimedBytes := by
  change SecretRelease.Certificate CosetFastSampler.scheme CosetScheme.claimedBytes
  rw [CosetFastSampler.scheme_eq]
  exact CosetROMSecurity.certificate

end G1Release.Submission.CosetFastCertified
