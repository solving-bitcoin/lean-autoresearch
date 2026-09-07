import G1Release.Submission.CosetFastCertified

namespace G1Release.Submission

/-- Norm-seven GLV decomposition uses 91 maps. Translating into a quadratic
extension-field coset reduces each map to eight affine Fp tables. Each table
stores 254 one-ciphertext rows with a public hint bit and one correction word:
91 * 8 * (254 + 1) * 32 = 5,940,480 bytes.
The certificate proves correctness and both protected ROM games for uniformly
sampled distinct 32-byte input labels and a finite private byte tape, including
the modular-sampling error. The executable sampler is proved equivalent. -/
def entry : Option (SecretRelease.Candidate G1Release.Protected.challenge) :=
  some ⟨CosetFastCertified.scheme, CosetScheme.claimedBytes, some CosetFastCertified.certificate⟩

end G1Release.Submission
