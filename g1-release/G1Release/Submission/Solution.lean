import G1Release.Submission.FastCertified

namespace G1Release.Submission

/-- The 161 balanced-ternary maps use sampled offsets constrained
by their Horner sum, nonzero projective scales, and independent mask fibers.
The certificate proves both protected ROM games for the actual finite coin
tape, including the bounded modular-sampling bias. Caching preserves every
serialized byte. The artifact contains
161 * 11 * 254 * 2 * 32 = 28,789,376 bytes. -/
def entry : Option (SecretRelease.Candidate G1Release.Protected.challenge) :=
  some ⟨FastCertified.scheme, Scheme.claimedBytes, some FastCertified.certificate⟩

end G1Release.Submission
