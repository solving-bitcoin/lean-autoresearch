import G1Release.Submission.DutyFreeCertified

namespace G1Release.Submission

/-- Duty-free nibble bridges are shared across the 91 norm-seven GLV maps.
Each of the 728 affine Fp outputs uses 64 additive joins and one decoder.
The 128 bridges contain 16 independent keys with four ciphertexts per key:
(128 * 16 * 4 + 91 * 8 * 65) * 32 = 1,776,384 bytes.
The full shared ROM certificate includes finite-label guessing, the existing
finite-coin sampling bound, and an explicit 2^-240 raw-pad tail bound. -/
def entry : Option (SecretRelease.Candidate G1Release.Protected.challenge) :=
  some DutyFreeCertified.entry

end G1Release.Submission
