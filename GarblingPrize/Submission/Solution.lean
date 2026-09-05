import GarblingPrize.Submission.GLVCompactPrivacy

namespace GarblingPrize.Submission

open GarblingPrize.Protected

/-- Norm-seven GLV garbling.  The certified endomorphism `phi` acts as the
Eisenstein unit `omega`, so 91 digits in `0, ±1, ±omega, ±omega²` suffice in
radix `3 + omega`.  Eleven affine tables implement each complete selector map.
All free masks are derived from distinct protected internal-oracle addresses. -/
def scheme : Scheme BN254.bn254 := GLVCompactScheme.scheme

/-- Exact worst-case serialized artifact size: 91 maps × 11 affine tables ×
127 row pairs × 127 bytes.  Each pair packs four 254-bit ciphertexts. -/
def claimedBytes : Nat := GLVCompactScheme.claimedBytes

theorem claimedBytes_eq : claimedBytes = 16145129 := rfl

theorem claimedBytes_lt_17MB : claimedBytes < 17000000 := by decide

/-- Replacing 161 ternary maps with 91 GLV maps saves exactly 70 map encodings. -/
theorem bytes_saved : 28564459 - claimedBytes = 12419330 := by decide

theorem claimedBytes_lt_30MB : claimedBytes < 30000000 := by decide

theorem validClaimed : ValidCandidate scheme claimedBytes :=
  GLVCompactPrivacy.valid

end GarblingPrize.Submission

namespace GarblingPrize.Benchmark

theorem candidate : GarblingPrize.Protected.RankedClaim
    GarblingPrize.Submission.scheme GarblingPrize.Submission.claimedBytes :=
  GarblingPrize.Submission.validClaimed

end GarblingPrize.Benchmark
