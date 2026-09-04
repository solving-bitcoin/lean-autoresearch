import GarblingPrize.Submission.CompactPrivacy

namespace GarblingPrize.Submission

open GarblingPrize.Protected

/-- The official computable balanced-ternary/threaded-mask construction. -/
def scheme : Scheme BN254.bn254 := CompactScheme.scheme

/-- Exact worst-case serialized artifact size: 161 maps, 11 affine tables per
map, 254 significant-coordinate rows per table, and 64 bytes per row. -/
def claimedBytes : Nat := CompactScheme.claimedBytes

theorem claimedBytes_eq : claimedBytes = 28564459 := rfl

theorem claimedBytes_lt_30MB : claimedBytes < 30000000 := by decide

theorem validClaimed : ValidCandidate scheme claimedBytes :=
  CompactPrivacy.valid

end GarblingPrize.Submission

namespace GarblingPrize.Benchmark

theorem candidate : GarblingPrize.Protected.RankedClaim
    GarblingPrize.Submission.scheme GarblingPrize.Submission.claimedBytes :=
  GarblingPrize.Submission.validClaimed

end GarblingPrize.Benchmark
