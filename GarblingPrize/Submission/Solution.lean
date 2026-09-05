import GarblingPrize.Submission.CosetPrivacy

namespace GarblingPrize.Submission

open GarblingPrize.Protected

/-- Norm-seven GLV garbling through a non-rational curve coset. Four affine
extension-field openings become eight exactly balanced base-field tables.
The coset's x-coordinate rationally recovers the full original group point. -/
def scheme : Scheme BN254.bn254 := CosetScheme.scheme

/-- 91 maps × 8 tables × (254 rows + one constant) × 32 bytes. -/
def claimedBytes : Nat := CosetScheme.claimedBytes

theorem claimedBytes_eq : claimedBytes = 5940480 := rfl

theorem claimedBytes_lt_6MB : claimedBytes < 6000000 := by decide

theorem claimedBytes_lt_8_2MB : claimedBytes < 8200000 := by decide

theorem bytes_saved : 28564459 - claimedBytes = 22623979 := by decide

theorem validClaimed : ValidCandidate scheme claimedBytes := CosetPrivacy.valid

end GarblingPrize.Submission

namespace GarblingPrize.Benchmark

theorem candidate : GarblingPrize.Protected.RankedClaim
    GarblingPrize.Submission.scheme GarblingPrize.Submission.claimedBytes :=
  GarblingPrize.Submission.validClaimed

end GarblingPrize.Benchmark
