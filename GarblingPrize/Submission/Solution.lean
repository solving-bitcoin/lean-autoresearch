import GarblingPrize.Submission.GLVHintPrivacy
import GarblingPrize.Submission.CosetAffineMap

namespace GarblingPrize.Submission

open GarblingPrize.Protected

/-- Norm-seven GLV garbling with exactly balanced one-hint affine tables.
A private coin modulo 4p balances the two field endpoints of each binary pad.
Equal-size fibers prove exact privacy while allowing one ciphertext per row. -/
def scheme : Scheme BN254.bn254 := GLVHintScheme.scheme

/-- 91 maps × 11 tables × (254 rows + one constant) × 32 bytes. -/
def claimedBytes : Nat := GLVHintScheme.claimedBytes

theorem claimedBytes_eq : claimedBytes = 8168160 := rfl

theorem claimedBytes_lt_8_2MB : claimedBytes < 8200000 := by decide

theorem bytes_saved : 28564459 - claimedBytes = 20396299 := by decide

theorem validClaimed : ValidCandidate scheme claimedBytes := GLVHintPrivacy.valid

end GarblingPrize.Submission

namespace GarblingPrize.Benchmark

theorem candidate : GarblingPrize.Protected.RankedClaim
    GarblingPrize.Submission.scheme GarblingPrize.Submission.claimedBytes :=
  GarblingPrize.Submission.validClaimed

end GarblingPrize.Benchmark
