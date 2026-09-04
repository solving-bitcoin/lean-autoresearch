import GarblingPrize.Protected.Runner
import GarblingPrize.Submission.Solution

/-! This is intentionally only a fully qualified bridge. All runner logic was
elaborated in the protected module before the untrusted submission import. -/

def main (args : List String) : IO UInt32 :=
  GarblingPrize.Protected.Runner.main
    GarblingPrize.Submission.scheme
    GarblingPrize.Submission.claimedBytes
    args
