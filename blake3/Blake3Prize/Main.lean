import Blake3Prize.Protected.Runner
import Blake3Prize.Submission.Solution

def main : IO Unit :=
  Blake3Prize.Protected.exportCircuit
    Blake3Prize.Submission.candidate Blake3Prize.Submission.claimedBytes
