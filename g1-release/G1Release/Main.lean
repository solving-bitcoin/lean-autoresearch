import G1Release.Protected.Runner
import G1Release.Submission.Solution

def main (args : List String) : IO UInt32 :=
  G1Release.Protected.Runner.run G1Release.Submission.entry args
