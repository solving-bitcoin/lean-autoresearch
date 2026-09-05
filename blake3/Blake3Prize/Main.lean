import Blake3Prize.Protected.Runner
import Blake3Prize.Submission.Solution

def main (args : List String) : IO UInt32 :=
  Blake3Prize.Protected.Runner.run Blake3Prize.Submission.entry args
