import Blake3Prize.Submission.HalfGatesTarget
import Lean

namespace Blake3Prize.Tests.HalfGates
open Blake3Prize.Protected Blake3Prize.Submission.HalfGates

/-- This optional author test imports the candidate and emits only public
circuit topology and a byte claim; no per-instance values exist at this stage. -/
def circuitJson (candidate : Blake3Prize.Submission.HalfGates.Candidate) (claimedBytes : Nat) : Lean.Json :=
  let circuit := Lowering.compile candidate
  Lean.Json.mkObj [
    ("schemaVersion", Lean.toJson (1 : Nat)),
    ("inputBits", Lean.toJson (512 : Nat)),
    ("outputBits", Lean.toJson (256 : Nat)),
    ("gates", Lean.toJson circuit.gates),
    ("outputs", Lean.toJson circuit.outputs.toArray),
    ("claimedBytes", Lean.toJson claimedBytes)]

def exportCircuit (candidate : Blake3Prize.Submission.HalfGates.Candidate) (claimedBytes : Nat) : IO Unit :=
  IO.println (circuitJson candidate claimedBytes).compress

end Blake3Prize.Tests.HalfGates
