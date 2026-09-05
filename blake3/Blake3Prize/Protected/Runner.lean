import Blake3Prize.Protected.Target
import Lean

namespace Blake3Prize.Protected

/-- This bridge is elaborated before submission imports. It emits only public
circuit topology and a byte claim; no per-instance values exist at this stage. -/
def exportCircuit (candidate : Candidate) (claimedBytes : Nat) : IO Unit := do
  let circuit := Lowering.compile candidate
  let output := Lean.Json.mkObj [
    ("schemaVersion", Lean.toJson (1 : Nat)),
    ("inputBits", Lean.toJson (512 : Nat)),
    ("outputBits", Lean.toJson (256 : Nat)),
    ("gates", Lean.toJson circuit.gates),
    ("outputs", Lean.toJson circuit.outputs.toArray),
    ("claimedBytes", Lean.toJson claimedBytes)]
  IO.println output.compress

end Blake3Prize.Protected
