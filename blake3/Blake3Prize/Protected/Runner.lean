import Blake3Prize.Protected.Target
import Lean

namespace Blake3Prize.Protected

/-- This bridge is elaborated before submission imports. It emits only public
circuit topology and a byte claim; no per-instance values exist at this stage. -/
def circuitJson (candidate : Candidate) (claimedBytes : Nat) : Lean.Json :=
  let circuit := Lowering.compile candidate
  Lean.Json.mkObj [
    ("schemaVersion", Lean.toJson (1 : Nat)),
    ("inputBits", Lean.toJson (512 : Nat)),
    ("outputBits", Lean.toJson (256 : Nat)),
    ("gates", Lean.toJson circuit.gates),
    ("outputs", Lean.toJson circuit.outputs.toArray),
    ("claimedBytes", Lean.toJson claimedBytes)]

def exportCircuit (candidate : Candidate) (claimedBytes : Nat) : IO Unit :=
  IO.println (circuitJson candidate claimedBytes).compress

end Blake3Prize.Protected
