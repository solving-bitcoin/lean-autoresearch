import Blake3Prize.Protected.Target
import Blake3Prize.Protected.RunnerIO
import Lean.Data.Json.FromToJson
import Lean.Data.Json.Printer

namespace Blake3Prize.Protected.Runner

private def describe (entry : Option CertifiedScheme) : Lean.Json :=
  match entry with
  | none => Lean.Json.mkObj [("status", Lean.toJson "unranked")]
  | some c => Lean.Json.mkObj [
      ("status", Lean.toJson "certified"),
      ("claimedBytes", Lean.toJson c.maxBytes),
      ("randomnessBytes", Lean.toJson c.scheme.randomnessBytes),
      ("securityProfile", Lean.toJson (match c.profile with | .classicalBoundedQueryROM => "classical-bounded-query-rom-v1")),
      ("maxOracleQueries", Lean.toJson ROM.maxQueries),
      ("oracleOutputBits", Lean.toJson (256 : Nat)),
      ("failureBound", Lean.toJson "(q + 1) / 2^128"),
      ("implementationBridge", Lean.toJson "SHA-256: heuristic / unproved")]

/-- Only a certificate-bearing entry can reach the submission execution path. -/
def run (entry : Option CertifiedScheme) (args : List String) : IO UInt32 := do
  if args = ["describe"] then
    IO.println (describe entry).compress
    return 0
  let some c := entry | throw (IO.userError "no certified submission")
  runScheme c.scheme c.maxBytes args

end Blake3Prize.Protected.Runner
