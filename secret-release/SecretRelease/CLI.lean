import SecretRelease.Runtime
import SecretRelease.NativeHash
import Lean.Data.Json.FromToJson
import Lean.Data.Json.Printer

/-! Generated entrypoints delegate only to these fixed role-specific commands.
The C SHA-256 profile is an explicit, unproved instantiation of the ideal oracle. -/
namespace SecretRelease.CLI
open Lean

private def fail (message : String) : IO α := throw (IO.userError message)
private def require (value : Option α) (message : String) : IO α :=
  match value with | some x => pure x | none => fail message
private def write (path : String) (value : Option ByteArray) : IO Unit := do
  IO.FS.writeBinFile path (← require value "invalid encoding or rejected evaluation")

private def keyMetadata (w : KeyWire d) : Json := Json.mkObj [
  ("kind", toJson w.kind), ("count", toJson w.count)]

def description (w : WireFormat c) (entry : Option (Candidate c)) : Json :=
  let status := match entry with
    | none => "missing"
    | some candidate => if candidate.certificate.isSome then "certified" else "uncertified"
  Json.mkObj [
    ("wireVersion", toJson (1 : Nat)), ("challenge", toJson w.identity),
    ("status", toJson status),
    ("claimedBytes", toJson (entry.map (·.maxBytes))),
    ("certifiedBytes", toJson (entry.bind fun v => v.certified.map (·.maxBytes))),
    ("randomnessBytes", toJson (entry.map (·.scheme.randomnessBytes))),
    ("privateBits", toJson c.privateCodec.width), ("inputBits", toJson c.inputCodec.width),
    ("inputKeys", keyMetadata w.inputs), ("outputKeys", keyMetadata w.outputs),
    ("referenceCodec", toJson w.output.isSome),
    ("securityProfile", toJson "classical-bounded-query-rom-v1"),
    ("maxOracleQueries", toJson c.rom.maxQueries), ("oracleOutputBits", toJson (256 : Nat)),
    ("failureBound", toJson "challenge.rom.error(q)"),
    ("nativePrimitive", toJson "trusted-C-SHA-256"),
    ("implementationBridge", toJson "SHA-256: heuristic / unproved")]

private def roundtrip (codec : ByteCodec A) (bytes : ByteArray) : Option ByteArray :=
  codec.decode bytes |>.map codec.encode

/-- No candidate is required for input encoding or protected reference tools. -/
def run (w : WireFormat c) (entry : Option (Candidate c)) (tool : String)
    (args : List String) : IO UInt32 := do
  match tool, args with
  | "challenge", ["describe"] => IO.println (description w entry).compress
  | "challenge", ["bound", queryCount] =>
    let q ← require queryCount.toNat? "invalid query count"
    let error := c.rom.error q
    IO.println (Json.mkObj [("queries",toJson q), ("admissible",toJson (decide (q ≤ c.rom.maxQueries))),
      ("numerator",toJson error.num), ("denominator",toJson error.den)]).compress
  | "challenge", ["sha256", src, dst] =>
    IO.FS.writeBinFile dst ⟨(nativeHash (← IO.FS.readBinFile src)).toArray⟩
  | "challenge", ["reference", p, x, dst] =>
    write dst (Runtime.reference w (← IO.FS.readBinFile p) (← IO.FS.readBinFile x))
  | "challenge", ["release", value, keys, dst] =>
    write dst (Runtime.release w nativeHash (← IO.FS.readBinFile value) (← IO.FS.readBinFile keys))
  | "challenge", ["expected", p, x, keys, dst] =>
    let rawP ← IO.FS.readBinFile p
    let rawX ← IO.FS.readBinFile x
    let rawKeys ← IO.FS.readBinFile keys
    write dst (do
      let p ← c.privateCodec.bytes.decode rawP
      let x ← c.inputCodec.bytes.decode rawX
      let keys ← w.outputs.codec.decode rawKeys
      pure (c.outputs.reveal nativeHash keys (c.reference p x)))
  | "challenge", ["roundtrip", kind, src, dst] =>
    let bytes ← IO.FS.readBinFile src
    write dst (match kind with
      | "private" => roundtrip c.privateCodec.bytes bytes
      | "input" => roundtrip c.inputCodec.bytes bytes
      | "input-keys" => roundtrip w.inputs.codec bytes
      | "output-keys" => roundtrip w.outputs.codec bytes
      | "output" => w.output.bind fun out => roundtrip out bytes
      | _ => none)
  | "encode", [src, keys, known, active] =>
    let input ← IO.FS.readBinFile src
    let selected ← require (Runtime.encode w nativeHash input (← IO.FS.readBinFile keys))
      "invalid canonical input or input keys"
    IO.FS.writeBinFile known input
    IO.FS.writeBinFile active selected
  | "garble", [coins, p, ik, ok, dst] =>
    let some candidate := entry | fail "no candidate implementation"
    let result ← require (Runtime.garble w candidate.scheme nativeHash
      (← IO.FS.readBinFile coins) (← IO.FS.readBinFile p)
      (← IO.FS.readBinFile ik) (← IO.FS.readBinFile ok)) "invalid coins, private value, or keys"
    unless result.size ≤ candidate.maxBytes do fail "artifact exceeds candidate's claimed bound"
    IO.FS.writeBinFile dst result
    IO.println (Json.mkObj [("artifactBytes", toJson result.size)]).compress
  | "evaluate", [artifact, known, active, dst] =>
    let some candidate := entry | fail "no candidate implementation"
    let artifact ← IO.FS.readBinFile artifact
    unless artifact.size ≤ candidate.maxBytes do fail "artifact exceeds candidate's claimed bound"
    write dst (Runtime.evaluate candidate.scheme nativeHash artifact
      (← IO.FS.readBinFile known) (← IO.FS.readBinFile active))
  | _, _ => fail "invalid tool or arguments (see the shared wire protocol)"
  return 0

/-- Four bundle filenames share one compiled object graph, with fixed dispatch. -/
def main (w : WireFormat c) (entry : Option (Candidate c)) (args : List String) : IO UInt32 := do
  let name := (← IO.appPath).fileName.getD ""
  if ["garble", "encode", "evaluate", "challenge"].contains name then run w entry name args
  else match args with
    | tool :: rest => run w entry tool rest
    | [] => fail "expected garble, encode, evaluate, or challenge"
end SecretRelease.CLI
