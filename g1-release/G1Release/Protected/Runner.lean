import G1Release.Protected.Target
import G1Release.Protected.NativeHash
import Lean.Data.Json.FromToJson
import Lean.Data.Json.Printer

namespace G1Release.Protected.Runner
open SecretRelease

private def readExact (path : String) (n : Nat) : IO ByteArray := do
  let bytes ← IO.FS.readBinFile path
  unless bytes.size = n do throw (IO.userError s!"expected {n} bytes: {path}")
  pure bytes

private def labelAt (bytes : ByteArray) (index : Nat) : Label :=
  Vector.ofFn fun j => bytes[index * 32 + j.val]!

private def parseKeys (bytes : ByteArray) : Option (Fin 512 → Pair) :=
  let pairs := fun i : Fin 512 => (labelAt bytes (2*i.val), labelAt bytes (2*i.val+1))
  if h : ∀ i, (pairs i).1 ≠ (pairs i).2 then
    some fun i => ⟨pairs i, h i⟩
  else none

/-- Fixed transport for a scheme; `run` below gates the submission on its full
certificate. This helper also permits separate, explicitly insecure I/O tests. -/
def runScheme (s : Scheme challenge) (maxBytes : Nat) (args : List String) : IO UInt32 := do
  match args with
  | ["garble", coinsPath, privatePath, pairsPath, artifactPath] =>
    let rawCoins ← readExact coinsPath s.randomnessBytes
    let coins : Bytes s.randomnessBytes := Vector.ofFn fun i => rawCoins[i.val]!
    let privateBytes ← readExact privatePath 97
    let some p := (bytesToBits 97 privateBytes).bind privateCodec.decode
      | throw (IO.userError "invalid canonical private point/scalar")
    let pairs ← readExact pairsPath (512*2*32)
    let some keys := parseKeys pairs | throw (IO.userError "input pair is not distinct")
    let artifact := s.garbleBytes nativeHash coins p keys ()
    unless artifact.size ≤ maxBytes do throw (IO.userError "serialized artifact exceeds bound")
    IO.FS.writeBinFile artifactPath artifact
    IO.println (Lean.Json.mkObj [("artifactBytes", Lean.toJson artifact.size)]).compress
    return 0
  | ["evaluate", artifactPath, inputPath, activePath, outputPath] =>
    let artifact ← IO.FS.readBinFile artifactPath
    unless artifact.size ≤ maxBytes do throw (IO.userError "serialized artifact exceeds bound")
    let rawInput ← readExact inputPath 64
    let some a := (bytesToBits 64 rawInput).bind inputCodec.decode
      | throw (IO.userError "invalid canonical finite-affine input point")
    let active ← readExact activePath (512*32)
    let some output := s.evaluateBytes nativeHash artifact a active
      | throw (IO.userError "evaluation rejected the artifact or active labels")
    let some _ := (bytesToBits 65 output).bind outputCodec.decode
      | throw (IO.userError "evaluation returned a noncanonical point")
    IO.FS.writeBinFile outputPath output
    return 0
  | _ => throw (IO.userError "expected describe, garble, or evaluate")

/-- No executable submission path exists without all shared proof obligations. -/
def run (entry : Option CertifiedScheme) (args : List String) : IO UInt32 := do
  if args = ["describe"] then
    let description := match entry with
      | none => Lean.Json.mkObj [("status", Lean.toJson "unranked")]
      | some c => Lean.Json.mkObj [
        ("status", Lean.toJson "certified"),
        ("claimedBytes", Lean.toJson c.maxBytes),
        ("randomnessBytes", Lean.toJson c.scheme.randomnessBytes),
        ("securityProfile", Lean.toJson "classical-bounded-query-rom-v1"),
        ("maxOracleQueries", Lean.toJson challenge.rom.maxQueries),
        ("oracleOutputBits", Lean.toJson (256 : Nat)),
        ("failureBound", Lean.toJson "(q + 1) / 2^128"),
        ("implementationBridge", Lean.toJson "SHA-256: heuristic / unproved")]
    IO.println description.compress
    return 0
  let some c := entry | throw (IO.userError "no certified submission")
  runScheme c.scheme c.maxBytes args

end G1Release.Protected.Runner
