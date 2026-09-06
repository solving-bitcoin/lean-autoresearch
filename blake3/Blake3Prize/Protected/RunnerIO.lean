import Blake3Prize.Protected.NativeHash
import Lean.Data.Json.FromToJson
import Lean.Data.Json.Printer

-- Compile filesystem and label transport without the probability-theory
-- import closure. The certificate gate remains in Protected.Runner.
namespace Blake3Prize.Protected.Runner

private def readExact (path : String) (n : Nat) : IO ByteArray := do
  let bytes ← IO.FS.readBinFile path
  unless bytes.size = n do throw (IO.userError s!"expected {n} bytes: {path}")
  pure bytes

private def labelAt (bytes : ByteArray) (index : Nat) : Label :=
  Vector.ofFn fun j => bytes[index * 32 + j.val]!

private def flatten {n : Nat} (labels : Vector Label n) : ByteArray :=
  ⟨labels.toArray.foldl (fun bytes label => bytes ++ label.toArray) #[]⟩

/-- Fixed I/O for a total scheme. The submission executable uses only the
certificate-gated `run` wrapper in `Protected.Runner`. The separate protected
plumbing test calls this function with a deliberately uncertified fixture. -/
def runScheme (s : Scheme) (maxBytes : Nat) (args : List String) : IO UInt32 := do
  match args with
  | ["garble", coinsPath, pairsPath, artifactPath] =>
    let coinsBytes ← readExact coinsPath s.randomnessBytes
    let coins : Randomness s.randomnessBytes := Vector.ofFn fun i => coinsBytes[i.val]!
    let pairs ← readExact pairsPath (768*2*32)
    let inputs : InputLabelPairs := fun i b => labelAt pairs (2*i.val + if b then 1 else 0)
    let outputs : OutputLabelPairs := fun i b => labelAt pairs (2*(512+i.val) + if b then 1 else 0)
    for i in List.finRange 512 do
      if inputs i false == inputs i true then throw (IO.userError "input pair is not distinct")
    for i in List.finRange 256 do
      if outputs i false == outputs i true then throw (IO.userError "output pair is not distinct")
    let artifact := s.garbleBytes nativeHash coins inputs outputs
    unless artifact.size ≤ maxBytes do throw (IO.userError "serialized artifact exceeds bound")
    IO.FS.writeBinFile artifactPath artifact
    IO.println (Lean.Json.mkObj [("artifactBytes", Lean.toJson artifact.size)]).compress
    return 0
  | ["evaluate", artifactPath, messagePath, activePath, outputPath] =>
    let artifact ← IO.FS.readBinFile artifactPath
    unless artifact.size ≤ maxBytes do throw (IO.userError "serialized artifact exceeds bound")
    let message ← readExact messagePath 64
    let input := inputFromBytes (Vector.ofFn fun i => message[i.val]!)
    let active ← readExact activePath (512*32)
    let inputs : ActiveInputLabels := Vector.ofFn fun i => labelAt active i.val
    let some outputs := s.evaluateBytes nativeHash artifact input inputs
      | throw (IO.userError "evaluation rejected the artifact or active labels")
    IO.FS.writeBinFile outputPath (flatten outputs)
    return 0
  | _ => throw (IO.userError "expected describe, garble, or evaluate")

end Blake3Prize.Protected.Runner
