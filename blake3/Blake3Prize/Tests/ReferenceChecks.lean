import Blake3Prize.Tests.ReferenceFixtures
import SecretRelease.NativeHash
import Lean.Data.Json.FromToJson
import Lean.Data.Json.Printer

namespace Blake3Prize.Tests.ReferenceChecks
open Blake3Prize.Protected
open SecretRelease (nativeHash)

def messages : Array (Vector UInt8 64) :=
  #[Vector.replicate 64 0, Vector.replicate 64 255,
    Vector.ofFn (fun i => UInt8.ofNat i.val),
    Vector.ofFn (fun i => if i.val % 2 = 0 then 0x55 else 0xaa)] ++
  (Array.range 512).map fun bit => Vector.ofFn fun i =>
    UInt8.ofNat (if i.val = bit / 8 then 2^(bit % 8) else 0)

def runChecks : IO Unit := do
  let references ← messages.mapM fun message => do
    let bytes := referenceBytes message
    let bits := (reference message).map UInt8.toNat
    unless bytes == bits do throw (IO.userError "Clean reference byte packing mismatch")
    pure <| Lean.Json.mkObj [
      ("input", Lean.toJson (message.map UInt8.toNat).toArray),
      ("digest", Lean.toJson bytes.toArray)]
  let hashes := (#[0,1,3,55,56,63,64,65,127,128,129,256] : Array Nat).map fun n =>
    let bytes : ByteArray := ⟨(Array.range n).map UInt8.ofNat⟩
    Lean.Json.mkObj [
      ("input", Lean.toJson (bytes.data.map UInt8.toNat)),
      ("digest", Lean.toJson ((nativeHash bytes).map UInt8.toNat).toArray)]
  IO.println (Lean.Json.mkObj [
    ("references", Lean.toJson references), ("hashes", Lean.toJson hashes)]).compress

end Blake3Prize.Tests.ReferenceChecks
