import Blake3Prize.Protected.NativeHash
import Lean.Data.Json.FromToJson
import Lean.Data.Json.Printer

namespace Blake3Prize.Protected.NativeChecks
open Blake3Prize.Protected

def messages : Array (Vector UInt8 64) :=
  #[Vector.replicate 64 0, Vector.replicate 64 255,
    Vector.ofFn (fun i => UInt8.ofNat i.val),
    Vector.ofFn (fun i => if i.val % 2 = 0 then 0x55 else 0xaa)] ++
  (Array.range 512).map fun bit => Vector.ofFn fun i =>
    UInt8.ofNat (if i.val = bit / 8 then 2^(bit % 8) else 0)

def inputOfBytes (message : Vector UInt8 64) : Input :=
  Vector.ofFn fun i => bitOfBool (message[i.val / 8].toNat.testBit (i.val % 8))

def bytesOfBits (bits : Output) : Vector Nat 32 :=
  Vector.ofFn fun i => (List.finRange 8).foldl
    (fun n j => n + bits[8*i.val+j.val].val * 2^j.val) 0

def runChecks : IO Unit := do
  let references ← messages.mapM fun message => do
    let bytes := referenceBytes message
    let bits := bytesOfBits (reference (inputOfBytes message))
    unless bytes == bits do throw (IO.userError "Clean byte/bit packing mismatch")
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

end Blake3Prize.Protected.NativeChecks
