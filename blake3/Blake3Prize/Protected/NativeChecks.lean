import Blake3Prize.Protected.Runner

namespace Blake3Prize.Protected.NativeChecks

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

/-- Exercise carry propagation, overflow, XOR, every boundary rotation,
oversized literals, arbitrary word indices, and mixed bit/word expressions. -/
def wordFixture (lastWord : Bool) : Candidate :=
  let x := WordExpr.inputWord (if lastWord then 15 else 0)
  let y := WordExpr.inputWord 1
  let w : Vector WordExpr 8 := #v[
    WordExpr.add x y, WordExpr.add x (WordExpr.literal (2^32-1)),
    WordExpr.xor x y, WordExpr.rotate x 0, WordExpr.rotate x 1,
    WordExpr.rotate x 31, WordExpr.rotate x 32,
    WordExpr.rotate (WordExpr.xor x (WordExpr.literal (2^40+17))) 63]
  Vector.ofFn fun i =>
    let bit := BitExpr.wordBit w[i.val / 32] ⟨i.val % 32, by omega⟩
    if lastWord then bit + BitExpr.inputExpr ⟨i.val, by omega⟩ else bit

def runChecks : IO Unit := do
  let references ← messages.mapM fun message => do
    let bytes := referenceBytes message
    let bits := bytesOfBits (reference (inputOfBytes message))
    unless bytes == bits do throw (IO.userError "Clean byte/bit packing mismatch")
    pure <| Lean.Json.mkObj [
      ("input", Lean.toJson (message.map UInt8.toNat).toArray),
      ("digest", Lean.toJson bytes.toArray)]
  let fixtures := #[false,true].map fun mode =>
    let candidate := wordFixture mode
    let expected := messages.map fun message =>
      (bytesOfBits (candidate.map (BitExpr.eval (inputOfBytes message)))).toArray
    Lean.Json.mkObj [
      ("circuit", circuitJson candidate (artifactBytes (Lowering.compile candidate))),
      ("expected", Lean.toJson expected)]
  IO.println (Lean.Json.mkObj [
    ("references", Lean.toJson references), ("wordFixtures", Lean.toJson fixtures)]).compress

end Blake3Prize.Protected.NativeChecks
