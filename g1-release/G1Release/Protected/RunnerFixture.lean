import G1Release.Protected.Runner

/-! Deliberately INSECURE transport test: it publishes the private parameters,
all label pairs, and coins. There is no certificate or ranked entry for it. -/
namespace G1Release.Protected
open SecretRelease

def insecureFixture : Scheme challenge where
  Artifact := ByteArray
  randomnessBytes := 3
  garble := fun _ coins p keys _ =>
    bitsToBytes (n := 97) (privateCodec.encode p) ++
      pack ((List.finRange 512).flatMap fun i => [(keys i).get false, (keys i).get true]) ++
      ⟨coins.toArray⟩
  encode := id
  decode := some
  evaluate := fun _ bytes a active => do
    let p ← (bytesToBits 97 (bytes.extract 0 97)).bind privateCodec.decode
    let expected := pack ((List.finRange 512).map fun i =>
      Vector.ofFn fun j => bytes[97 + 32*(2*i.val + if (inputCodec.encode a)[i.val] then 1 else 0) + j.val]!)
    if active == expected then pure (encodeOutput (reference p a)) else none

end G1Release.Protected

def main (args : List String) : IO UInt32 :=
  G1Release.Protected.Runner.runScheme G1Release.Protected.insecureFixture 32868 args
