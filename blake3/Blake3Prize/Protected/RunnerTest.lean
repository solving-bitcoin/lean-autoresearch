import Blake3Prize.Protected.Wire

/-! Deliberately insecure generic transport fixture: discloses every label.
Its custom framing and coins must all count towards the artifact size. -/
namespace Blake3Prize.Protected.RunnerTest
open SecretRelease

def fixture : SecretRelease.Scheme challenge where
  Artifact := ByteArray
  randomnessBytes := 7
  garble := fun _ coins _ ik ok => wire.inputs.codec.encode ik ++ wire.outputs.codec.encode ok ++ ⟨coins.toArray⟩
  encode := fun b => ⟨#[76,69,65]⟩ ++ b
  decode := fun b => if b.extract 0 3 == ⟨#[76,69,65]⟩ then some (b.extract 3 b.size) else none
  evaluate := fun h b x active => do
    let ik ← wire.inputs.codec.decode (b.extract 0 32768)
    let ok ← wire.outputs.codec.decode (b.extract 32768 49152)
    if active == challenge.inputs.reveal h ik x then
      some (challenge.outputs.reveal h ok (reference x)) else none

def entry : Option (SecretRelease.Candidate challenge) := some ⟨fixture,49162,none⟩
end Blake3Prize.Protected.RunnerTest
