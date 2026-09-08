import G1Release.Submission.DutyFreeCorrect

/-! Correctness and size are independent of the finite coin sampler. -/
namespace G1Release.Submission.DutyFreeSampler
open SecretRelease G1Release.Protected
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

theorem correct_of_parts {c : Challenge} (s : SecretRelease.Scheme c)
    (hd : ∀ a, s.decode (s.encode a) = some a)
    (hc : ∀ hash coins hidden keys outputs input,
      s.evaluate hash (s.garble hash coins hidden keys outputs) input (c.inputs.reveal hash keys input) =
        some (c.outputs.reveal hash outputs (c.reference hidden input))) : Correct s := by
  intro hash coins hidden keys outputs input
  unfold SecretRelease.Scheme.evaluateBytes SecretRelease.Scheme.garbleBytes
  rw [hd, Option.bind_some]
  exact hc hash coins hidden keys outputs input

theorem bound_of_encoder {c : Challenge} (s : SecretRelease.Scheme c) (bytes : Nat)
    (hb : ∀ a, (s.encode a).size = bytes) : ArtifactBound s bytes :=
  fun hash coins hidden keys outputs => (hb (s.garble hash coins hidden keys outputs)).le

def schemeWith (n : Nat) (sampler : Bytes n → (hidden : Private) →
    DutyFreeProgram.Randomness hidden × DutyFreeProgram.HotKeys) : SecretRelease.Scheme challenge where
  Artifact := DutyFreeProgram.Artifact
  randomnessBytes := n
  garble := fun hash coins hidden keys _ =>
    let labels := Vector.ofFn keys
    let sampled := sampler coins hidden
    DutyFreeProgram.garble hash hidden sampled.1 labels.get sampled.2
  encode := DutyFreeArtifact.encode
  decode := DutyFreeArtifact.decode
  evaluate := DutyFreeProgram.evaluate

theorem schemeWith_encode (n : Nat) (sampler : Bytes n → (hidden : Private) →
    DutyFreeProgram.Randomness hidden × DutyFreeProgram.HotKeys)
    (artifact : DutyFreeProgram.Artifact) :
    (schemeWith n sampler).encode artifact = DutyFreeArtifact.encode artifact := rfl

theorem schemeWith_decode (n : Nat) (sampler : Bytes n → (hidden : Private) →
    DutyFreeProgram.Randomness hidden × DutyFreeProgram.HotKeys) :
    (schemeWith n sampler).decode = DutyFreeArtifact.decode := rfl

theorem schemeWith_garble (n : Nat) (sampler : Bytes n → (hidden : Private) →
    DutyFreeProgram.Randomness hidden × DutyFreeProgram.HotKeys)
    (hash : Hash) (coins : Bytes n) (hidden : Private)
    (keys : challenge.inputs.Keys) (outputs : challenge.outputs.Keys) :
    (schemeWith n sampler).garble hash coins hidden keys outputs =
      DutyFreeProgram.garble hash hidden (sampler coins hidden).1 keys (sampler coins hidden).2 := by
  have hk : (Vector.ofFn keys).get = keys := by funext i; exact Vector.get_ofFn keys i
  simp only [schemeWith, hk]

theorem schemeWith_evaluate (n : Nat) (sampler : Bytes n → (hidden : Private) →
    DutyFreeProgram.Randomness hidden × DutyFreeProgram.HotKeys) :
    (schemeWith n sampler).evaluate = DutyFreeProgram.evaluate := rfl

theorem evaluate_encode (n : Nat) (sampler : Bytes n → (hidden : Private) →
    DutyFreeProgram.Randomness hidden × DutyFreeProgram.HotKeys)
    (hash : Hash) (artifact : DutyFreeProgram.Artifact) (input : Input) (active : ByteArray) :
    (schemeWith n sampler).evaluateBytes hash ((schemeWith n sampler).encode artifact) input active =
      DutyFreeProgram.evaluate hash artifact input active := by
  delta SecretRelease.Scheme.evaluateBytes
  erw [schemeWith_encode, schemeWith_decode, DutyFreeArtifact.decode_encode, Option.bind_some,
    schemeWith_evaluate]

theorem encoded_size (n : Nat) (sampler : Bytes n → (hidden : Private) →
    DutyFreeProgram.Randomness hidden × DutyFreeProgram.HotKeys)
    (artifact : DutyFreeProgram.Artifact) :
    ((schemeWith n sampler).encode artifact).size = 1776384 := by
  rw [schemeWith_encode]
  exact DutyFreeArtifact.encode_size artifact

theorem correctWith (n : Nat) (sampler : Bytes n → (hidden : Private) →
    DutyFreeProgram.Randomness hidden × DutyFreeProgram.HotKeys) : Correct (schemeWith n sampler) := by
  apply correct_of_parts
  · intro artifact
    erw [schemeWith_encode, schemeWith_decode, DutyFreeArtifact.decode_encode]
    rfl
  · intro hash coins hidden keys outputs input
    erw [schemeWith_garble, schemeWith_evaluate]
    exact DutyFreeProgram.evaluate_garble hash hidden (sampler coins hidden).1 keys
      (sampler coins hidden).2 input

theorem artifactBoundWith (n : Nat) (sampler : Bytes n → (hidden : Private) →
    DutyFreeProgram.Randomness hidden × DutyFreeProgram.HotKeys) :
    ArtifactBound (schemeWith n sampler) 1776384 :=
  bound_of_encoder (schemeWith n sampler) 1776384 (encoded_size n sampler)

end G1Release.Submission.DutyFreeSampler
