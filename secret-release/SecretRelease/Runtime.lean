import SecretRelease.Encoding

namespace SecretRelease

/-- Author-owned transport metadata; custom disclosures use their own codecs.
`kind` is only a fixture hint, never a restriction on the mathematical game. -/
structure KeyWire (d : Disclosure A) where
  codec : ByteCodec d.Keys
  kind : String := "custom"
  count : Nat := 0

def KeyWire.lamport (c : Codec A) : KeyWire (Lamport c) := ⟨lamportKeys c, "lamport", c.width⟩
def KeyWire.hors (n : Nat) (select : Hash → A → Fin n → Bool) : KeyWire (HORS n select) :=
  ⟨horsKeys n select, "hors", n⟩
def KeyWire.onesOnly (c : Codec A) : KeyWire (OnesOnly c) := ⟨onesOnlyKeys c, "ones-only", c.width⟩
def KeyWire.preimage (p : A → Bool) : KeyWire (Preimage p) := ⟨preimageKeys p, "preimage", 1⟩
def KeyWire.plain (encode : A → ByteArray) : KeyWire (Plain encode) := ⟨plainKeys encode, "plain", 0⟩

structure WireFormat (c : Challenge) where
  identity : String
  inputs : KeyWire c.inputs
  outputs : KeyWire c.outputs
  /-- Optional: custom output types need not have a fixed-size codec. -/
  output : Option (ByteCodec c.Output) := none

namespace Runtime

def garble (w : WireFormat c) (s : Scheme c) (h : Hash)
    (coins privateBytes inputKeys outputKeys : ByteArray) : Option ByteArray := do
  if hc : coins.size = s.randomnessBytes then
    let p ← c.privateCodec.bytes.decode privateBytes
    let ik ← w.inputs.codec.decode inputKeys
    let ok ← w.outputs.codec.decode outputKeys
    pure (s.garbleBytes h ⟨coins.data,hc⟩ p ik ok)
  else none

/-- The known input is a separate fixed canonical channel. Only the selected
credentials are returned; garbling never receives this input. -/
def encode (w : WireFormat c) (h : Hash) (input inputKeys : ByteArray) : Option ByteArray := do
  let x ← c.inputCodec.bytes.decode input
  let ik ← w.inputs.codec.decode inputKeys
  pure (c.inputs.reveal h ik x)

def evaluate (s : Scheme c) (h : Hash) (artifact input active : ByteArray) : Option ByteArray := do
  let x ← c.inputCodec.bytes.decode input
  s.evaluateBytes h artifact x active

def reference (w : WireFormat c) (privateBytes input : ByteArray) : Option ByteArray := do
  let out ← w.output
  let p ← c.privateCodec.bytes.decode privateBytes
  let x ← c.inputCodec.bytes.decode input
  pure (out.encode (c.reference p x))

def release (w : WireFormat c) (h : Hash) (value keys : ByteArray) : Option ByteArray := do
  let out ← w.output
  let y ← out.decode value
  let ok ← w.outputs.codec.decode keys
  pure (c.outputs.reveal h ok y)

@[simp] theorem garble_encoded (w : WireFormat c) (s : Scheme c) (h : Hash)
    (coins : Bytes s.randomnessBytes) (p : c.Private) (ik : c.inputs.Keys) (ok : c.outputs.Keys) :
    garble w s h ⟨coins.toArray⟩ (c.privateCodec.bytes.encode p)
      (w.inputs.codec.encode ik) (w.outputs.codec.encode ok) = some (s.garbleBytes h coins p ik ok) := by
  simp [garble, ByteArray.size, ByteCodec.decode_encode]

@[simp] theorem encode_encoded (w : WireFormat c) (h : Hash) (x : c.Input) (ik : c.inputs.Keys) :
    encode w h (c.inputCodec.bytes.encode x) (w.inputs.codec.encode ik) =
      some (c.inputs.reveal h ik x) := by simp [encode, ByteCodec.decode_encode]

@[simp] theorem evaluate_encoded (s : Scheme c) (h : Hash) (artifact active : ByteArray) (x : c.Input) :
    evaluate s h artifact (c.inputCodec.bytes.encode x) active = s.evaluateBytes h artifact x active := by
  simp [evaluate, ByteCodec.decode_encode]

@[simp] theorem reference_encoded (w : WireFormat c) (out : ByteCodec c.Output)
    (ho : w.output = some out) (p : c.Private) (x : c.Input) :
    reference w (c.privateCodec.bytes.encode p) (c.inputCodec.bytes.encode x) =
      some (out.encode (c.reference p x)) := by
  simp [reference, ho, ByteCodec.decode_encode]

@[simp] theorem release_encoded (w : WireFormat c) (out : ByteCodec c.Output)
    (ho : w.output = some out) (h : Hash) (y : c.Output) (ok : c.outputs.Keys) :
    release w h (out.encode y) (w.outputs.codec.encode ok) = some (c.outputs.reveal h ok y) := by
  simp [release, ho, ByteCodec.decode_encode]

/-- Binary correctness is exactly serialized scheme correctness after canonical
input/key decoding, and does not depend on the concrete hash instantiation. -/
theorem pipeline_correct (w : WireFormat c) (s : Scheme c) (correct : Correct s)
    (h : Hash) (coins : Bytes s.randomnessBytes) (p : c.Private) (ik : c.inputs.Keys)
    (ok : c.outputs.Keys) (x : c.Input) :
    (garble w s h ⟨coins.toArray⟩ (c.privateCodec.bytes.encode p)
      (w.inputs.codec.encode ik) (w.outputs.codec.encode ok)).bind (fun artifact =>
      (encode w h (c.inputCodec.bytes.encode x) (w.inputs.codec.encode ik)).bind fun active =>
        evaluate s h artifact (c.inputCodec.bytes.encode x) active) =
      some (c.outputs.reveal h ok (c.reference p x)) := by
  simp only [garble_encoded, encode_encoded, Option.bind_some, evaluate_encoded]
  exact correct h coins p ik ok x

end Runtime
end SecretRelease
