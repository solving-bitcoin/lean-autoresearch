import SecretRelease.Encoding
import SecretRelease.Profiles

/-! Declaration patterns, not certified schemes or construction proofs. -/
namespace SecretRelease.Examples

/-- The G1 declaration pattern: instantiate `reference` with Q + [r]A,
the private codec with canonical (Q,r), and the input codec with valid affine
points. The output encoder is injective; its bytes are the explicit permitted
private-parameter leakage. This does not transport G1's existing infinite-pad
proof to finite keys. -/
def privateMap (privateCodec : Codec P) (inputCodec : Codec A)
    (encodeOutput : O → ByteArray) (_injective : Function.Injective encodeOutput)
    (reference : P → A → O) : Challenge where
  Private := P
  Input := A
  Output := O
  privateCodec := privateCodec
  inputCodec := inputCodec
  inputs := Lamport inputCodec
  outputs := Plain encodeOutput
  reference := reference
  Claim := Fin inputCodec.width × Label
  wins := fun _ _ a keys _ guess => guess.2 =
    (keys guess.1).get (!(inputCodec.encode a)[guess.1.val])
  privateLeakage := some fun p a => encodeOutput (reference p a)
  rom := Profiles.rom128

/-- An optional hard cap, fixed by the challenge's trusted acceptance layer.
Without this wrapper, `maxBytes` is a certified score, not a threshold check. -/
structure SizeAccepted (c : Challenge) (limit : Nat) where
  certified : Certified c
  withinLimit : certified.maxBytes ≤ limit

end SecretRelease.Examples
