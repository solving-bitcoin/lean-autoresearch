import SecretRelease
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.NormNum

/-! Declaration patterns, not certified schemes or construction proofs. -/
namespace SecretRelease.Examples

def rom128 : ClassicalBoundedQueryROM where
  maxQueries := 2^64
  error := fun q => (q + 1 : ℚ≥0) / 2^128
  nontrivial := by
    intro q hq
    have hq' : (q : ℚ≥0) ≤ (2^64 : ℚ≥0) := by exact_mod_cast hq
    calc
      (q + 1 : ℚ≥0) / 2^128 ≤ (2^64 + 1 : ℚ≥0) / 2^128 := by gcongr
      _ < 1 := by norm_num

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
  rom := rom128

end SecretRelease.Examples
