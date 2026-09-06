import SecretRelease
import Blake3Prize.Protected.Reference
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.NormNum

/-! Challenge declarations only. Neither example is a certified construction
or a replacement for either existing challenge's ranked acceptance predicate. -/
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

def hash64 (x : Vector Bool 512) : Vector Bool 256 :=
  (Blake3Prize.Protected.reference (x.map Blake3Prize.Protected.bitOfBool)).map
    (fun b => b.val == 1)

def blake3 : Challenge where
  Private := Unit
  Input := Vector Bool 512
  Output := Vector Bool 256
  privateCodec := Codec.unit
  inputCodec := Codec.bits 512
  inputs := Lamport (Codec.bits 512)
  outputs := Lamport (Codec.bits 256)
  reference := fun _ => hash64
  Claim := (Fin 512 ⊕ Fin 256) × Label
  wins := fun _ _ x ik ok guess => guess.2 = match guess.1 with
    | .inl i => (ik i).get (!x[i.val])
    | .inr i => (ok i).get (!(hash64 x)[i.val])
  withholding := some fun _ _ _ ik ok guess =>
    let pair := match guess.1 with
      | .inl i => ik i
      | .inr i => ok i
    guess.2 = pair.get false ∨ guess.2 = pair.get true
  rom := rom128

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
