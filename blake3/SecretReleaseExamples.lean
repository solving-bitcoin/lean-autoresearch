import SecretRelease.Examples
import Blake3Prize.Protected.Reference

/-! BLAKE3 declaration only; this does not replace its acceptance predicate. -/
namespace SecretRelease.Examples

def blake3 : Challenge where
  Private := Unit
  Input := Bytes 64
  Output := Bytes 32
  privateCodec := Codec.unit
  inputCodec := Codec.byteVector 64
  inputs := Lamport (Codec.byteVector 64)
  outputs := Lamport (Codec.byteVector 32)
  reference := fun _ => Blake3Prize.Protected.reference
  Claim := (Fin 512 ⊕ Fin 256) × Label
  wins := fun _ _ x ik ok guess => guess.2 = match guess.1 with
    | .inl i => (ik i).get (!((Codec.byteVector 64).encode x).get i)
    | .inr i => (ok i).get (!((Codec.byteVector 32).encode (Blake3Prize.Protected.reference x)).get i)
  withholding := some fun _ _ _ ik ok guess =>
    let pair := match guess.1 with
      | .inl i => ik i
      | .inr i => ok i
    guess.2 = pair.get false ∨ guess.2 = pair.get true
  rom := Profiles.rom128

end SecretRelease.Examples
