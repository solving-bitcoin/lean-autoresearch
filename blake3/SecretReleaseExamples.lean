import SecretRelease.Examples
import Blake3Prize.Protected.Reference

/-! BLAKE3 declaration only; this does not replace its acceptance predicate. -/
namespace SecretRelease.Examples

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

end SecretRelease.Examples
