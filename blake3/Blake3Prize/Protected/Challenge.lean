import Blake3Prize.Protected.Reference
import SecretRelease.Encoding
import SecretRelease.Profiles

namespace Blake3Prize.Protected
open SecretRelease (Codec)

/-- The accepted BLAKE3 game remains post-release recovery of any opposite
input/output label. Withholding and private-map privacy are not added. -/
def challenge : SecretRelease.Challenge where
  Private := Unit
  Input := Input
  Output := Output
  privateCodec := .unit
  inputCodec := Codec.byteVector 64
  inputs := SecretRelease.Lamport (Codec.byteVector 64)
  outputs := SecretRelease.Lamport (Codec.byteVector 32)
  reference := fun _ => reference
  Claim := Fin 768 × SecretRelease.Label
  wins := fun _ _ input ik ok guess => guess.2 =
    if h : guess.1.val < 512 then
      (ik ⟨guess.1.val,h⟩).get (!((Codec.byteVector 64).encode input).get ⟨guess.1.val,h⟩)
    else
      let i : Fin 256 := ⟨guess.1.val-512,by omega⟩
      (ok i).get (!((Codec.byteVector 32).encode (reference input)).get i)
  rom := SecretRelease.Profiles.rom128

end Blake3Prize.Protected
