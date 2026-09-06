import Blake3Prize.Protected.Reference
import SecretRelease.Encoding
import SecretRelease.Examples

namespace Blake3Prize.Protected

@[simp] theorem bit_roundtrip (b : Bit) : bitOfBool (b.val == 1) = b := by
  fin_cases b <;> rfl
@[simp] theorem bool_roundtrip (b : Bool) : ((bitOfBool b).val == 1) = b := by
  cases b <;> rfl

/-- Keep the original GF(2) mathematical interface and its exact bit order. -/
def bitCodec (n : Nat) : SecretRelease.Codec (Vector Bit n) where
  width := n
  encode := fun v => v.map fun b => b.val == 1
  decode := fun v => some (v.map bitOfBool)
  decode_encode := by intro v; apply congrArg some; ext i hi; simp
  encode_decode := by
    intro bits a h
    cases Option.some.inj h
    ext i hi; simp

/-- The accepted BLAKE3 game remains post-release recovery of any opposite
input/output label. Withholding and private-map privacy are not added. -/
def challenge : SecretRelease.Challenge where
  Private := Unit
  Input := Input
  Output := Output
  privateCodec := .unit
  inputCodec := bitCodec 512
  inputs := SecretRelease.Lamport (bitCodec 512)
  outputs := SecretRelease.Lamport (bitCodec 256)
  reference := fun _ => reference
  Claim := Fin 768 × SecretRelease.Label
  wins := fun _ _ input ik ok guess => guess.2 =
    if h : guess.1.val < 512 then
      (ik ⟨guess.1.val,h⟩).get (!(inputBit input ⟨guess.1.val,h⟩))
    else
      (ok ⟨guess.1.val-512,by change guess.1.val-512 < 256; omega⟩).get (!((reference input)[guess.1.val-512].val == 1))
  rom := SecretRelease.Examples.rom128

end Blake3Prize.Protected
