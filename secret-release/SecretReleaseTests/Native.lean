import SecretRelease.Profiles
import SecretRelease.Runtime

/-! Executability/selection tests only. These known fixture keys and dummy
oracle are deliberately public; this executable is not a certified scheme. -/
open SecretRelease

private def zero : Label := Vector.replicate 32 0
private def one : Label := Vector.replicate 32 1
private def hash : Hash := fun _ => zero
private def pair : Pair := ⟨(zero, one), by decide⟩

private def coinEchoChallenge : Challenge where
  Private := Unit
  Input := Unit
  Output := Unit
  privateCodec := Codec.unit
  inputCodec := Codec.unit
  inputs := Plain (fun _ => ByteArray.empty)
  outputs := Plain (fun _ => ByteArray.empty)
  reference := fun _ _ => ()
  Claim := Unit
  wins := fun _ _ _ _ _ _ => False
  rom := Profiles.rom128

private def coinEchoScheme (n : Nat) : Scheme coinEchoChallenge where
  Artifact := ByteArray
  randomnessBytes := n
  garble := fun _ coins _ _ _ => ⟨coins.toArray⟩
  encode := id
  decode := some
  evaluate := fun _ _ _ _ => some ByteArray.empty
  packedGarble := some { run := fun _ coins _ _ _ => coins, agrees := by intros; rfl }

private def coinEchoWire : WireFormat coinEchoChallenge where
  identity := "test-packed-coins"
  inputs := .plain (fun _ => ByteArray.empty)
  outputs := .plain (fun _ => ByteArray.empty)

def main : IO Unit := do
  let bits := #v[true, false]
  let codec := Codec.bits 2
  unless (Lamport codec).reveal hash (fun _ => pair) bits == pack [one, zero] do
    throw (IO.userError "Lamport selection")
  let keys : Fin 2 → Label := fun i => if i.val == 0 then one else zero
  unless (OnesOnly codec).reveal hash keys bits == pack [one] do
    throw (IO.userError "ones-only selection")
  unless (HORS 2 (fun _ (_ : Unit) i => i.val == 1)).reveal hash keys () == pack [zero] do
    throw (IO.userError "HORS subset selection")
  unless (Preimage id).reveal hash one false == ByteArray.empty &&
      (Preimage id).reveal hash one true == pack [one] do
    throw (IO.userError "preimage disclosure")
  let checked := Codec.checked 2 (fun b => b[0] != b[1])
  unless (checked.decode #v[false, false]).isNone &&
      (checked.decode #v[true, true]).isNone &&
      (checked.decode bits).isSome do
    throw (IO.userError "valid encoding boundary")
  unless Profiles.rom128.maxQueries == 2^64 &&
      Profiles.rom128.error 0 == (1 : ℚ≥0) / 2^128 do
    throw (IO.userError "executable challenge metadata")
  -- Non-byte-aligned widths accept canonical padding only.
  let bitWire := (Codec.bits 2).bytes
  unless bitWire.encode bits == ⟨#[1]⟩ &&
      bitWire.decode ⟨#[1]⟩ == some bits && (bitWire.decode ⟨#[5]⟩).isNone &&
      (bitWire.decode ⟨#[1,0]⟩).isNone && (bitWire.decode ⟨#[]⟩).isNone do
    throw (IO.userError "canonical bit padding/length")
  let lamport := lamportKeys codec
  let raw := lamport.encode (fun _ => pair)
  unless raw == pack [zero,one,zero,one] && (lamport.decode raw).isSome &&
      (lamport.decode (pack [zero,zero,zero,one])).isNone do
    throw (IO.userError "Lamport key wire codec")
  let only := onesOnlyKeys codec
  unless only.encode keys == pack [one,zero] && (only.decode (pack [one,zero])).isSome do
    throw (IO.userError "ones-only key wire codec")
  let pre := preimageKeys (fun b : Bool => b)
  unless pre.encode one == pack [one] && (pre.decode (pack [one])).isSome do
    throw (IO.userError "preimage key codec")
  unless (plainKeys (fun _ : Unit => ByteArray.empty)).encode () == ByteArray.empty do
    throw (IO.userError "empty Plain key codec")
  let custom := HORS 2 (fun h (b : Bool) i => b && ((h ByteArray.empty)[0] == 0 || i.val == 1))
  let customWire := KeyWire.hors 2 (fun h (b : Bool) i => b && ((h ByteArray.empty)[0] == 0 || i.val == 1))
  unless (customWire.codec.decode (customWire.codec.encode keys)).isSome &&
      custom.reveal hash keys false == ByteArray.empty &&
      custom.reveal hash keys true == pack [one,zero] &&
      custom.reveal (fun _ => one) keys true == pack [zero] do
    throw (IO.userError "hash-dependent variable-size custom disclosure")
  IO.println "PASS: byte/key codecs, zero padding, distinct pairs, and custom selectors"
  IO.println "PASS: native SecretRelease disclosure modes, checked encodings, and metadata"
  -- 256 MiB of packed bytes would require 2 GiB just for an unpacked pointer
  -- array on the CI host. This must pass the unchanged 1 GiB native guard.
  let mut coins : ByteArray := ⟨#[37]⟩
  for _ in [:28] do
    coins := coins ++ coins
  let result := Runtime.garble coinEchoWire (coinEchoScheme (2^28)) hash
    coins ByteArray.empty ByteArray.empty ByteArray.empty
  unless result.map ByteArray.size == some (2^28) do
    throw (IO.userError "packed coin execution")
  unless (Runtime.garble coinEchoWire (coinEchoScheme 1) hash
    ByteArray.empty ByteArray.empty ByteArray.empty ByteArray.empty).isNone do
    throw (IO.userError "packed coin length rejection")
  IO.println "PASS: proved packed coin path, 256 MiB buffer, exact length check"
