import SecretReleaseExamples

/-! Executability/selection tests only. These known fixture keys and dummy
oracle are deliberately public; this executable is not a certified scheme. -/
open SecretRelease

private def zero : Label := Vector.replicate 32 0
private def one : Label := Vector.replicate 32 1
private def hash : Hash := fun _ => zero
private def pair : Pair := ⟨(zero, one), by decide⟩

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
  unless Examples.blake3.inputCodec.width == 512 &&
      Examples.blake3.rom.error 0 == (1 : ℚ≥0) / 2^128 do
    throw (IO.userError "executable challenge metadata")
  IO.println "PASS: native SecretRelease disclosure modes, checked encodings, and metadata"
