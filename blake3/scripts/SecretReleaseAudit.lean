import SecretReleaseExamples
import Lean

open SecretRelease
example : Examples.blake3.inputCodec.width = 512 := rfl
example : Examples.blake3.privateLeakage = none := rfl
example : Examples.blake3.withholding.isSome = true := rfl
example : Examples.blake3.correctness = .exact := rfl

open Lean Elab Command in
run_cmd liftTermElabM do
  for ax in ← collectAxioms ``SecretRelease.Examples.blake3 do
    unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
      throwError "BLAKE3 shared declaration has forbidden axiom: {ax}"
  IO.println "PASS: BLAKE3 shared declaration and axiom closure"
