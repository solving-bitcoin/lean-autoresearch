import SecretRelease.Examples
import Lean

open Lean Elab Command in
run_cmd liftTermElabM do
  for decl in [``SecretRelease.Examples.privateMap, ``SecretRelease.Examples.SizeAccepted] do
    for ax in ← collectAxioms decl do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "optional example has forbidden axiom: {ax}"
  IO.println "PASS: optional declaration examples and size-cap wrapper"
