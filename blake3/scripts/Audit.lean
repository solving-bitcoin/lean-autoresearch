import Blake3Prize.Protected.Wire
import Blake3Prize.Submission.Solution
import Lean

example : Option (SecretRelease.Candidate Blake3Prize.Protected.challenge) := Blake3Prize.Submission.entry

open Lean Elab Command in
run_cmd liftTermElabM do
  let env ← getEnv
  let modules := env.header.moduleNames
  let mut declarations := [``Blake3Prize.Submission.entry,
    ``Blake3Prize.Protected.challenge, ``Blake3Prize.Protected.wire,
    ``SecretRelease.Certificate, ``SecretRelease.Candidate, ``SecretRelease.Certified]
  for (name,info) in env.constants.toList do
    if let some index := env.getModuleIdxFor? name then
      if (`Blake3Prize.Submission).isPrefixOf modules[index.toNat]! then
        if info.isAxiom then throwError "submission axiom: {name}"
        unless (`Blake3Prize.Submission).isPrefixOf name || (`_private).isPrefixOf name do
          throwError "submission declares outside its namespace: {name}"
        declarations := name :: declarations
  for decl in declarations do
    for ax in (← collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "forbidden axiom: {ax} in {decl}"
  IO.println "PASS: exact shared candidate, certificate and wire-codec axiom closure"
