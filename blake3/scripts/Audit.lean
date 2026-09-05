import Blake3Prize.Protected.Runner
import Blake3Prize.Submission.Solution

example : Blake3Prize.Protected.ValidCandidate
    Blake3Prize.Submission.candidate Blake3Prize.Submission.claimedBytes :=
  Blake3Prize.Submission.validClaimed

open Lean Elab Command in
run_cmd liftTermElabM do
  let env ← getEnv
  let modules := env.header.moduleNames
  for (name,info) in env.constants.toList do
    if let some index := env.getModuleIdxFor? name then
      let mod := modules[index.toNat]!
      if (`Blake3Prize.Submission).isPrefixOf mod then
        if info.isAxiom then throwError "submission axiom: {name}"
        unless (`Blake3Prize.Submission).isPrefixOf name || (`_private).isPrefixOf name do
          throwError "submission declares outside its namespace: {name}"
  for decl in [``Blake3Prize.Submission.validClaimed,
    ``Blake3Prize.Protected.referenceExpressions_correct,
    ``Blake3Prize.Protected.HalfGate.correct,
    ``Blake3Prize.Protected.artifactBytes_eq,
    ``Blake3Prize.Protected.Framing.decode_encode,
    ``Blake3Prize.Protected.Framing.encode_decode] do
    let axioms ← collectAxioms decl
    for ax in axioms do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "forbidden axiom: {ax}"
  IO.println "PASS: exact protected candidate type and allowed axiom closure"
