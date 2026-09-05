import Blake3Prize.Protected.Runner
import Blake3Prize.Submission.Solution

-- The verifier appends a kernel check binding entry.map maxBytes to the exact
-- score.txt literal (or none). No submission-selected proposition is audited.
example : Option Blake3Prize.Protected.CertifiedScheme := Blake3Prize.Submission.entry

open Lean Elab Command in
run_cmd liftTermElabM do
  let env ← getEnv
  let modules := env.header.moduleNames
  for mod in modules do
    if (`Challenge).isPrefixOf mod then
      throwError "unexpected former specification dependency: {mod}"
  let mut declarations := [``Blake3Prize.Submission.entry,
    ``Blake3Prize.Protected.ValidCandidate,
    ``Blake3Prize.Protected.ROM.Secrecy,
    ``Blake3Prize.Protected.ROM.runProgram_pure,
    ``Blake3Prize.Protected.ROM.experimentLaw_univ,
    ``Blake3Prize.Protected.ROM.inputPairs_distinct,
    ``Blake3Prize.Protected.ROM.outputPairs_distinct,
    ``Blake3Prize.Protected.ROM.not_secrecy_of_always_wins,
    ``Blake3Prize.Protected.nativeHash]
  for (name,info) in env.constants.toList do
    if let some index := env.getModuleIdxFor? name then
      let mod := modules[index.toNat]!
      if (`Blake3Prize.Submission).isPrefixOf mod then
        if info.isAxiom then throwError "submission axiom: {name}"
        unless (`Blake3Prize.Submission).isPrefixOf name || (`_private).isPrefixOf name do
          throwError "submission declares outside its namespace: {name}"
        declarations := name :: declarations
  for decl in declarations do
    let axioms ← collectAxioms decl
    for ax in axioms do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "forbidden axiom: {ax} in {decl}"
  IO.println "PASS: exact scheme-level certificate type and allowed axiom closure"
