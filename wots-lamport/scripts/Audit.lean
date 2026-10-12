import WotsLamport.Submission.Solution
import WotsLamport.Protected.Wire
import Lean

example : Option (SecretRelease.Candidate WotsLamport.Protected.challenge) :=
  WotsLamport.Submission.entry

open Lean Elab Command in
run_cmd liftTermElabM do
  let env ← getEnv
  let modules := env.header.moduleNames
  let mut declarations := [``WotsLamport.Submission.entry,
    ``WotsLamport.Protected.challenge, ``WotsLamport.Protected.wire, ``WotsLamport.Protected.CertifiedScheme,
    ``WotsLamport.Protected.inputCodec, ``WotsLamport.Protected.outputCodec,
    ``WotsLamport.Protected.privateCodec, ``WotsLamport.Protected.wotsDisclosure,
    ``WotsLamport.Protected.publicKey_visible,
    ``SecretRelease.Certified, ``SecretRelease.Certificate, ``SecretRelease.Candidate]
  for (name, info) in env.constants.toList do
    if let some index := env.getModuleIdxFor? name then
      let mod := modules[index.toNat]!
      if (`WotsLamport.Submission).isPrefixOf mod then
        if info.isAxiom then throwError "submission axiom: {name}"
        unless (`WotsLamport.Submission).isPrefixOf name || (`_private).isPrefixOf name do
          throwError "submission declares outside its namespace: {name}"
        declarations := name :: declarations
  for decl in declarations do
    for ax in (← collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "forbidden axiom: {ax} in {decl}"
  IO.println "PASS: WOTS candidate, protected games, correlated disclosure, and axiom closure"

example : WotsLamport.Submission.entry =
    WotsLamport.Submission.submission.map WotsLamport.Protected.Entry.candidate := by rfl
