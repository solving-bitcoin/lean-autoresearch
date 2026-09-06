import G1Release.Submission.Solution
import G1Release.Protected.Wire
import Lean

example : Option (SecretRelease.Candidate G1Release.Protected.challenge) :=
  G1Release.Submission.entry

open Lean Elab Command in
run_cmd liftTermElabM do
  let env ← getEnv
  let modules := env.header.moduleNames
  let mut declarations := [``G1Release.Submission.entry,
    ``G1Release.Protected.challenge, ``G1Release.Protected.wire, ``G1Release.Protected.CertifiedScheme,
    ``G1Release.Protected.inputCodec, ``G1Release.Protected.outputCodec,
    ``G1Release.Protected.privateCodec, ``G1Release.Protected.reference_toPoint,
    ``G1Release.Protected.same_leakage_iff, ``G1Release.Protected.same_leakage_zero_map, ``G1Release.Protected.bytesToBits_bitsToBytes,
    ``SecretRelease.Certified, ``SecretRelease.Certificate, ``SecretRelease.Candidate]
  for (name, info) in env.constants.toList do
    if let some index := env.getModuleIdxFor? name then
      let mod := modules[index.toNat]!
      if (`G1Release.Submission).isPrefixOf mod then
        if info.isAxiom then throwError "submission axiom: {name}"
        unless (`G1Release.Submission).isPrefixOf name || (`_private).isPrefixOf name do
          throwError "submission declares outside its namespace: {name}"
        declarations := name :: declarations
  for decl in declarations do
    for ax in (← collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "forbidden axiom: {ax} in {decl}"
  IO.println "PASS: G1 certificate, canonical codecs, group semantics, and axiom closure"
