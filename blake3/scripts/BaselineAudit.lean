import Blake3Prize.Submission.HalfGatesTarget
import Lean

open Lean Elab Command in
run_cmd liftTermElabM do
  for decl in [``Blake3Prize.Submission.HalfGates.referenceExpressions_correct,
    ``Blake3Prize.Submission.HalfGates.referenceWordExpressions_correct,
    ``Blake3Prize.Submission.HalfGates.WordProgram.digest_nat,
    ``Blake3Prize.Submission.HalfGates.HalfGate.correct,
    ``Blake3Prize.Submission.HalfGates.artifactBytes_eq,
    ``Blake3Prize.Submission.HalfGates.Framing.decode_encode,
    ``Blake3Prize.Submission.HalfGates.Framing.encode_decode] do
    let axioms ← collectAxioms decl
    for ax in axioms do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "baseline proof has forbidden axiom: {ax}"
  IO.println "PASS: optional expression/gate/codec proofs; no scheme-level secrecy claim"
