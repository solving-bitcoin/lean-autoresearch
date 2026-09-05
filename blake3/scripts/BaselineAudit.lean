import Blake3Prize.Baselines.HalfGates.Target
import Lean

open Lean Elab Command in
run_cmd liftTermElabM do
  for decl in [``Blake3Prize.Baselines.HalfGates.referenceExpressions_correct,
    ``Blake3Prize.Baselines.HalfGates.referenceWordExpressions_correct,
    ``Blake3Prize.Baselines.HalfGates.WordProgram.digest_nat,
    ``Blake3Prize.Baselines.HalfGates.HalfGate.correct,
    ``Blake3Prize.Baselines.HalfGates.artifactBytes_eq,
    ``Blake3Prize.Baselines.HalfGates.Framing.decode_encode,
    ``Blake3Prize.Baselines.HalfGates.Framing.encode_decode] do
    let axioms ← collectAxioms decl
    for ax in axioms do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "baseline proof has forbidden axiom: {ax}"
  IO.println "PASS: optional expression/gate/codec proofs; no scheme-level secrecy claim"
