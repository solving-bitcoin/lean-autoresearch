import SecretRelease.Simulation
import Lean

-- Check the actual upstream definitions and their transitive axiom closure.
-- This is an integration audit, not a simulation certificate for a scheme.
open Lean Elab Command in
run_cmd liftTermElabM do
  for decl in [``Interaction.UC.ObservedCompUCSecure,
    ``Interaction.UC.ObservedCompEmulates.refl,
    ``Interaction.UC.ObservedCompEmulates.triangle,
    ``Interaction.UC.AsympObservedCompEmulates,
    ``OracleComp.Complexity.StrictPPTWitness,
    ``OracleComp.Complexity.PureCertificate,
    ``OracleComp.Complexity.StrictPPTWitness.runsWithin,
    ``SecurityGame.ReductionWithCost,
    ``SecurityGame.secureAgainst_of_reduction_withCost] do
    for ax in ← collectAxioms decl do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "VCVio simulation infrastructure has forbidden axiom: {ax}"
  IO.println "PASS: VCVio simulation, computational witnesses, and reduction-cost imports"
