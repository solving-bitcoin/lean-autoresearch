/- Trusted verifier-side environment and axiom audit. -/
import GarblingPrize.Benchmark.Challenge

open Lean Lean.Meta

def trustedModulePrefixes : List String :=
  ["Init", "Lean", "Lake", "Std", "Batteries", "Aesop", "Qq", "Plausible",
   "ProofWidgets", "ImportGraph", "LeanSearchClient", "Mathlib",
   "CompPoly",
   "GarblingPrize"]

open Elab.Command in
run_cmd liftCoreM do
  let env ← getEnv
  let modules := env.header.moduleNames
  let mut badModules : Array Name := #[]
  for moduleName in modules do
    let top := (moduleName.components.head?.getD moduleName).toString
    unless trustedModulePrefixes.contains top do
      badModules := badModules.push moduleName
  unless badModules.isEmpty do
    for moduleName in badModules do
      IO.eprintln s!"unreviewed module prefix: {moduleName}"
    throwError "unreviewed modules in candidate environment"

  let mut localAxioms : Array (Name × Name) := #[]
  for (name, constantInfo) in env.constants.toList do
    if let some index := env.getModuleIdxFor? name then
      let moduleName := modules[index.toNat]!
      if (`GarblingPrize).isPrefixOf moduleName && constantInfo.isAxiom then
        localAxioms := localAxioms.push (name, moduleName)
  unless localAxioms.isEmpty do
    for (name, moduleName) in localAxioms do
      IO.eprintln s!"local axiom {name} declared in {moduleName}"
    throwError "local axiom declarations are forbidden"

open Elab.Command in
run_cmd liftTermElabM do
  let whitelist : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let declarations : List Name :=
    [``GarblingPrize.Benchmark.candidate,
     ``GarblingPrize.Protected.reference,
     ``GarblingPrize.Protected.ValidCandidate,
     ``GarblingPrize.Protected.Scheme.garbleWithSeedAndLabelPairs_eq_garbleBytes,
     ``GarblingPrize.Protected.Scheme.evaluateWithLabels_correct,
     ``GarblingPrize.Protected.Scheme.evaluateWithLabels_reusable,
     ``GarblingPrize.Protected.Scheme.garbleWithSeedAndLabelPairs_size_le]
  for declaration in declarations do
    let axioms ← collectAxioms declaration
    let offending := axioms.toList.filter fun axiomName =>
      !whitelist.contains axiomName
    unless offending.isEmpty do
      for axiomName in offending do
        IO.eprintln s!"{declaration} depends on forbidden axiom {axiomName}"
      throwError "candidate has a non-whitelisted axiom dependency"
  IO.println "ok — candidate uses only propext/Classical.choice/Quot.sound"
