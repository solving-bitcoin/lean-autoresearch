import G1Release.Protected.Target
import Lean

open Lean Elab Command in
run_cmd do
  for mod in (← getEnv).header.moduleNames do
    for forbidden in [`G1Release.Submission, `G1Release.Tests,
                      `SecretRelease.Examples,
                      `SecretRelease.Simulation, `SecretRelease.NativeHash, `SecretRelease.CLI] do
      if forbidden.isPrefixOf mod then
        throwError "implementation leaked into neutral target: {mod}"
  IO.println "PASS: G1 target excludes solution helpers, examples, tests, and native hashing"
