import WotsLamport.Protected.Target
import Lean

open Lean Elab Command in
run_cmd do
  for mod in (← getEnv).header.moduleNames do
    for forbidden in [`WotsLamport.Submission, `WotsLamport.Tests,
                      `SecretRelease.Examples,
                      `SecretRelease.Simulation, `SecretRelease.NativeHash, `SecretRelease.CLI] do
      if forbidden.isPrefixOf mod then
        throwError "implementation leaked into neutral target: {mod}"
  IO.println "PASS: WOTS target excludes solution helpers, examples, tests, and native hashing"
