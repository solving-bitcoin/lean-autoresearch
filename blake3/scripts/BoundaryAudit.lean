import Blake3Prize.Protected.Target
import Lean

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for mod in env.header.moduleNames do
    for forbidden in [`Blake3Prize.Baselines, `Blake3Prize.Protected.NativeHash,
                      `Clean.Specs.SHA256, `Challenge] do
      if forbidden.isPrefixOf mod then
        throwError "implementation leaked into neutral target: {mod}"
  IO.println "PASS: neutral contract imports neither a baseline nor the SHA-256 instantiation"
