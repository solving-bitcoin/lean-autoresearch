import Lake
open Lake DSL

package blake3_garbling_challenge where
  weakLeanArgs := #["-j1"]

require mathlib from git "https://github.com/leanprover-community/mathlib4" @
  "0df444a360eaa60ab8c11dca51a86af692955474"
require Clean from git "https://github.com/Verified-zkEVM/clean" @
  "93c9d1ef45be9f687214625d7857889cf2485504"

require secretRelease from "../secret-release"

@[default_target]
lean_lib Blake3Prize

lean_lib SecretReleaseExamples

lean_exe "blake3-submission" where
  root := `Blake3Prize.Main

lean_exe "blake3-trusted" where
  root := `Blake3Prize.Protected.TrustedMain

-- Optional baseline: these executables are never called by acceptance.
lean_exe "blake3-half-gates" where
  root := `Blake3Prize.Baselines.HalfGates.Main

lean_exe "blake3-half-gates-checks" where
  root := `Blake3Prize.Baselines.HalfGates.TrustedMain

lean_exe "blake3-runner-test" where
  root := `Blake3Prize.Protected.RunnerTest
