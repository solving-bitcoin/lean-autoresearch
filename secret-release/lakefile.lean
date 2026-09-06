import Lake
open Lake DSL

package secretRelease where
  weakLeanArgs := #["-j1"]

require mathlib from git "https://github.com/leanprover-community/mathlib4" @
  "0df444a360eaa60ab8c11dca51a86af692955474"
require VCVio from git "https://github.com/Verified-zkEVM/VCVio" @
  "ffd0ca198fe6e640c0dd7f0f9c599943caacbf64"

@[default_target]
lean_lib SecretRelease

lean_exe "secret-release-checks" where
  root := `SecretReleaseTests.Native
