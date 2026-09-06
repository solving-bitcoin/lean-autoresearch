import Lake
open Lake DSL System

package g1Release where
  weakLeanArgs := #["-j1"]

require mathlib from git "https://github.com/leanprover-community/mathlib4" @
  "0df444a360eaa60ab8c11dca51a86af692955474"
require CompPoly from git "https://github.com/Verified-zkEVM/CompPoly.git" @
  "a09455a22fea4623a2a1c5b363cf6efc61486a83"
require secretRelease from "../secret-release"

-- Reuse the existing protected BN254 mathematics, never the old submission.
lean_lib GarblingPrize where
  srcDir := ".."
  globs := #[.submodules `GarblingPrize.Protected]

@[default_target]
lean_lib G1Release

-- The shared builder generates this module; authors write no I/O code.
lean_exe "secret-release-tools" where
  srcDir := ".lake/generated"
  root := `SRTools
