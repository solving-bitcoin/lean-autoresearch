import Lake
open Lake DSL
package wotsLamport where
  weakLeanArgs := #["-j1"]
require mathlib from git "https://github.com/leanprover-community/mathlib4" @
  "0df444a360eaa60ab8c11dca51a86af692955474"
require secretRelease from "../secret-release"
@[default_target]
lean_lib WotsLamport
lean_exe "secret-release-tools" where
  srcDir := ".lake/generated"
  root := `SRTools
