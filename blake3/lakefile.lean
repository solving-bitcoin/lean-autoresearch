import Lake
open Lake DSL

package blake3_garbling_challenge where
  weakLeanArgs := #["-j1"]

require mathlib from git "https://github.com/leanprover-community/mathlib4" @
  "8f9d9cff6bd728b17a24e163c9402775d9e6a365"
require clean from git "https://github.com/Verified-zkEVM/clean" @
  "041c6e7ebc06f5cbfd534c2a19c4120f3de62435"

@[default_target]
lean_lib Blake3Prize

lean_exe "blake3-circuit" where
  root := `Blake3Prize.Main

lean_exe "blake3-trusted" where
  root := `Blake3Prize.Protected.TrustedMain
