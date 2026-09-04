import Lake

open System Lake DSL

package g1_garbling_challenge where
  license := "Apache-2.0"
  weakLeanArgs := #["-j1"]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.33.1"

require CompPoly from git
  "https://github.com/Verified-zkEVM/CompPoly.git" @ "v4.33.1"

target nativeSha256.o pkg : FilePath := do
  let objectFile := pkg.buildDir / "native" / "sha256.o"
  let source ← inputTextFile <| pkg.dir / "native" / "sha256.c"
  let weakArgs := #["-I", (← getLeanIncludeDir).toString]
  buildO objectFile source weakArgs #["-O3", "-fPIC"]

extern_lib nativeSha256 pkg := do
  let objectFile ← nativeSha256.o.fetch
  buildStaticLib (pkg.staticLibDir / nameToStaticLib "g1_sha256") #[objectFile]

@[default_target]
lean_lib GarblingPrize

lean_exe "g1-challenge" where
  root := `GarblingPrize.Executable.Main
