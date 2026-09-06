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

-- The existing audited portable C backend is a runtime instantiation only.
target nativeSha256.o pkg : FilePath := do
  buildO (pkg.buildDir / "native" / "sha256.o")
    (← inputTextFile <| pkg.dir / "native" / "sha256.c")
    #["-I", (← getLeanIncludeDir).toString] #["-O3", "-fPIC"]
extern_lib nativeSha256 pkg := do
  buildStaticLib (pkg.staticLibDir / nameToStaticLib "g1_sha256") #[← nativeSha256.o.fetch]

lean_exe "g1-release" where
  root := `G1Release.Main
lean_exe "g1-release-checks" where
  root := `G1Release.Protected.NativeChecks

lean_exe "g1-release-runner-test" where
  root := `G1Release.Protected.RunnerFixture
