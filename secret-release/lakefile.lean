import Lake
open Lake DSL System

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

-- Trusted runtime instantiation; absent from SecretRelease's proof imports.
target nativeSha256.o pkg : FilePath := do
  buildO (pkg.buildDir / "native" / "sha256.o")
    (← inputTextFile <| pkg.dir / "native" / "sha256.c")
    #["-I", (← getLeanIncludeDir).toString] #["-O3", "-fPIC"]
extern_lib nativeSha256 pkg := do
  buildStaticLib (pkg.staticLibDir / nameToStaticLib "secret_release_sha256") #[← nativeSha256.o.fetch]
