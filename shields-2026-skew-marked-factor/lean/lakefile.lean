import Lake
open Lake DSL

package «skew-marked-factor» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩,
    ⟨`weak.linter.mathlibStandardSet, true⟩,
    ⟨`weak.linter.style.header, false⟩,
    ⟨`weak.linter.style.longFile, .ofNat 1500⟩
  ]
  lintDriver := "batteries/runLinter"

require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "v4.34.1"

lean_lib Vendor where
  srcDir := "../../_lean_shared"
  globs := #[.submodules `Vendor]

lean_lib Shields where
  srcDir := "../../_lean_shared"
  globs := #[.andSubmodules `Shields]

@[default_target]
lean_lib SkewMarkedFactor where
  globs := #[.andSubmodules `SkewMarkedFactor]
