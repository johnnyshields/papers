import Lake
open Lake DSL

package «skew-base-computational» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩,
    ⟨`weak.linter.mathlibStandardSet, true⟩,
    ⟨`weak.linter.style.header, false⟩,
    ⟨`weak.linter.style.longFile, .ofNat 1500⟩
  ]
  lintDriver := "batteries/runLinter"

require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "v4.34.1"

-- Declarations copied from unmerged Mathlib pull requests and external Lean
-- projects, shared across the papers in this repository.  Each unit names its
-- source and author; see `../../_lean_shared/Vendor/README.md`.
lean_lib Vendor where
  srcDir := "../../_lean_shared"
  globs := #[.submodules `Vendor]

-- Our own Mathlib candidates, extracted from these papers and shared across
-- them; see `../../_lean_shared/Shields/README.md`.
lean_lib Shields where
  srcDir := "../../_lean_shared"
  globs := #[.andSubmodules `Shields]

@[default_target]
lean_lib SkewBase where
  globs := #[.andSubmodules `SkewBase]
