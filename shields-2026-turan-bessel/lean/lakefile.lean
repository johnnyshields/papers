import Lake
open Lake DSL

package «turan-bessel» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩,
    ⟨`weak.linter.mathlibStandardSet, true⟩,
    ⟨`weak.linter.style.header, false⟩,      -- replaced by our own doc.header* checks
    ⟨`weak.linter.style.longFile, .ofNat 1500⟩
  ]
  lintDriver := "batteries/runLinter"

require mathlib from git "https://github.com/leanprover-community/mathlib4" @
  "07de3072413e608bacca32c543e792a37815be64"

-- Declarations copied from unmerged Mathlib pull requests, shared across the
-- papers in this repository.  Each file names its source PR and that PR's
-- author; see `../../_lean_shared/Vendor/README.md`.  Delete a vendored file
-- when its PR merges and the Mathlib pin is bumped.
lean_lib Vendor where
  srcDir := "../../_lean_shared"
  globs := #[.submodules `Vendor]

@[default_target]
lean_lib TuranBessel where
  globs := #[.andSubmodules `TuranBessel]
