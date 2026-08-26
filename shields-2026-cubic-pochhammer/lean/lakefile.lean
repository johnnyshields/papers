import Lake
open Lake DSL

package «cubic-pochhammer-turan» where
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

@[default_target]
lean_lib CubicPochhammer where
  globs := #[.andSubmodules `CubicPochhammer]
