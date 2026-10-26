-- TODO-COPIED: _papers_done/turan-bessel/lean/lakefile.lean
import Lake
open Lake DSL

package «skew-class-inflation» where
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
  leanOptions := #[⟨`weak.linter.mathlibStandardSet, false⟩]

lean_lib Shields where
  srcDir := "../../_lean_shared"
  globs := #[.submodules `Shields]

lean_lib SkewJacobiNegative where
  globs := #[.submodules `SkewJacobiNegative]

lean_lib SkewSchurReconstruction where
  globs := #[.submodules `SkewSchurReconstruction]

lean_lib SkewGluing where
  globs := #[.submodules `SkewGluing]

lean_lib SkewRibbonCoarsenings where
  globs := #[.submodules `SkewRibbonCoarsenings]

@[default_target]
lean_lib SkewClassInflation where
  globs := #[.andSubmodules `SkewClassInflation]
