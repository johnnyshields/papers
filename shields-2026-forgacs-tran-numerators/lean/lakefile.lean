import Lake
open Lake DSL

package «forgacs-tran» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩,
    ⟨`weak.linter.mathlibStandardSet, true⟩,
    -- `style.header` compares the second copyright line against the literal
    -- "Released under Apache 2.0 license as described in the file LICENSE."
    -- (`Mathlib/Tactic/Linter/Header.lean:241`, an exact string equality with no
    -- alternatives).  Every module here carries a truthful MIT header, which
    -- fails that check on both the license name and the filename.  So the only
    -- license line this linter accepts is a FALSE statement about this tree --
    -- it is not that we happen to lack headers.  The rest of the block passes:
    -- the copyright and `Authors:` lines match the checks at :209-:227, and the
    -- license line is the sole obstruction.  Every other linter in the standard
    -- set applies and is left on.
    ⟨`weak.linter.style.header, false⟩,
    ⟨`weak.linter.style.longFile, .ofNat 1500⟩
  ]
  lintDriver := "batteries/runLinter"

require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "master"

-- Declarations copied from unmerged Mathlib pull requests, shared across the
-- papers in this repository.  Each file names its source PR and that PR's
-- author; see `../../_lean_shared/Vendor/README.md`.  Delete a vendored file
-- when its PR merges and the Mathlib pin is bumped.
lean_lib Vendor where
  srcDir := "../../_lean_shared"
  globs := #[.submodules `Vendor]

-- Our own Mathlib candidates, extracted from these papers and shared across
-- them, written in the form a Mathlib pull request would take; see
-- `../../_lean_shared/Shields/README.md`.  The namespace is `Shields` rather
-- than the upstream one so that nothing here can clash with Mathlib.
lean_lib Shields where
  srcDir := "../../_lean_shared"
  globs := #[.andSubmodules `Shields]

@[default_target]
lean_lib ForgacsTran where
  globs := #[.andSubmodules `ForgacsTran]
