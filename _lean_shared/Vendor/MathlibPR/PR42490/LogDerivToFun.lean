/-
Vendored from Mathlib pull request #42490, `chore: add `to_fun` tag to theorems on logarithmic
derivations`, by Stefan Kebekus (GitHub `kebekus`).

  https://github.com/leanprover-community/mathlib4/pull/42490

The pull request is merged upstream but lands after the Mathlib revision pinned by this repository.
It restates `logDeriv_mul`, `logDeriv_div` and `logDeriv_prod` of
`Mathlib/Analysis/Calculus/LogDeriv.lean` in `Pi` form and lets `@[to_fun]` generate the
`fun`-variants under the names used here.

Upstream copyright and authorship follow, verbatim.
-/

/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.Analysis.Calculus.LogDeriv

-- Adapted to the pinned revision: at the pin these three theorems are already stated in the
-- `fun`-form the pull request moves to the generated variants, and a `to_fun` tag cannot be added
-- from outside the defining module, so the upstream names are introduced here as aliases of the
-- pinned ones.  After the pin is bumped the aliases become duplicates and this file is deleted.
alias logDeriv_fun_mul := logDeriv_mul
alias logDeriv_fun_div := logDeriv_div
alias logDeriv_fun_prod := logDeriv_prod
