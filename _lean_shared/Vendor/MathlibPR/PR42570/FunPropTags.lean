/-
Vendored from Mathlib pull request #42570, `chore: add tag `fun_prop` to `MeromorphicOn` and
`AnalyticOnNhd``, by Stefan Kebekus (GitHub `kebekus`).

  https://github.com/leanprover-community/mathlib4/pull/42570

The PR is merged upstream but postdates the pinned Mathlib revision.  Almost all of it is a
`@[fun_prop]` attribute added to declarations the pinned Mathlib already carries verbatim, so the
copy here is the corresponding `attribute [fun_prop]` commands rather than a copy of the
declarations.  Two neighbouring post-pin PRs tag declarations in the same discharge path, and their
tags are applied here as well so that a single import restores the upstream `fun_prop` behaviour:
`Complex.meromorphic_canonicalFactor` and `Complex.analyticOnNhd_canonicalFactor`.

Where the PR also *changes* a statement, the change is not reproduced --- see the note at
`analyticOnNhd_circleMap` below.

When the pin is bumped past these PRs, delete this file.  The tags then arrive with Mathlib and the
commands here become redundant rather than wrong, so a stale copy is caught by the import graph
rather than by a duplicate-declaration error.

Upstream copyright and authorship follow, verbatim.
-/

/-
Copyright (c) 2026 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
import Mathlib.Analysis.Complex.CanonicalDecomposition
import Mathlib.Analysis.Meromorphic.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.MeasureTheory.Integral.CircleIntegral

attribute [fun_prop]
  MeromorphicOn
  AnalyticOnNhd.meromorphicOn
  MeromorphicOn.id
  MeromorphicOn.const
  MeromorphicOn.add MeromorphicOn.fun_add
  MeromorphicOn.sub MeromorphicOn.fun_sub
  MeromorphicOn.neg MeromorphicOn.fun_neg
  MeromorphicOn.smul MeromorphicOn.fun_smul
  MeromorphicOn.const_smul MeromorphicOn.fun_const_smul
  MeromorphicOn.mul MeromorphicOn.fun_mul
  MeromorphicOn.prod MeromorphicOn.fun_prod MeromorphicOn.finprod
  MeromorphicOn.sum MeromorphicOn.fun_sum MeromorphicOn.finsum
  MeromorphicOn.inv MeromorphicOn.fun_inv
  MeromorphicOn.div MeromorphicOn.fun_div
  MeromorphicOn.pow MeromorphicOn.fun_pow
  MeromorphicOn.zpow MeromorphicOn.fun_zpow
  MeromorphicOn.deriv MeromorphicOn.iterated_deriv
  Meromorphic.meromorphicOn
  AnalyticOnNhd
  analyticOnNhd_const
  analyticOnNhd_id
  AnalyticOnNhd.add
  AnalyticOnNhd.neg
  AnalyticOnNhd.sub
  AnalyticOnNhd.const_smul AnalyticOnNhd.fun_const_smul
  AnalyticOnNhd.div_const
  AnalyticOnNhd.prod
  AnalyticOnNhd.smul
  AnalyticOnNhd.mul
  AnalyticOnNhd.pow AnalyticOnNhd.fun_pow
  AnalyticOnNhd.inv AnalyticOnNhd.fun_inv
  AnalyticOnNhd.zpow AnalyticOnNhd.fun_zpow
  AnalyticOnNhd.div
  Finset.analyticOnNhd_sum Finset.analyticOnNhd_fun_sum
  Finset.analyticOnNhd_prod Finset.analyticOnNhd_fun_prod
  analyticOnNhd_cexp
  analyticOnNhd_rexp
  Complex.analyticOnNhd_sin Complex.analyticOnNhd_cos
  Complex.analyticOnNhd_sinh Complex.analyticOnNhd_cosh
  Complex.meromorphic_canonicalFactor
  Complex.analyticOnNhd_canonicalFactor

-- Adapted to the pinned revision: for these three the pull request tags the `Pi`-form theorem with
-- `@[to_fun (attr := fun_prop)]`, and it is the generated `fun`-variant that `fun_prop` uses on a
-- lambda goal.  A `to_fun` tag cannot be added from outside the defining module, so the variants
-- are stated here under their upstream names; each is the pinned theorem, the two forms being
-- definitionally equal.
section AnalyticOnNhdFunVariants

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {f g : E → F} {s : Set E}

@[fun_prop]
theorem AnalyticOnNhd.fun_add (hf : AnalyticOnNhd 𝕜 f s) (hg : AnalyticOnNhd 𝕜 g s) :
    AnalyticOnNhd 𝕜 (fun x ↦ f x + g x) s :=
  hf.add hg

@[fun_prop]
theorem AnalyticOnNhd.fun_neg (hf : AnalyticOnNhd 𝕜 f s) :
    AnalyticOnNhd 𝕜 (fun x ↦ -f x) s :=
  hf.neg

@[fun_prop]
theorem AnalyticOnNhd.fun_sub (hf : AnalyticOnNhd 𝕜 f s) (hg : AnalyticOnNhd 𝕜 g s) :
    AnalyticOnNhd 𝕜 (fun x ↦ f x - g x) s :=
  hf.sub hg

end AnalyticOnNhdFunVariants
