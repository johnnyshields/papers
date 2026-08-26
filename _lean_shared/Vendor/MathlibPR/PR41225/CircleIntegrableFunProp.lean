/-
Vendored from Mathlib pull request #41225, `feat: tag circle integrability as fun_prop`,

  https://github.com/leanprover-community/mathlib4/pull/41225

by Stefan Kebekus (GitHub `kebekus`).  The pull request is merged upstream but postdates the
Mathlib revision pinned by this repository.

The pull request does three things: it registers `CircleIntegrable` and its closure lemmas with
`fun_prop`, it adds `circleIntegrable_id` and the two `f • g` / `f * g` companions of the existing
`g • f` / `g * f` lemmas, and it renames `smul_of_continuousOn` / `mul_of_continuousOn` to
`continuousOn_smul` / `continuousOn_mul`.  Only what the pinned revision lacks is reproduced: the
attributes, the new declarations, and the new names supplied as aliases so that consuming code is
written exactly as it will be against a merged Mathlib.

Two adaptations to the pinned revision, both marked inline below:
* upstream carries the attribute through `@[to_fun (attr := fun_prop)]`, which also regenerates the
  `fun_`-variants; here the variants already exist under the same names, so the attribute is applied
  to them directly and the two genuinely new `fun_`-variants are stated explicitly;
* upstream deprecates the old names, which cannot be done from outside the defining module, so the
  new names are aliases of the old ones rather than the other way round.

When this material reaches the Mathlib pin, delete this file.  The aliases retire with it: their
upstream definitions carry the same statements under the same names.

Upstream copyright and authorship follow, verbatim.
-/

/-
Copyright (c) 2026 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Analysis.SpecialFunctions.Integrability.LogMeromorphic
import Mathlib.Analysis.SpecialFunctions.Integrals.PosLogEqCircleAverage

/-!
## Circle integrability as a `fun_prop` goal
-/

open MeasureTheory Metric Real Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

-- Adapted to the pinned revision: upstream writes these attributes at the declarations, and lets
-- `@[to_fun (attr := fun_prop)]` propagate them to the `fun_`-variants.
attribute [fun_prop]
  CircleIntegrable
  circleIntegrable_const
  CircleIntegrable.abs
  CircleIntegrable.add
  CircleIntegrable.fun_add
  CircleIntegrable.sub
  CircleIntegrable.fun_sub
  CircleIntegrable.sum
  CircleIntegrable.fun_sum
  CircleIntegrable.finsum
  CircleIntegrable.neg
  CircleIntegrable.const_smul
  CircleIntegrable.const_fun_smul
  CircleIntegrable.smul_of_continuousOn
  CircleIntegrable.fun_smul_of_continuousOn
  CircleIntegrable.mul_of_continuousOn
  CircleIntegrable.fun_mul_of_continuousOn
  ContinuousOn.circleIntegrable'
  circleIntegrable_log_norm_sub_const
  circleIntegrable_log_norm_factorizedRational

@[fun_prop]
theorem circleIntegrable_id (c : ℂ) (R : ℝ) : CircleIntegrable (fun z => z) c R :=
  (continuous_circleMap c R).intervalIntegrable 0 (2 * π)

namespace CircleIntegrable

variable {f g : ℂ → E} {c : ℂ} {R : ℝ}
variable {𝕜 F : Type*} [NormedRing 𝕜] [NormedAddCommGroup F] [Module 𝕜 F] [NormSMulClass 𝕜 F]

/--
If `f` is circle integrable and `g` is continuous on the circle `sphere c |R|`, then `f • g` is
circle integrable.
-/
@[fun_prop]
theorem smul_continuousOn {f : ℂ → 𝕜} {g : ℂ → F} (hf : CircleIntegrable f c R)
    (hg : ContinuousOn g (sphere c |R|)) :
    CircleIntegrable (f • g) c R :=
  IntervalIntegrable.smul_continuousOn hf
    (hg.comp (by fun_prop) (fun x hx ↦ circleMap_mem_sphere' c R x))

/--
If `f` is circle integrable and `g` is continuous on the circle `sphere c |R|`, then `f • g` is
circle integrable.
-/
@[fun_prop]
theorem fun_smul_continuousOn {f : ℂ → 𝕜} {g : ℂ → F} (hf : CircleIntegrable f c R)
    (hg : ContinuousOn g (sphere c |R|)) :
    CircleIntegrable (fun z ↦ f z • g z) c R :=
  hf.smul_continuousOn hg

/--
If `f` is circle integrable and `g` is continuous on the circle `sphere c |R|`, then `f * g` is
circle integrable.
-/
@[fun_prop]
theorem mul_continuousOn {f g : ℂ → 𝕜} (hf : CircleIntegrable f c R)
    (hg : ContinuousOn g (sphere c |R|)) :
    CircleIntegrable (f * g) c R :=
  IntervalIntegrable.mul_continuousOn hf
    (hg.comp (by fun_prop) (fun x hx ↦ circleMap_mem_sphere' c R x))

/--
If `f` is circle integrable and `g` is continuous on the circle `sphere c |R|`, then `f * g` is
circle integrable.
-/
@[fun_prop]
theorem fun_mul_continuousOn {f g : ℂ → 𝕜} (hf : CircleIntegrable f c R)
    (hg : ContinuousOn g (sphere c |R|)) :
    CircleIntegrable (fun z ↦ f z * g z) c R :=
  hf.mul_continuousOn hg

-- Adapted to the pinned revision: upstream renames the four declarations below and deprecates the
-- old names.  A deprecation cannot be added from outside the defining module, so the upstream names
-- are introduced here as aliases of the pinned ones.
alias continuousOn_smul := smul_of_continuousOn
alias fun_continuousOn_smul := fun_smul_of_continuousOn
alias continuousOn_mul := mul_of_continuousOn
alias fun_continuousOn_mul := fun_mul_of_continuousOn

end CircleIntegrable
