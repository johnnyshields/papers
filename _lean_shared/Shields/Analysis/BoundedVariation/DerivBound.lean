/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.EMetricSpace.BoundedVariation

/-!
# A derivative bound is a variation bound

A Lipschitz function on a set contained in `Icc a b` has total variation at most `C (b - a)`
there, and a function differentiable on `Ioo a b` with `|f'| ≤ κ` has total variation at most
`κ (b - a)` on that interval.  Mathlib reaches the conclusion only through
`LipschitzOnWith.comp_eVariationOn_le`, which composes a Lipschitz map with a function
already known to have bounded variation, and through
`LipschitzOnWith.locallyBoundedVariationOn`, which gives finiteness without a constant.
The quantitative statement, with the constant `C (b - a)`, is not there.

The interval of the derivative bound is deliberately **open**.  The mean value inequality is
applied on the convex set `Ioo a b`, so nothing is asked of `f` at the endpoints -- which is
what a function differentiable on an open arc and nowhere else can supply.

## Main results

* `Shields.eVariationOn_le_of_lipschitzOnWith` -- `eVariationOn f s ≤ C (b - a)` for
  `s ⊆ Icc a b`.
* `Shields.eVariationOn_le_of_abs_deriv_le` -- `eVariationOn f (Ioo a b) ≤ κ (b - a)`.

Used by `forgacs-tran-numerators`.

## Tags

bounded variation, total variation, mean value inequality, derivative bound
-/

open Set
open scoped NNReal ENNReal

namespace Shields

/-- **A Lipschitz function has a variation bound on every set inside an interval.**  The
identity has variation `b - a` on `Icc a b`, and composing with a `C`-Lipschitz map multiplies
the variation by at most `C`. -/
theorem eVariationOn_le_of_lipschitzOnWith {E : Type*} [PseudoEMetricSpace E]
    {f : ℝ → E} {s : Set ℝ} {a b : ℝ} {C : ℝ≥0}
    (hf : LipschitzOnWith C f s) (hs : s ⊆ Set.Icc a b) :
    eVariationOn f s ≤ C * ENNReal.ofReal (b - a) := by
  rcases s.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
  · simp
  have hab : a ≤ b := (hs hx).1.trans (hs hx).2
  have hid : eVariationOn (id : ℝ → ℝ) s ≤ ENNReal.ofReal (b - a) := by
    simpa using eVariationOn.mono id hs
  simpa using (hf.comp_eVariationOn_le (Set.mapsTo_id s)).trans (by gcongr)

/-- **A derivative bound gives a variation bound, on the OPEN interval.**  The mean value
inequality on the convex set `Ioo a b` makes `f` Lipschitz there, and a Lipschitz function has
variation at most `κ (b - a)` on a set inside `Icc a b`. -/
theorem eVariationOn_le_of_abs_deriv_le {f f' : ℝ → ℝ} {a b κ : ℝ} (hκ : 0 ≤ κ)
    (hd : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x)
    (hbd : ∀ x ∈ Ioo a b, |f' x| ≤ κ) :
    eVariationOn f (Ioo a b) ≤ ENNReal.ofReal (κ * (b - a)) := by
  have hlip : LipschitzOnWith κ.toNNReal f (Ioo a b) :=
    (convex_Ioo a b).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
      (fun x hx => (hd x hx).hasDerivWithinAt)
      (fun x hx => by
        rw [← NNReal.coe_le_coe, coe_nnnorm, Real.norm_eq_abs, Real.coe_toNNReal κ hκ]
        exact hbd x hx)
  refine (eVariationOn_le_of_lipschitzOnWith hlip Set.Ioo_subset_Icc_self).trans ?_
  exact le_of_eq (ENNReal.ofReal_mul hκ).symm


/-! ### Axiom footprint -/

/-- info: 'Shields.eVariationOn_le_of_abs_deriv_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms eVariationOn_le_of_abs_deriv_le

end Shields
