/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# A majorant of order `1/ρ` at every radius pins a real number

Two forms of the same closing move.  A quantity admitting the bound `C / ρ` at *every* `ρ ≥ 1`
admits it in the limit, where `C / ρ` is `0`; a two-sided bound then forces the quantity to
vanish and a one-sided bound forces it to be nonnegative.

The hypothesis is stated as a bound holding for each `ρ` separately, which is the form a radius
sweep produces: an estimate is available on every circle, the constant `C` does not move with the
radius, and no single circle says anything.  Mathlib's `ge_of_tendsto` and `le_of_tendsto` do the
limiting, and what is packaged here is the `C / ρ` majorant and the `1 ≤ ρ` eventuality.

## Main results

* `Shields.eq_zero_of_abs_le_const_div` -- `|x| ≤ C / ρ` for every `ρ ≥ 1` forces `x = 0`.
* `Shields.nonneg_of_neg_const_div_le` -- `-(C / ρ) ≤ x` for every `ρ ≥ 1` forces `0 ≤ x`.

Used by `edrei-spectral-classification` and `zero-reconstruction-edrei`.

## Tags

limit, majorant, radius sweep, Liouville
-/

namespace Shields

/-- A nonnegative quantity dominated by `C/ρ` for every large `ρ` is zero. -/
theorem eq_zero_of_abs_le_const_div {x C : ℝ} (h : ∀ ρ : ℝ, 1 ≤ ρ → |x| ≤ C / ρ) :
    x = 0 := by
  have hlim : Filter.Tendsto (fun ρ : ℝ => C / ρ) Filter.atTop (nhds 0) :=
    Filter.Tendsto.div_atTop tendsto_const_nhds Filter.tendsto_id
  have h0 : |x| ≤ 0 := ge_of_tendsto hlim (Filter.eventually_atTop.2 ⟨1, fun ρ hρ => h ρ hρ⟩)
  exact abs_eq_zero.1 (le_antisymm h0 (abs_nonneg x))

/-- A quantity bounded below by `-(C/ρ)` for every large `ρ` is nonnegative. -/
theorem nonneg_of_neg_const_div_le {x C : ℝ} (h : ∀ ρ : ℝ, 1 ≤ ρ → -(C / ρ) ≤ x) :
    0 ≤ x := by
  have hlim : Filter.Tendsto (fun ρ : ℝ => -(C / ρ)) Filter.atTop (nhds 0) := by
    simpa using (Filter.Tendsto.div_atTop (tendsto_const_nhds (x := C)) Filter.tendsto_id).neg
  exact le_of_tendsto hlim (Filter.eventually_atTop.2 ⟨1, fun ρ hρ => h ρ hρ⟩)


/-! ### Axiom footprint -/

/-- info: 'Shields.eq_zero_of_abs_le_const_div' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms eq_zero_of_abs_le_const_div

/-- info: 'Shields.nonneg_of_neg_const_div_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms nonneg_of_neg_const_div_le

end Shields
