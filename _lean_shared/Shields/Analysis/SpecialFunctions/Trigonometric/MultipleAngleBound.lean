/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith

/-!
# A multiple angle's sine is bounded by the angle's

`|sin (nθ)| ≤ n |sin θ|` for every natural `n`.  The addition formula splits `sin ((m+1)θ)` into
`sin (mθ) cos θ + cos (mθ) sin θ`, and both cosines are bounded by `1`, so each step of the
induction costs exactly one `|sin θ|`.

The constant `n` cannot be lowered: `sin (nθ) / sin θ → n` as `θ → 0`.  Mathlib carries
`Real.abs_sin_le_abs` (`|sin x| ≤ |x|`) and the Lipschitz bound `Real.abs_sin_sub_sin_le`, neither
of which compares a harmonic with the first harmonic.

The use is Fourier: against a density that is nonnegative in `sin θ`, this bounds the `n`-th sine
coefficient by `n` times the first, which is what turns a one-sided sign condition into a
coefficient estimate.

## Main results

* `Shields.abs_sin_natCast_mul_le` -- `|sin (nθ)| ≤ n |sin θ|`.

Used by `edrei-spectral-classification` and `zero-reconstruction-edrei`.

## Tags

sine, multiple angle, harmonic, Fourier coefficient
-/

open Real

namespace Shields

/-- `|sin (nθ)| ≤ n |sin θ|`: the elementary inequality that compares a higher harmonic with the
first one against a nonnegative density. -/
theorem abs_sin_natCast_mul_le (n : ℕ) (θ : ℝ) :
    |Real.sin (n * θ)| ≤ n * |Real.sin θ| := by
  induction n with
  | zero => simp
  | succ m ih =>
      have hstep : ((m : ℝ) + 1) * θ = (m : ℝ) * θ + θ := by ring
      have hcalc : |Real.sin ((m : ℝ) * θ + θ)| ≤ |Real.sin ((m : ℝ) * θ)| + |Real.sin θ| := by
        rw [Real.sin_add]
        calc |Real.sin ((m : ℝ) * θ) * Real.cos θ + Real.cos ((m : ℝ) * θ) * Real.sin θ|
            ≤ |Real.sin ((m : ℝ) * θ) * Real.cos θ| + |Real.cos ((m : ℝ) * θ) * Real.sin θ| :=
              abs_add_le _ _
          _ = |Real.sin ((m : ℝ) * θ)| * |Real.cos θ|
                + |Real.cos ((m : ℝ) * θ)| * |Real.sin θ| := by rw [abs_mul, abs_mul]
          _ ≤ |Real.sin ((m : ℝ) * θ)| * 1 + 1 * |Real.sin θ| := by
              gcongr
              · exact Real.abs_cos_le_one θ
              · exact Real.abs_cos_le_one _
          _ = |Real.sin ((m : ℝ) * θ)| + |Real.sin θ| := by ring
      push_cast
      rw [hstep]
      refine hcalc.trans ?_
      have : |Real.sin ((m : ℝ) * θ)| ≤ (m : ℝ) * |Real.sin θ| := by exact_mod_cast ih
      linarith


/-! ### Axiom footprint -/

/-- info: 'Shields.abs_sin_natCast_mul_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms abs_sin_natCast_mul_le

end Shields
