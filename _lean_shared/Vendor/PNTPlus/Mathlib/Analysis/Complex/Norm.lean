/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
/-
The upstream file carries no copyright block.  The one above is supplied here, naming
the author recorded for this path in the project's commit history, so that the copy
carries its attribution.
-/
/-
VENDORED FROM AN EXTERNAL LEAN PROJECT -- see `Vendor/PNTPlus.lean` for the full
quality audit, the licence, and the retirement condition.

* Project: PrimeNumberTheoremAnd (PNT+), <https://github.com/AlexKontorovich/PrimeNumberTheoremAnd>
* Upstream path: `PrimeNumberTheoremAnd/Mathlib/Analysis/Complex/Norm.lean`
* Revision: `7715064f690d0689f30889846f4e2c5e7ec0c47e`
* Licence: Apache 2.0.  The copyright and `Authors:` line above are upstream's.

Copied verbatim apart from the `PrimeNumberTheoremAnd.` import prefix, which becomes
`Vendor.PNTPlus.`.  Any other change is marked inline as adapted to the pin.
-/
module

public import Mathlib.Analysis.Complex.Norm

/-!
# Norm estimates for complex analysis

Elementary norm estimates used in Cartan-style product bounds and Gamma/zeta growth arguments.
-/

public section

noncomputable section

namespace Complex

variable {z : ℂ}

@[bound]
theorem neg_norm_le_re (z : ℂ) : -‖z‖ ≤ z.re :=
  neg_le_of_abs_le (abs_re_le_norm z)

/-- `‖z - 1‖ ≤ 1 + ‖z‖`. -/
lemma norm_sub_one_le_one_add_norm (z : ℂ) : ‖z - 1‖ ≤ 1 + ‖z‖ := by
  have hone : ‖(1 : ℂ)‖ = (1 : ℝ) := by simpa using Complex.norm_natCast 1
  simpa [hone, add_comm] using norm_sub_le z (1 : ℂ)

/-- `‖1 - z‖ ≤ 1 + ‖z‖`. -/
lemma norm_one_sub_le_one_add_norm (z : ℂ) : ‖1 - z‖ ≤ 1 + ‖z‖ := by
  have hone : ‖(1 : ℂ)‖ = (1 : ℝ) := by simpa using Complex.norm_natCast 1
  simpa [hone] using norm_sub_le (1 : ℂ) z

/-- If `3 < ‖z‖`, then `1 ≤ ‖1 - z‖`; the constant leaves the margin needed in the
Cartan-product estimates. -/
lemma one_le_norm_one_sub_of_norm_gt_three {z : ℂ} (hz : 3 < ‖z‖) : (1 : ℝ) ≤ ‖1 - z‖ := by
  have hge : (‖z‖ - 1 : ℝ) ≤ ‖1 - z‖ := by
    have hone : ‖(1 : ℂ)‖ = (1 : ℝ) := by simpa using Complex.norm_natCast 1
    have h := norm_sub_norm_le z (1 : ℂ)
    rw [hone, norm_sub_rev] at h
    linarith
  linarith

/-- If `‖u‖ ≥ 1`, then inverse powers of `u` have norm at most one. -/
lemma norm_inv_pow_le_one_of_one_le_norm (u : ℂ) (n : ℕ) (hu : (1 : ℝ) ≤ ‖u‖) :
    ‖(u ^ n)⁻¹‖ ≤ 1 := by
  have hge : (1 : ℝ) ≤ ‖u ^ n‖ := by
    rw [Complex.norm_pow]
    exact one_le_pow₀ hu
  calc ‖(u ^ n)⁻¹‖ = ‖(1 : ℂ) / u ^ n‖ := by rw [inv_eq_one_div]
    _ = 1 / ‖u ^ n‖ := by
        have hone : ‖(1 : ℂ)‖ = (1 : ℝ) := by simpa using Complex.norm_natCast 1
        rw [Complex.norm_div, hone]
    _ ≤ 1 := by simpa [one_div] using inv_le_one_of_one_le₀ hge

/-- The reflected point `1 - z` is not `1` if `z` is nonzero. -/
lemma one_sub_ne_one_of_norm_pos {z : ℂ} (hz : 0 < ‖z‖) : 1 - z ≠ 1 := by
  intro h
  exact hz.ne' (by simpa using sub_eq_self.mp h)

/-- A point with positive real part is not a nonpositive integer. -/
lemma ne_neg_nat_of_re_pos {w : ℂ} (hw : 0 < w.re) : ∀ n : ℕ, w ≠ -n := by
  intro n hn
  have hre : w.re = -(n : ℝ) := by
    have := congrArg Complex.re hn
    simpa using this
  nlinarith

end Complex
