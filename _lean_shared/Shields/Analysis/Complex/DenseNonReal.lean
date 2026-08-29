/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib.Analysis.Complex.Basic

/-!
# The non-real points are dense in the plane

`{z : ℂ | z.im ≠ 0}` is dense: every ball around `z` contains `z ± (r/2) i`, and the sign is
chosen by the sign of `Im z` so the perturbation never returns to the axis.

The use is extension off the real axis.  A representation valid only where `z.im ≠ 0` -- because
the axis carries poles, or because a reflection hypothesis is stated there -- still determines a
continuous function everywhere, since two continuous functions agreeing on a dense set agree
(`Continuous.ext_on`).

## Main results

* `Shields.dense_im_ne_zero` -- the non-real points are dense in `ℂ`.

Used by `edrei-spectral-classification` and `zero-reconstruction-edrei`.

## Tags

dense, real axis, imaginary part, continuous extension
-/

namespace Shields

/-- The non-real points are dense in the plane. -/
theorem dense_im_ne_zero : Dense {z : ℂ | z.im ≠ 0} := by
  rw [Metric.dense_iff]
  intro z r hr
  refine ⟨z + ((if 0 ≤ z.im then r / 2 else -(r / 2) : ℝ) : ℂ) * Complex.I, ?_, ?_⟩
  · have habs : |(if 0 ≤ z.im then r / 2 else -(r / 2) : ℝ)| = r / 2 := by
      split_ifs
      · exact abs_of_pos (by linarith)
      · rw [abs_neg]; exact abs_of_pos (by linarith)
    rw [Metric.mem_ball, dist_eq_norm,
      show z + ((if 0 ≤ z.im then r / 2 else -(r / 2) : ℝ) : ℂ) * Complex.I - z
        = ((if 0 ≤ z.im then r / 2 else -(r / 2) : ℝ) : ℂ) * Complex.I by ring]
    simp only [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, habs]
    linarith
  · simp only [Set.mem_ofPred_eq, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_im, Complex.ofReal_im, Complex.I_re, mul_one, mul_zero, add_zero]
    split_ifs with h
    · exact ne_of_gt (by linarith)
    · exact ne_of_lt (by have := not_le.mp h; linarith)


/-! ### Axiom footprint -/

/-- info: 'Shields.dense_im_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms dense_im_ne_zero

end Shields
