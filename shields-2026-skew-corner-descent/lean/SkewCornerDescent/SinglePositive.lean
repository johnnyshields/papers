/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

/-!
# The strict scalar inequality for one positive support

Supports `shields-2026-skew-corner-descent.tex`, «Scalar and geometric refinements»
(`sec:strengthening`, `cor:one-positive-short`). This is the strict logarithmic inequality
on a common positive assignment, for any finite number of negative supports. No
independence of the values is assumed. The original determinant-coefficient transfer
remains a separate obligation. Sorry-free.
-/

namespace SkewCornerDescent.SinglePositive

open scoped BigOperators

/-- Nonnegative negative-support weights give a strict exponential bound as soon as one
positive weight is attached to a ratio different from one. -/
theorem strict_negative_weight_bound {ι : Type*} (s : Finset ι) (c x : ι → ℝ)
    (hc : ∀ i ∈ s, 0 ≤ c i) (hx : ∀ i ∈ s, 0 < x i)
    (hne : ∃ i ∈ s, 0 < c i ∧ x i ≠ 1) :
    1 + ∑ i ∈ s, c i * (1 - x i) <
      Real.exp (-(∑ i ∈ s, c i * Real.log (x i))) := by
  have hle (i : ι) (hi : i ∈ s) :
      c i * (1 - x i) ≤ -(c i * Real.log (x i)) := by
    have h := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos (hx i hi)) (hc i hi)
    linarith
  obtain ⟨i, hi, hci, hxi⟩ := hne
  have hlt : c i * (1 - x i) < -(c i * Real.log (x i)) := by
    have h := mul_lt_mul_of_pos_left (Real.log_lt_sub_one_of_pos (hx i hi) hxi) hci
    linarith
  have hs := Finset.sum_lt_sum hle ⟨i, hi, hlt⟩
  rw [Finset.sum_neg_distrib] at hs
  have he := Real.add_one_le_exp (-(∑ i ∈ s, c i * Real.log (x i)))
  linarith

/-- The one-positive-support inequality in its unnormalized form. -/
theorem strict_single_positive_support {ι : Type*} (s : Finset ι)
    (c Z : ι → ℝ) (Zp : ℝ) (hp : 0 < Zp)
    (hc : ∀ i ∈ s, 0 ≤ c i) (hZ : ∀ i ∈ s, 0 < Z i)
    (hne : ∃ i ∈ s, 0 < c i ∧ Z i ≠ Zp) :
    (1 + ∑ i ∈ s, c i) * Zp - ∑ i ∈ s, c i * Z i <
      Zp * Real.exp (-(∑ i ∈ s, c i * Real.log (Z i / Zp))) := by
  have hratio : ∃ i ∈ s, 0 < c i ∧ Z i / Zp ≠ 1 := by
    obtain ⟨i, hi, hci, hzi⟩ := hne
    exact ⟨i, hi, hci, fun he => hzi ((div_eq_one_iff_eq hp.ne').mp he)⟩
  have h := mul_lt_mul_of_pos_left
    (strict_negative_weight_bound s c (fun i => Z i / Zp) hc
      (fun i hi => div_pos (hZ i hi) hp) hratio) hp
  have he : Zp * (1 + ∑ i ∈ s, c i * (1 - Z i / Zp)) =
      (1 + ∑ i ∈ s, c i) * Zp - ∑ i ∈ s, c i * Z i := by
    rw [mul_add, mul_one, Finset.mul_sum, add_mul, one_mul, Finset.sum_mul]
    have hi (i : ι) : Zp * (c i * (1 - Z i / Zp)) = c i * Zp - c i * Z i := by
      field_simp [hp.ne']
    simp_rw [hi]
    rw [Finset.sum_sub_distrib]
    ring
  rwa [he] at h

end SkewCornerDescent.SinglePositive
