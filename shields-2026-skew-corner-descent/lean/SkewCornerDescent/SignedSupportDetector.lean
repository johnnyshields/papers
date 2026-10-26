/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.SinglePositive
import Mathlib.Analysis.MeanInequalities

/-!
# Finite positive-mean signed-support detector

Supports `shields-2026-skew-corner-descent.tex` (`cor:one-positive-short`).
Finite Jensen supplies the geometric-mean bound used by the strict single-positive
support inequality. All values use one assignment; their independence is not assumed.
The logarithmic product balance is an explicit input. Its identification with the
actual cyclic windows and the original coefficient transfer remain separate obligations.
Sorry-free.
-/

namespace SkewCornerDescent.SinglePositive

open scoped BigOperators

/-- A finite positive mean with the stated product balance strictly exceeds the signed
single-positive-support expression, for any finite number of negative supports. -/
theorem finite_mean_signed_detector {ι κ : Type*} (s : Finset ι) (u : Finset κ)
    (c Z : ι → ℝ) (w V : κ → ℝ) (Zp : ℝ) (hp : 0 < Zp)
    (hc : ∀ i ∈ s, 0 ≤ c i) (hZ : ∀ i ∈ s, 0 < Z i)
    (hne : ∃ i ∈ s, 0 < c i ∧ Z i ≠ Zp)
    (hw : ∀ j ∈ u, 0 ≤ w j) (hw' : ∑ j ∈ u, w j = 1) (hV : ∀ j ∈ u, 0 < V j)
    (hbalance : ∑ j ∈ u, w j * Real.log (V j) =
      Real.log Zp - ∑ i ∈ s, c i * Real.log (Z i / Zp)) :
    0 < (∑ j ∈ u, w j * V j) - ((1 + ∑ i ∈ s, c i) * Zp - ∑ i ∈ s, c i * Z i) ∧
      (∑ j ∈ u, w j * V j) - ((1 + ∑ i ∈ s, c i) * Zp - ∑ i ∈ s, c i * Z i) ≠ 0 := by
  have hJ := convexOn_exp.map_sum_le hw hw'
    (fun j _ => Set.mem_univ (Real.log (V j)))
  simp only [smul_eq_mul] at hJ
  have hR : ∑ j ∈ u, w j * Real.exp (Real.log (V j)) = ∑ j ∈ u, w j * V j :=
    Finset.sum_congr rfl (fun j hj => by rw [Real.exp_log (hV j hj)])
  rw [hbalance, sub_eq_add_neg, Real.exp_add, Real.exp_log hp, hR] at hJ
  have hstrict := strict_single_positive_support s c Z Zp hp hc hZ hne
  have hpos : 0 < (∑ j ∈ u, w j * V j) -
      ((1 + ∑ i ∈ s, c i) * Zp - ∑ i ∈ s, c i * Z i) := by linarith
  exact ⟨hpos, ne_of_gt hpos⟩

end SkewCornerDescent.SinglePositive
