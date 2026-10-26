/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.SignedSupportDetector

/-!
# Signed weights with one positive support

Supports `shields-2026-skew-corner-descent.tex` (`lem:two-support`,
`cor:one-positive-short`). The positive mass and logarithmic ratio balance are
produced from a signed weight family of total one. Zero-weight classes may remain;
no position or response class is deleted. Sorry-free.
-/

namespace SkewCornerDescent.SinglePositive

open scoped BigOperators

/-- A positive finite mean strictly exceeds a signed mean with exactly one
positive weight, provided the same actual logarithmic balance holds. The negative
support need not have a fixed cardinality. -/
theorem finite_mean_one_positive_weights {α κ : Type*}
    [Fintype α] (weight Z : α → ℝ) (p : α)
    (hweight : ∑ a, weight a = 1) (hothers : ∀ a, a ≠ p → weight a ≤ 0)
    (hZ : ∀ a, 0 < Z a) (hnegative : ∃ a, weight a < 0 ∧ Z a ≠ Z p)
    (u : Finset κ) (meanWeight V : κ → ℝ)
    (hw : ∀ i ∈ u, 0 ≤ meanWeight i) (hwone : ∑ i ∈ u, meanWeight i = 1)
    (hV : ∀ i ∈ u, 0 < V i)
    (hbalance : ∑ i ∈ u, meanWeight i * Real.log (V i) =
      ∑ a, weight a * Real.log (Z a)) :
    0 < (∑ i ∈ u, meanWeight i * V i) - ∑ a, weight a * Z a := by
  classical
  let negative := Finset.univ.erase p
  let c := fun a => -weight a
  have hmass : weight p = 1 + ∑ a ∈ negative, c a := by
    have he := Finset.add_sum_erase Finset.univ weight (Finset.mem_univ p)
    rw [hweight] at he
    simp only [c, Finset.sum_neg_distrib]
    linarith
  have hc : ∀ a ∈ negative, 0 ≤ c a := by
    intro a ha
    exact neg_nonneg.mpr (hothers a (Finset.mem_erase.mp ha).1)
  have hne : ∃ a ∈ negative, 0 < c a ∧ Z a ≠ Z p := by
    obtain ⟨a, hwa, hza⟩ := hnegative
    have hap : a ≠ p := by
      intro heq
      subst a
      exact hza rfl
    exact ⟨a, Finset.mem_erase.mpr ⟨hap, Finset.mem_univ _⟩, neg_pos.mpr hwa, hza⟩
  have hlog (a : α) : Real.log (Z a / Z p) = Real.log (Z a) - Real.log (Z p) :=
    Real.log_div (hZ a).ne' (hZ p).ne'
  have hbalance' : ∑ i ∈ u, meanWeight i * Real.log (V i) =
      Real.log (Z p) - ∑ a ∈ negative, c a * Real.log (Z a / Z p) := by
    rw [hbalance, ← Finset.add_sum_erase Finset.univ
      (fun a => weight a * Real.log (Z a)) (Finset.mem_univ p), hmass]
    simp_rw [hlog, mul_sub]
    simp only [c, neg_mul, Finset.sum_sub_distrib, Finset.sum_neg_distrib,
      ← Finset.sum_mul]
    ring
  have hsplit : ∑ a, weight a * Z a =
      (1 + ∑ a ∈ negative, c a) * Z p - ∑ a ∈ negative, c a * Z a := by
    rw [← Finset.add_sum_erase Finset.univ (fun a => weight a * Z a)
      (Finset.mem_univ p), hmass]
    simp only [c, negative, neg_mul, Finset.sum_neg_distrib, sub_neg_eq_add]
  have hstrict := finite_mean_signed_detector negative u c Z meanWeight V (Z p)
    (hZ p) hc (fun a _ => hZ a) hne hw hwone hV hbalance'
  rw [hsplit]
  exact hstrict.1

end SkewCornerDescent.SinglePositive
