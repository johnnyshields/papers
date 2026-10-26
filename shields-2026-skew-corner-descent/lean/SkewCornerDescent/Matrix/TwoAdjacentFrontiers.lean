/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.HessenbergMarkedFrontierReduction

/-!
# Exact coefficient aggregation over adjacent selected costs

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
The residue functional and first-normal functional act on the two complete
marked sums separately. No coefficient of an individual activity is frozen.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix

/-- Two consecutive nonnegative costs aggregate under independent additive
coefficient functionals. The positive target prevents the truncated zero-cost overlap. -/
theorem sum_two_adjacent_frontiers {ι S R : Type*} [Fintype ι]
    [AddCommMonoid S] [Semiring R]
    (admissible : ι → Prop) [DecidablePred admissible] (cost : ι → ℕ) (marked : ι → S)
    (L₀ L₁ : S →+ R) (a b : R) (m : ℕ) (hm : 0 < m) :
    (∑ i, if admissible i then
      if cost i = m then a * L₀ (marked i)
      else if cost i + 1 = m then b * L₁ (marked i) else 0 else 0) =
    a * L₀ (∑ i, if admissible i ∧ cost i = m then marked i else 0) +
      b * L₁ (∑ i, if admissible i ∧ cost i = m - 1 then marked i else 0) := by
  rw [map_sum, map_sum]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : admissible i
  · by_cases hc : cost i = m
    · have hl : ¬ (admissible i ∧ cost i = m - 1) := by
        intro h
        omega
      rw [ite_eq_left hi, ite_eq_left hc, ite_eq_left ⟨hi, hc⟩,
        ite_eq_right hl, map_zero, mul_zero, add_zero]
    · have hfull : ¬ (admissible i ∧ cost i = m) := fun h => hc h.2
      by_cases hl : cost i = m - 1
      · have hnext : cost i + 1 = m := by omega
        rw [ite_eq_left hi, ite_eq_right hc, ite_eq_left hnext,
          ite_eq_right hfull, ite_eq_left ⟨hi, hl⟩, map_zero, mul_zero, zero_add]
      · have hnext : cost i + 1 ≠ m := by omega
        have hlow : ¬ (admissible i ∧ cost i = m - 1) := fun h => hl h.2
        rw [ite_eq_left hi, ite_eq_right hc, ite_eq_right hnext,
          ite_eq_right hfull, ite_eq_right hlow, map_zero, map_zero,
          mul_zero, mul_zero, add_zero]
  · have hfull : ¬ (admissible i ∧ cost i = m) := fun h => hi h.1
    have hlow : ¬ (admissible i ∧ cost i = m - 1) := fun h => hi h.1
    rw [ite_eq_right hi, ite_eq_right hfull, ite_eq_right hlow,
      map_zero, map_zero, mul_zero, mul_zero, add_zero]

end SkewCornerDescent.Matrix
