/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.FiniteVirtualClosureWindows

/-!
# Gap-filtered complete closure inventories

Supports `shields-2026-skew-corner-descent.tex` (`lem:maximal-bin`). Only starts
with the specified gap sum are retained. Changing the actual closure response
scales each crossing window once, without deleting repeated response positions.
Sorry-free.
-/

namespace SkewCornerDescent.CyclicWindows

open scoped BigOperators

/-- Complete cyclic inverse inventory at one geometric gap sum. -/
noncomputable def filteredInverseWindowSum {B : ℕ} [NeZero B] {F : Type*} [Field F]
    (f : ZMod B → F) (g : ZMod B → ℤ) (j : ℕ) (M : ℤ) : F :=
  ∑ i, if windowSum g 1 j i = M then (windowProduct f 1 j i)⁻¹ else 0

/-- If every retained window crosses the closure position, its complete inverse
inventory is a common context times the inverse closure response. The identity
also holds at zero under the field's total inverse convention. -/
theorem filteredInverseWindowSum_closure_scale {B : ℕ} [NeZero B]
    {F : Type*} [Field F] (l : Fin (B - 1) → F) (S : F)
    (g : ZMod B → ℤ) (j : ℕ) (hj : j ≤ B) (M : ℤ)
    (hnoncross : ∀ i : ZMod B, i.val < B - j → windowSum g 1 j i ≠ M) :
    filteredInverseWindowSum (completeResponseCycle l S) g j M =
      filteredInverseWindowSum (completeResponseCycle l 1) g j M / S := by
  classical
  unfold filteredInverseWindowSum
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hret : windowSum g 1 j i = M
  · have hcross : B - j ≤ i.val := by
      by_contra h
      exact hnoncross i (Nat.lt_of_not_ge h) hret
    have hp := completeResponseCycle_crossing_product_replace l 1 S one_ne_zero
      i.val j (ZMod.val_lt i) hj hcross
    simp only [div_one, ZMod.natCast_zmod_val] at hp
    rw [ite_eq_left hret, ite_eq_left hret, hp, mul_inv]
    simp only [div_eq_mul_inv]
  · simp only [ite_eq_right hret, zero_div]

/-- A retained nonempty family of positive complete windows has a strictly
positive context inventory, on one common assignment. -/
theorem filteredInverseWindowSum_pos {B : ℕ} [NeZero B]
    (f : ZMod B → ℝ) (g : ZMod B → ℤ) (j : ℕ) (M : ℤ)
    (hf : ∀ i, 0 < f i) (hretain : ∃ i, windowSum g 1 j i = M) :
    0 < filteredInverseWindowSum f g j M := by
  classical
  unfold filteredInverseWindowSum
  apply Finset.sum_pos'
  · intro i _
    split_ifs
    · exact (inv_pos.mpr (Finset.prod_pos fun _ _ => hf _)).le
    · exact le_rfl
  · obtain ⟨i, hi⟩ := hretain
    refine ⟨i, Finset.mem_univ i, ?_⟩
    rw [ite_eq_left hi]
    exact inv_pos.mpr (Finset.prod_pos fun _ _ => hf _)

end SkewCornerDescent.CyclicWindows
