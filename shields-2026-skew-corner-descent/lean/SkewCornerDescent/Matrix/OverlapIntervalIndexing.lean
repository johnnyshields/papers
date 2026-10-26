/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.FixedOffsetIntervalIndexing
import SkewCornerDescent.Matrix.OverlapStartIndexing

/-!
# Actual finite overlapping endpoint pairs

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
The four original endpoints are reindexed by their true bounded interval starts.
Truncated subtraction cannot add backward intervals, and both exterior
adjacent pairs remain in the overlap condition.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix

/-- Two nonempty ordered finite intervals meet exactly when their endpoints cross. -/
theorem finite_intervals_overlap_iff {N : ℕ} (i j k l : Fin N)
    (hij : i ≤ j) (hkl : k ≤ l) :
    ¬ Disjoint (Finset.Icc i j) (Finset.Icc k l) ↔ i ≤ l ∧ k ≤ j := by
  rw [Finset.not_disjoint_iff]
  constructor
  · rintro ⟨x, hx, hy⟩
    rcases Finset.mem_Icc.mp hx with ⟨hix, hxj⟩
    rcases Finset.mem_Icc.mp hy with ⟨hkx, hxl⟩
    exact ⟨hix.trans hxl, hkx.trans hxj⟩
  · rintro ⟨hil, hkj⟩
    exact ⟨max i k, Finset.mem_Icc.mpr ⟨le_max_left _ _, max_le hij hkj⟩,
      Finset.mem_Icc.mpr ⟨le_max_right _ _, max_le hil hkl⟩⟩

/-- All four original overlap endpoints reduce to their two genuine start indices.
The long interval has positive displacement, so backward pairs cannot appear. -/
theorem overlapping_interval_pair_sum {N d : ℕ} (hd : 0 < d)
    {R : Type*} [AddCommMonoid R] (F : Fin N → Fin N → Fin N → Fin N → R) :
    (∑ i : Fin N, ∑ j : Fin N, ∑ k : Fin N, ∑ l : Fin N,
      if j.val - i.val = d ∧ l.val = k.val + 1 ∧
        ¬ Disjoint (Finset.Icc i j) (Finset.Icc k l) then F i j k l else 0) =
      ∑ s : Fin (N - d), ∑ k : Fin (N - 1),
        if s.val ≤ k.val + 1 ∧ k.val ≤ s.val + d then
          F ⟨s.val, by have := s.isLt; omega⟩
            ⟨s.val + d, by have := s.isLt; omega⟩
            ⟨k.val, by have := k.isLt; omega⟩
            ⟨k.val + 1, by have := k.isLt; omega⟩ else 0 := by
  classical
  have hp (i j : Fin N) :
      (∑ k : Fin N, ∑ l : Fin N,
        if j.val - i.val = d ∧ l.val = k.val + 1 ∧
          ¬ Disjoint (Finset.Icc i j) (Finset.Icc k l) then F i j k l else 0) =
      if j.val - i.val = d then
        ∑ k : Fin (N - 1),
          if ¬ Disjoint (Finset.Icc i j)
            (Finset.Icc (⟨k.val, by have := k.isLt; omega⟩ : Fin N)
              ⟨k.val + 1, by have := k.isLt; omega⟩) then
            F i j ⟨k.val, by have := k.isLt; omega⟩
              ⟨k.val + 1, by have := k.isLt; omega⟩ else 0 else 0 := by
    by_cases h : j.val - i.val = d
    · simp only [h, true_and, ite_true, ite_and]
      exact fixed_offset_pair_sum 1 (fun k l =>
        if ¬ Disjoint (Finset.Icc i j) (Finset.Icc k l) then F i j k l else 0)
    · simp only [h, false_and, ite_false, Finset.sum_const_zero]
  simp_rw [hp]
  rw [positive_difference_pair_sum hd]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro k _
  have hi : (⟨s.val, by have := s.isLt; omega⟩ : Fin N) ≤
      ⟨s.val + d, by have := s.isLt; omega⟩ := by change s.val ≤ s.val + d; omega
  have hk : (⟨k.val, by have := k.isLt; omega⟩ : Fin N) ≤
      ⟨k.val + 1, by have := k.isLt; omega⟩ := by change k.val ≤ k.val + 1; omega
  simp only [finite_intervals_overlap_iff _ _ _ _ hi hk, Fin.le_def]

end SkewCornerDescent.Matrix
