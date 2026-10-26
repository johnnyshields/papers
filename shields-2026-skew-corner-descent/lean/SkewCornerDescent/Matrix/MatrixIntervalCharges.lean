/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.FixedOffsetIntervalIndexing

/-!
# Whole-matrix window formulas for interval charges

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
Finite interval products and onsite sums are complete principal-window
functionals. In particular their off-diagonal endpoint entries are not replaced
by products of diagonal response words.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix

/-- An endpoint-entry charge with its complete diagonal interval product is
exactly a sum of full contiguous matrix-window charges. -/
theorem matrix_interval_charge_windows {N : ℕ} (d : ℕ) {α R : Type*}
    [CommSemiring R] (M : Matrix (Fin N) (Fin N) α) (f g : α → R) :
    (∑ i : Fin N, ∑ j : Fin N, if i.val ≤ j.val ∧ j.val - i.val = d then
      f (M i j) * ∏ k ∈ Finset.Icc i j, g (M k k) else 0) =
      ∑ s : Fin (N - d),
        f (contiguousMatrixWindow M (d + 1) ⟨s.val, by have := s.isLt; omega⟩
          0 (Fin.last d)) *
        ∏ k : Fin (d + 1),
          g (contiguousMatrixWindow M (d + 1) ⟨s.val, by have := s.isLt; omega⟩ k k) := by
  rw [ordered_difference_pair_sum]
  apply Finset.sum_congr rfl
  intro s _
  rw [fixed_interval_product]
  simp only [contiguousMatrixWindow, Matrix.submatrix_apply, Fin.val_zero,
    Fin.val_last, Nat.add_zero]

/-- Onsite interval charges retain all diagonal weights and all first jets of
the full window, including the shortest admissible interval. -/
theorem matrix_vertex_charge_windows {N : ℕ} (d : ℕ) {α R : Type*}
    [CommSemiring R] (M : Matrix (Fin N) (Fin N) α) (w ν : α → R) :
    (∑ i : Fin N, ∑ j : Fin N, if i.val ≤ j.val ∧ j.val - i.val = d then
      (∏ k ∈ Finset.Icc i j, w (M k k)) * (∑ k ∈ Finset.Icc i j, ν (M k k)) else 0) =
      ∑ s : Fin (N - d),
        (∏ k : Fin (d + 1),
          w (contiguousMatrixWindow M (d + 1) ⟨s.val, by have := s.isLt; omega⟩ k k)) *
        (∑ k : Fin (d + 1),
          ν (contiguousMatrixWindow M (d + 1) ⟨s.val, by have := s.isLt; omega⟩ k k)) := by
  rw [ordered_difference_pair_sum]
  apply Finset.sum_congr rfl
  intro s _
  rw [fixed_interval_product, fixed_interval_sum]
  rfl

end SkewCornerDescent.Matrix
