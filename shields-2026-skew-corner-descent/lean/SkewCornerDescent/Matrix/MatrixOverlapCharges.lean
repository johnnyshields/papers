/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OverlapIntervalIndexing

/-!
# Full matrix windows for overlapping-pair charges

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
The internal overlaps use a complete long window. Each exterior overlap uses
one additional state, retaining the actual endpoint pair and every weight.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix

/-- All overlapping adjacent-pair charges are the sum of the internal window
charge and the two full exterior window charges, with their actual start counts. -/
theorem matrix_overlap_charge_windows {N d : ℕ} (hd : 0 < d) {α R : Type*}
    [CommSemiring R] (M : Matrix (Fin N) (Fin N) α) (w τ : α → R) :
    (∑ i : Fin N, ∑ j : Fin N, ∑ k : Fin N, ∑ l : Fin N,
      if j.val - i.val = d ∧ l.val = k.val + 1 ∧
        ¬ Disjoint (Finset.Icc i j) (Finset.Icc k l) then
        (∏ v ∈ Finset.Icc i j, w (M v v)) * (τ (M k l) * w (M k k) * w (M l l))
      else 0) =
      (∑ s : Fin (N - d),
        let V := contiguousMatrixWindow M (d + 1) ⟨s.val, by have := s.isLt; omega⟩
        (∏ k, w (V k k)) *
          ∑ t : Fin d, τ (V t.castSucc t.succ) * w (V t.castSucc t.castSucc) *
            w (V t.succ t.succ)) +
      (∑ s : Fin (N - d - 1),
        let V := contiguousMatrixWindow M (d + 2) ⟨s.val, by have := s.isLt; omega⟩
        (∏ k : Fin (d + 1), w (V k.succ k.succ)) *
          (τ (V 0 1) * w (V 0 0) * w (V 1 1))) +
      (∑ s : Fin (N - d - 1),
        let V := contiguousMatrixWindow M (d + 2) ⟨s.val, by have := s.isLt; omega⟩
        (∏ k : Fin (d + 1), w (V k.castSucc k.castSucc)) *
          (τ (V (Fin.last d).castSucc (Fin.last (d + 1))) *
            w (V (Fin.last d).castSucc (Fin.last d).castSucc) *
            w (V (Fin.last (d + 1)) (Fin.last (d + 1))))) := by
  rw [overlapping_interval_pair_sum hd, interval_overlap_start_sum hd]
  congr 1
  · congr 1
    · apply Finset.sum_congr rfl
      intro s _
      dsimp only
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t _
      rw [fixed_interval_product]
      simp only [contiguousMatrixWindow, Matrix.submatrix_apply,
        Fin.val_castSucc, Fin.val_succ, Nat.add_assoc]
    · apply Finset.sum_congr rfl
      intro s _
      dsimp only
      rw [fixed_interval_product (fun k : Fin N => w (M k k))
        (⟨s.val + 1, by have := s.isLt; omega⟩ : Fin (N - d))]
      simp only [contiguousMatrixWindow, Matrix.submatrix_apply,
        Fin.val_succ, Fin.val_zero, Fin.val_one, Nat.add_zero,
        Nat.add_left_comm, Nat.add_comm]
  · apply Finset.sum_congr rfl
    intro s _
    dsimp only
    rw [fixed_interval_product (fun k : Fin N => w (M k k))
      (⟨s.val, by have := s.isLt; omega⟩ : Fin (N - d))]
    simp only [contiguousMatrixWindow, Matrix.submatrix_apply,
      Fin.val_castSucc, Fin.val_last, Nat.add_assoc]

end SkewCornerDescent.Matrix
