/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.FinitePeriodicWords
import SkewCornerDescent.Matrix.ConsecutiveMatrixWindows

/-!
# Canonical finite word periods from whole copied matrix regions

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
Two complete literal matrix copies supply the overlap periods of both diagonal
and adjacent-entry words. The canonical `finiteWordCycle` retains the actual
crossing pair at the last period position; its second endpoint is not replaced
by column zero of a cyclic submatrix.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix

/-- Whole copies at offsets zero and T supply genuine overlap periods for both
matrix words. The pair word retains every original adjacent entry, including
entries crossing the boundary of its first full period. -/
theorem copied_matrix_word_periods {N B T : ℕ} {α : Type*} (hdim : N = T + B)
    (M : Matrix (Fin N) (Fin N) α) (P : Matrix (Fin B) (Fin B) α)
    (hupper : ∀ i j : Fin B,
      M ⟨i.val, by have := i.isLt; omega⟩ ⟨j.val, by have := j.isLt; omega⟩ = P i j)
    (hlower : ∀ i j : Fin B,
      M ⟨T + i.val, by have := i.isLt; omega⟩
        ⟨T + j.val, by have := j.isLt; omega⟩ = P i j) :
    (∀ i j : Fin N, j.val = i.val + T → M i i = M j j) ∧
      (∀ i j : Fin (N - 1), j.val = i.val + T →
        M ⟨i.val, by have := i.isLt; omega⟩ ⟨i.val + 1, by have := i.isLt; omega⟩ =
          M ⟨j.val, by have := j.isLt; omega⟩ ⟨j.val + 1, by have := j.isLt; omega⟩) := by
  constructor
  · intro i j hij
    let k : Fin B := ⟨i.val, by have := j.isLt; omega⟩
    have hj : (⟨T + k.val, by have := k.isLt; omega⟩ : Fin N) = j := by
      apply Fin.ext
      change T + i.val = j.val
      omega
    calc
      M i i = P k k := hupper k k
      _ = M j j := by simpa only [hj] using (hlower k k).symm
  · intro i j hij
    let k : Fin B := ⟨i.val, by have := j.isLt; omega⟩
    let l : Fin B := ⟨i.val + 1, by have := j.isLt; omega⟩
    have hj0 : (⟨T + k.val, by have := k.isLt; omega⟩ : Fin N) =
        ⟨j.val, by have := j.isLt; omega⟩ := by
      apply Fin.ext
      change T + i.val = j.val
      omega
    have hj1 : (⟨T + l.val, by have := l.isLt; omega⟩ : Fin N) =
        ⟨j.val + 1, by have := j.isLt; omega⟩ := by
      apply Fin.ext
      change T + (i.val + 1) = j.val + 1
      omega
    exact (hupper k l).trans (by simpa only [hj0, hj1] using (hlower k l).symm)

end SkewCornerDescent.Matrix
