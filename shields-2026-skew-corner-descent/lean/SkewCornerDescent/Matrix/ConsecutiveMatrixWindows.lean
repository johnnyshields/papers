/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.HessenbergIntervalSum
import Mathlib.Algebra.BigOperators.Fin

/-!
# Complete contiguous matrix windows and copied tails

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
A full copied response matrix transports every local window functional.
The exact finite start count includes empty and oversized-source boundaries.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix

/-- The full contiguous principal window, without copying or dropping any entry. -/
def contiguousMatrixWindow {N : ℕ} {α : Type*} (M : Matrix (Fin N) (Fin N) α)
    (L : ℕ) (s : Fin (N + 1 - L)) : Matrix (Fin L) (Fin L) α :=
  let e := fun i : Fin L => (⟨s.val + i.val, by have := s.isLt; have := i.isLt; omega⟩ : Fin N)
  M.submatrix e e

/-- A whole copied matrix region transports every full local principal window. -/
theorem contiguousMatrixWindow_copy {N B T : ℕ} {α : Type*}
    (hbound : T + B ≤ N) (M : Matrix (Fin N) (Fin N) α)
    (P : Matrix (Fin B) (Fin B) α)
    (hcopy : ∀ i j : Fin B,
      M ⟨T + i.val, by have := i.isLt; omega⟩ ⟨T + j.val, by have := j.isLt; omega⟩ = P i j)
    (L : ℕ) (s : Fin (B + 1 - L)) :
    contiguousMatrixWindow M L ⟨T + s.val, by have := s.isLt; omega⟩ =
      contiguousMatrixWindow P L s := by
  ext i j : 1
  have hi : s.val + i.val < B := by have := s.isLt; have := i.isLt; omega
  have hj : s.val + j.val < B := by have := s.isLt; have := j.isLt; omega
  simpa only [contiguousMatrixWindow, Matrix.submatrix_apply, Nat.add_assoc] using
    hcopy ⟨s.val + i.val, hi⟩ ⟨s.val + j.val, hj⟩

/-- Removing a complete copied tail leaves precisely the original prefix starts.
The size bound is essential at a source window one larger than its matrix. -/
theorem contiguousMatrixWindow_sum_copy_tail {N B T L : ℕ} {α β : Type*}
    [AddCommMonoid β] (hsize : L ≤ B + 1) (hdim : N = T + B)
    (M : Matrix (Fin N) (Fin N) α) (P : Matrix (Fin B) (Fin B) α)
    (hcopy : ∀ i j : Fin B,
      M ⟨T + i.val, by have := i.isLt; omega⟩ ⟨T + j.val, by have := j.isLt; omega⟩ = P i j)
    (F : Matrix (Fin L) (Fin L) α → β) :
    (∑ s : Fin (N + 1 - L), F (contiguousMatrixWindow M L s)) =
      (∑ s : Fin (B + 1 - L), F (contiguousMatrixWindow P L s)) +
      ∑ s : Fin T, F (contiguousMatrixWindow M L ⟨s.val, by have := s.isLt; omega⟩) := by
  have hstarts : N + 1 - L = T + (B + 1 - L) := by omega
  let e := finCongr hstarts
  have hreindex : (∑ s : Fin (N + 1 - L), F (contiguousMatrixWindow M L s)) =
      ∑ s : Fin (T + (B + 1 - L)), F (contiguousMatrixWindow M L (e.symm s)) := by
    apply Fintype.sum_equiv e
    intro s
    simp only [Equiv.symm_apply_apply]
  rw [hreindex, Fin.sum_univ_add]
  have hpref : (∑ s : Fin T, F (contiguousMatrixWindow M L (e.symm (s.castAdd (B + 1 - L))))) =
      ∑ s : Fin T, F (contiguousMatrixWindow M L ⟨s.val, by have := s.isLt; omega⟩) := by
    apply Finset.sum_congr rfl
    intro s _
    exact congrArg (fun t => F (contiguousMatrixWindow M L t)) (Fin.ext rfl)
  have htail : (∑ s : Fin (B + 1 - L), F (contiguousMatrixWindow M L (e.symm (s.natAdd T)))) =
      ∑ s : Fin (B + 1 - L), F (contiguousMatrixWindow P L s) := by
    apply Finset.sum_congr rfl
    intro s _
    have he : e.symm (s.natAdd T) =
        (⟨T + s.val, by have := s.isLt; omega⟩ : Fin (N + 1 - L)) := Fin.ext rfl
    rw [he, contiguousMatrixWindow_copy (by omega) M P hcopy]
  rw [hpref, htail, add_comm]

/-- The displacement-indexed starts and the native positive-window starts have
the same actual indices, including the empty oversized-window case. -/
theorem contiguousMatrixWindow_sum_starts {N : ℕ} {α β : Type*} [AddCommMonoid β]
    (M : Matrix (Fin N) (Fin N) α) (d : ℕ)
    (F : Matrix (Fin (d + 1)) (Fin (d + 1)) α → β) :
    (∑ s : Fin (N - d),
      F (contiguousMatrixWindow M (d + 1) ⟨s.val, by have := s.isLt; omega⟩)) =
      ∑ s, F (contiguousMatrixWindow M (d + 1) s) := by
  apply Fintype.sum_equiv (finCongr (show N - d = N + 1 - (d + 1) by omega))
  intro s
  exact congrArg (fun t => F (contiguousMatrixWindow M (d + 1) t)) (Fin.ext rfl)

end SkewCornerDescent.Matrix
