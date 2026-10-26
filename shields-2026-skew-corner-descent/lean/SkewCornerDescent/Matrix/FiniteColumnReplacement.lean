/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.DeterminantMixedDerivation

/-!
# Exact cofactors for two original column replacements

Supports `shields-2026-skew-corner-descent.tex` (`rem:square-word`).
Sparse original derivative columns reduce to complete two-row/two-column minors.
No determinant path or off-diagonal entry is discarded. Sorry-free.
-/

namespace SkewCornerDescent.Matrix

open scoped BigOperators

/-- One literal basis column exposes its full signed cofactor. -/
theorem det_updateCol_single {R : Type*} [CommRing R] {n : ℕ}
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (r j : Fin (n + 1)) :
    (M.updateCol j (Pi.single r 1)).det =
      (-1 : R) ^ ((r : ℕ) + (j : ℕ)) * (M.submatrix r.succAbove j.succAbove).det := by
  have hminor : (M.updateCol j (Pi.single r 1)).submatrix r.succAbove j.succAbove =
      M.submatrix r.succAbove j.succAbove := by
    ext a b
    simp [Matrix.submatrix_apply]
  rw [Matrix.det_succ_column _ j, Finset.sum_eq_single r]
  · simp [hminor]
  · intro a _ har
    simp [har]
  · intro h
    exact False.elim (h (Finset.mem_univ r))

/-- Removing another original column preserves the whole replacement column. -/
theorem submatrix_updateCol_succAbove {R : Type*} {n : ℕ}
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    (r i : Fin (n + 1)) (j : Fin n) (v : Fin (n + 1) → R) :
    (M.updateCol (i.succAbove j) v).submatrix r.succAbove i.succAbove =
      (M.submatrix r.succAbove i.succAbove).updateCol j (v ∘ r.succAbove) := by
  ext a b
  simp [Matrix.submatrix_apply, Matrix.updateCol_apply]

/-- A retained basis row remains its literal basis row after deletion. -/
theorem single_comp_succAbove {R : Type*} [Zero R] {n : ℕ}
    (r : Fin (n + 1)) (s : Fin n) (a : R) :
    Pi.single (r.succAbove s) a ∘ r.succAbove = Pi.single s a := by
  funext b
  simp [Pi.single_apply]

/-- Two distinct basis columns expose the complete original double cofactor.
The retained row and column are supplied in their deletion coordinates. -/
theorem det_two_basis_columns {R : Type*} [CommRing R] {n : ℕ}
    (M : Matrix (Fin (n + 2)) (Fin (n + 2)) R)
    (r i : Fin (n + 2)) (s j : Fin (n + 1)) :
    ((M.updateCol (i.succAbove j) (Pi.single (r.succAbove s) 1)).updateCol i
      (Pi.single r 1)).det =
      (-1 : R) ^ ((r : ℕ) + (i : ℕ)) *
        ((-1 : R) ^ ((s : ℕ) + (j : ℕ)) *
          ((M.submatrix r.succAbove i.succAbove).submatrix s.succAbove j.succAbove).det) := by
  rw [det_updateCol_single, submatrix_updateCol_succAbove, single_comp_succAbove,
    det_updateCol_single]

/-- Two distinct replacement columns supported on one row have zero determinant. -/
theorem det_same_basis_row {ν R : Type*} [Fintype ν] [DecidableEq ν] [CommRing R]
    (M : Matrix ν ν R) (r i j : ν) (hij : i ≠ j) :
    ((M.updateCol j (Pi.single r 1)).updateCol i (Pi.single r 1)).det = 0 := by
  apply Matrix.det_zero_of_column_eq hij
  intro a
  simp [Ne.symm hij]

end SkewCornerDescent.Matrix
