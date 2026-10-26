/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.SemiringInverse

/-!
# Option-indexed Laplace expansions for compatible borders

Supports `shields-2026-skew-corner-descent.tex` (`lem:shared-core`).
Moving the distinguished row or column into each remaining slot gives a
uniform minus sign. The same replacement order can therefore be used in both
members of a compatible cross difference. Sorry-free.
-/

namespace SkewCornerDescent.Matrix

open scoped BigOperators

/-- Laplace expansion with one distinguished row, preserving the common
remaining index type and its replacement order. -/
theorem det_option_expand_row {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]
    (A : Matrix (Option n) (Option n) R) :
    A.det = A none none * (A.submatrix some some).det -
      ∑ k : n, A none (some k) *
        (A.submatrix some (Function.update some k none)).det := by
  rw [Matrix.det_eq_detp_sub_detp]
  rw [Matrix.detp_option_expand_row_none, Matrix.detp_option_expand_row_none]
  simp only [neg_neg]
  simp_rw [Matrix.det_eq_detp_sub_detp, mul_sub]
  rw [Finset.sum_sub_distrib]
  ring

/-- The corresponding distinguished-column expansion retains every border row. -/
theorem det_option_expand_column {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]
    (A : Matrix (Option n) (Option n) R) :
    A.det = A none none * (A.submatrix some some).det -
      ∑ k : n, A (some k) none *
        (A.submatrix (Function.update some k none) some).det := by
  have h := det_option_expand_row A.transpose
  rw [Matrix.det_transpose] at h
  simpa only [Matrix.transpose_apply, ← Matrix.transpose_submatrix, Matrix.det_transpose] using h

end SkewCornerDescent.Matrix
