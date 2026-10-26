/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.ComponentRegularMatrices

/-!
# Nonzero inverse vectors of complete components

Supports `shields-2026-skew-corner-descent.tex`, «From response functions to literal copies»
(`sec:one-active`, `lem:early-recovery`). Every row and column of the complete
nonselected component inverse remains a nonzero vector on the actual selected
residue chart. No per-entry nonvanishing is asserted. Sorry-free.
-/

namespace SkewCornerDescent.Matrix

section Invertible

variable {ν R : Type*} [Fintype ν] [DecidableEq ν] [Semiring R] [Nontrivial R]

/-- Every row of an invertible matrix's inverse has a nonzero entry. -/
theorem invOf_row_exists_ne_zero (A : Matrix ν ν R) [Invertible A] (i : ν) :
    ∃ k, ⅟A i k ≠ 0 := by
  by_contra h
  push Not at h
  have h1 : (⅟A * A) i i = 0 := by
    rw [Matrix.mul_apply]
    exact Finset.sum_eq_zero fun k _ => by rw [h k, zero_mul]
  rw [invOf_mul_self, Matrix.one_apply_eq] at h1
  exact one_ne_zero h1

/-- Every column of an invertible matrix's inverse has a nonzero entry. -/
theorem invOf_col_exists_ne_zero (A : Matrix ν ν R) [Invertible A] (j : ν) :
    ∃ k, ⅟A k j ≠ 0 := by
  by_contra h
  push Not at h
  have h1 : (A * ⅟A) j j = 0 := by
    rw [Matrix.mul_apply]
    exact Finset.sum_eq_zero fun k _ => by rw [h k, mul_zero]
  rw [mul_invOf_self, Matrix.one_apply_eq] at h1
  exact one_ne_zero h1

end Invertible

namespace SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Every complete nonselected component inverse row is nonzero on the selected chart.
**Differs from the paper's route.** The already constructed residue inverse and its
right inverse identity give whole-vector nonvanishing directly, without individual
cofactor tests. -/
theorem residue_inverse_row_exists_ne_zero {n : ℕ} (P : Profile n)
    (hne : cellSchur D hD.1 ≠ P.schur) (i : Fin (n + 1)) :
    letI := c.profileResidueInverse P hne
    ∃ k, ⅟((jtMatrix P.xi P.zeta).map c.residueMap) i k ≠ 0 := by
  let := c.profileResidueInverse P hne
  exact invOf_row_exists_ne_zero ((jtMatrix P.xi P.zeta).map c.residueMap) i

/-- Every complete nonselected component inverse column is nonzero on the selected chart.
**Differs from the paper's route.** The already constructed residue inverse and its
left inverse identity give whole-vector nonvanishing directly, without individual
cofactor tests. -/
theorem residue_inverse_col_exists_ne_zero {n : ℕ} (P : Profile n)
    (hne : cellSchur D hD.1 ≠ P.schur) (j : Fin (n + 1)) :
    letI := c.profileResidueInverse P hne
    ∃ k, ⅟((jtMatrix P.xi P.zeta).map c.residueMap) k j ≠ 0 := by
  let := c.profileResidueInverse P hne
  exact invOf_col_exists_ne_zero ((jtMatrix P.xi P.zeta).map c.residueMap) j

end SelectedCoordinate
end SkewCornerDescent.Matrix
