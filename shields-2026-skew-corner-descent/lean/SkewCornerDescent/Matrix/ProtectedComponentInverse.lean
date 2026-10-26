/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.ProtectedComponentMinors

/-!
# Protected extreme inverse entries on the selected chart

Supports `shields-2026-skew-corner-descent.tex` (`lem:early-recovery`). Every entry
of the least-column inverse row and greatest-row inverse column is nonzero for an
actual nonselected component of span at most the selected span. The original
extreme cofactors are nonzero and strictly lower; their residues cannot disappear.
Internal inverse entries are not asserted nonzero. Sorry-free.
-/

namespace SkewCornerDescent.Matrix

open SkewGluing MvPolynomial

/-- In an invertible field matrix, a nonzero cofactor gives a nonzero inverse entry. -/
theorem invOf_entry_ne_zero_of_adjugate {ν F : Type*}
    [Fintype ν] [DecidableEq ν] [Field F] (A : Matrix ν ν F) [Invertible A]
    (i j : ν) (hcofactor : A.adjugate i j ≠ 0) : ⅟A i j ≠ 0 := by
  let := Matrix.detInvertibleOfInvertible A
  have hdetInv : ⅟A.det ≠ 0 := by
    intro hz
    have h := invOf_mul_self A.det
    rw [hz, zero_mul] at h
    exact zero_ne_one h
  rw [Matrix.invOf_eq, Matrix.smul_apply, smul_eq_mul]
  exact mul_ne_zero hdetInv hcofactor

namespace SelectedCoordinate

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The least original column and an arbitrary original row give a nonzero
cofactor residue at every maximal-span selected prime. -/
theorem last_column_minor_residue_ne_zero {n : ℕ} (P : Profile n)
    (hspan : P.topVar ≤ c.top) (j : Fin (n + 1)) :
    c.residueMap (((jtMatrix P.xi P.zeta).submatrix
      j.succAbove (Fin.last n).succAbove).det) ≠ 0 := by
  apply (c.residueMap_ne_zero_iff _).mpr
  apply c.not_dvd_lower (last_column_minor_ne_zero P j)
  exact supported_mono (fun _ hk => lt_of_lt_of_le hk hspan) (last_column_minor_mem_below P j)

/-- The greatest original row and an arbitrary original column likewise give a
nonzero cofactor residue, including empty deleted minors. -/
theorem first_row_minor_residue_ne_zero {n : ℕ} (P : Profile n)
    (hspan : P.topVar ≤ c.top) (j : Fin (n + 1)) :
    c.residueMap (((jtMatrix P.xi P.zeta).submatrix
      (0 : Fin (n + 1)).succAbove j.succAbove).det) ≠ 0 := by
  apply (c.residueMap_ne_zero_iff _).mpr
  apply c.not_dvd_lower (first_row_minor_ne_zero P j)
  exact supported_mono (fun _ hk => lt_of_lt_of_le hk hspan) (first_row_minor_mem_below P j)

/-- Every original least-column cofactor survives the selected residue, whether
or not the complete component is selected and singular on that chart. -/
theorem residue_least_column_cofactor_ne_zero {n : ℕ} (P : Profile n)
    (hspan : P.topVar ≤ c.top) (j : Fin (n + 1)) :
    ((jtMatrix P.xi P.zeta).map c.residueMap).adjugate (Fin.last n) j ≠ 0 := by
  have hmap := congrArg (fun A => A (Fin.last n) j)
    (c.residueMap.map_adjugate (jtMatrix P.xi P.zeta))
  change c.residueMap ((jtMatrix P.xi P.zeta).adjugate (Fin.last n) j) =
    ((jtMatrix P.xi P.zeta).map c.residueMap).adjugate (Fin.last n) j at hmap
  rw [← hmap, Matrix.adjugate_fin_succ_eq_det_submatrix, map_mul, map_pow, map_neg, map_one]
  exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (c.last_column_minor_residue_ne_zero P hspan j)

/-- Every original greatest-row cofactor also survives, including the selected
singular-core case and all empty deleted minors. -/
theorem residue_greatest_row_cofactor_ne_zero {n : ℕ} (P : Profile n)
    (hspan : P.topVar ≤ c.top) (i : Fin (n + 1)) :
    ((jtMatrix P.xi P.zeta).map c.residueMap).adjugate i 0 ≠ 0 := by
  have hmap := congrArg (fun A => A i 0)
    (c.residueMap.map_adjugate (jtMatrix P.xi P.zeta))
  change c.residueMap ((jtMatrix P.xi P.zeta).adjugate i 0) =
    ((jtMatrix P.xi P.zeta).map c.residueMap).adjugate i 0 at hmap
  rw [← hmap, Matrix.adjugate_fin_succ_eq_det_submatrix, map_mul, map_pow, map_neg, map_one]
  exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (c.first_row_minor_residue_ne_zero P hspan i)

/-- Every entry in the inverse row indexed by the least original column is a
protected nonzero rational function. This is stronger than whole-row nonvanishing
and does not extend to arbitrary internal inverse rows. -/
theorem residue_inverse_least_column_entry_ne_zero {n : ℕ} (P : Profile n)
    (hne : cellSchur D hD.1 ≠ P.schur) (hspan : P.topVar ≤ c.top) (j : Fin (n + 1)) :
    letI := c.profileResidueInverse P hne
    ⅟((jtMatrix P.xi P.zeta).map c.residueMap) (Fin.last n) j ≠ 0 := by
  let := c.profileResidueInverse P hne
  exact invOf_entry_ne_zero_of_adjugate _ _ _ (c.residue_least_column_cofactor_ne_zero P hspan j)

/-- Every entry in the inverse column indexed by the greatest original row is
protected and nonzero. All original rows, columns and couplings are retained. -/
theorem residue_inverse_greatest_row_entry_ne_zero {n : ℕ} (P : Profile n)
    (hne : cellSchur D hD.1 ≠ P.schur) (hspan : P.topVar ≤ c.top) (i : Fin (n + 1)) :
    letI := c.profileResidueInverse P hne
    ⅟((jtMatrix P.xi P.zeta).map c.residueMap) i 0 ≠ 0 := by
  let := c.profileResidueInverse P hne
  exact invOf_entry_ne_zero_of_adjugate _ _ _ (c.residue_greatest_row_cofactor_ne_zero P hspan i)

end SelectedCoordinate
end SkewCornerDescent.Matrix
