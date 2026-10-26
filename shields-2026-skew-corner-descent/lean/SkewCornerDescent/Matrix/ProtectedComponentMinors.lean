/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.ComponentRegularMatrices

/-!
# Extreme component cofactors and their strictly lower supports

Supports `shields-2026-skew-corner-descent.tex` (`lem:early-recovery`). Deleting
any row and the least original column, or the greatest original row and any
column, gives aligned nonnegative beta lists. Every such determinant is nonzero
and uses generators strictly below the complete component's span. Empty minors
are included. No assertion is made about arbitrary internal inverse entries.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix

open SkewGluing MvPolynomial

/-- A single indexed complete homogeneous generator below a bound has that
strict support, including negative indices and the unit at index zero. -/
theorem hh_mem_strictly_below (N : ℕ+) (z : ℤ) (hz : z < (N : ℤ)) :
    hh z ∈ supported ℚ {j : ℕ+ | j < N} := by
  by_cases hnegative : z < 0
  · rw [hh_of_neg hnegative]
    exact Subalgebra.zero_mem _
  · simp only [hh, hnegative, ite_false, hPos]
    split_ifs with hpositive
    · apply (X_mem_supported (R := ℚ)).mpr
      change (⟨z.toNat, hpositive⟩ : ℕ+) < N
      change z.toNat < (N : ℕ)
      omega
    · exact Subalgebra.one_mem _

/-- A deleted row never shifts a retained row below its immediate successor. -/
private theorem deleted_row_le_succ {n : ℕ} (j : Fin (n + 1)) (i : Fin n) :
    j.succAbove i ≤ i.succ := by
  unfold Fin.succAbove
  split_ifs
  · change i.val ≤ i.val + 1
    omega
  · exact le_rfl

/-- A deleted column never shifts a retained column above its unchanged position. -/
private theorem castSucc_le_deleted_col {n : ℕ} (j : Fin (n + 1)) (i : Fin n) :
    i.castSucc ≤ j.succAbove i := by
  unfold Fin.succAbove
  split_ifs
  · exact le_rfl
  · change i.val ≤ i.val + 1
    omega

/-- Every least-column cofactor of a connected profile is a nonzero actual
beta determinant, even when its minor has empty rows. -/
theorem last_column_minor_ne_zero {n : ℕ} (P : Profile n) (j : Fin (n + 1)) :
    ((jtMatrix P.xi P.zeta).submatrix j.succAbove (Fin.last n).succAbove).det ≠ 0 := by
  rw [Fin.succAbove_last]
  change (jtMatrix (fun i => P.xi (j.succAbove i)) (fun i => P.zeta i.castSucc)).det ≠ 0
  apply det_jtMatrix_ne_zero
    (P.xi_strictAnti.comp_strictMono (Fin.strictMono_succAbove j))
    (P.zeta_strictAnti.comp_strictMono Fin.strictMono_castSucc)
  intro i
  exact (P.zeta_le_xi_succ i).trans
    (P.xi_strictAnti.antitone (deleted_row_le_succ j i))

/-- Every greatest-row cofactor is a nonzero aligned beta determinant. -/
theorem first_row_minor_ne_zero {n : ℕ} (P : Profile n) (j : Fin (n + 1)) :
    ((jtMatrix P.xi P.zeta).submatrix (0 : Fin (n + 1)).succAbove j.succAbove).det ≠ 0 := by
  rw [Fin.succAbove_zero]
  change (jtMatrix (fun i => P.xi i.succ) (fun i => P.zeta (j.succAbove i))).det ≠ 0
  apply det_jtMatrix_ne_zero
    (P.xi_strictAnti.comp_strictMono Fin.strictMono_succ)
    (P.zeta_strictAnti.comp_strictMono (Fin.strictMono_succAbove j))
  intro i
  exact (P.zeta_strictAnti.antitone (castSucc_le_deleted_col j i)).trans
    (P.zeta_le_xi_succ i)

/-- Least-column cofactors omit the component's largest generator strictly. -/
theorem last_column_minor_mem_below {n : ℕ} (P : Profile n) (j : Fin (n + 1)) :
    ((jtMatrix P.xi P.zeta).submatrix j.succAbove (Fin.last n).succAbove).det ∈
      supported ℚ {k : ℕ+ | k < P.topVar} := by
  rw [Fin.succAbove_last]
  apply det_mem_subalgebra
  intro i k
  apply hh_mem_strictly_below
  have hxi := P.xi_strictAnti.antitone (Fin.zero_le (j.succAbove i))
  have hzeta := P.zeta_strictAnti (Fin.castSucc_lt_last k)
  have htop := P.topVar_coe
  have hzero := P.zeta_last
  omega

/-- Greatest-row cofactors also lie strictly below the component's largest generator. -/
theorem first_row_minor_mem_below {n : ℕ} (P : Profile n) (j : Fin (n + 1)) :
    ((jtMatrix P.xi P.zeta).submatrix (0 : Fin (n + 1)).succAbove j.succAbove).det ∈
      supported ℚ {k : ℕ+ | k < P.topVar} := by
  rw [Fin.succAbove_zero]
  apply det_mem_subalgebra
  intro i k
  apply hh_mem_strictly_below
  have hxi := P.xi_strictAnti (Fin.succ_pos i)
  have hzeta := P.zeta_nonneg (j.succAbove k)
  have htop := P.topVar_coe
  omega

end SkewCornerDescent.Matrix
