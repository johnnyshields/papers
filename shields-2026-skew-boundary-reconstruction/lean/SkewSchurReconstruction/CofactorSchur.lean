/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewSchurReconstruction.CappedDiagrams
import SkewSchurReconstruction.BoundaryOperations

/-!
# Jacobi--Trudi presentation and first-row deletion

Formalizes «Cofactors as skew Schur functions» and «Reconstruction from the first-row
 deletion» (`sec:geometry`, `subsec:child-separation`, `lem:top-row-cofactor`)
in `shields-2026-skew-boundary-reconstruction.tex`.  Sorry-free.
-/

namespace SkewSchurReconstruction
namespace Diagram

open scoped BigOperators

variable {n : ℕ}

/-- The ordinary Jacobi--Trudi matrix with signed integer subscripts. -/
noncomputable def jacobiTrudiMatrix (X : Diagram n) : Matrix (Fin n) (Fin n) CompleteRing :=
  Matrix.of fun i j => complete ((X.outer i : ℤ) - X.inner j - i.val + j.val)

/-- Deleting the cap column zero gives exactly the ordinary Jacobi--Trudi matrix. -/
theorem capMatrix_delete_zero (X : Diagram n) :
    X.capMatrix.submatrix id (0 : Fin (n + 1)).succAbove = X.jacobiTrudiMatrix := by
  apply Matrix.ext
  intro i j
  simp only [capMatrix, Matrix.submatrix_apply, Matrix.of_apply, id_eq,
    Fin.zero_succAbove, capShift_succ, rowParam, jacobiTrudiMatrix]
  congr 1
  ring

/-- The cofactor-defined Schur function is the actual Jacobi--Trudi determinant. -/
theorem schurFunction_eq_jacobiTrudiDet (X : Diagram n) :
    X.schurFunction = X.jacobiTrudiMatrix.det := by
  simp only [schurFunction, cofactor, signedMaximalCofactor, Fin.val_zero,
    pow_zero, one_mul, capMatrix_delete_zero]

/-- The first column below the top row is zero before any connectedness is used. -/
theorem capMatrix_first_column_succ (X : Diagram (n + 1)) (i : Fin n) :
    X.capMatrix i.succ 0 = 0 := by
  have hpos := X.rowParam_strictMono (show (0 : Fin (n + 1)) < i.succ from Fin.succ_pos i)
  have hzero : X.rowParam (0 : Fin (n + 1)) = 0 := by simp [rowParam, top]
  rw [hzero] at hpos
  simp only [capMatrix, Matrix.of_apply, capShift_zero]
  exact complete_of_neg (by omega)

/-- The first-row deletion observation is exactly the negative first positive cofactor. -/
theorem cofactor_one_eq_neg_deleteFirstRow (X : Diagram (n + 1)) :
    X.cofactor 1 = -(X.deleteFirstRow.schurFunction) := by
  let B : Matrix (Fin (n + 1)) (Fin (n + 1)) CompleteRing :=
    X.capMatrix.submatrix id (1 : Fin (n + 1 + 1)).succAbove
  have hB0 : B 0 0 = 1 := by
    simp [B, capMatrix, rowParam, capShift_zero]
  have hBs : ∀ i : Fin n, B i.succ 0 = 0 := by
    intro i
    simpa [B] using X.capMatrix_first_column_succ i
  have hminor : B.submatrix Fin.succ Fin.succ = X.deleteFirstRow.jacobiTrudiMatrix := by
    apply Matrix.ext
    intro i j
    change complete (X.capShift ((0 : Fin (n + 1)).succ.succAbove j.succ) -
      X.rowParam i.succ) =
        complete ((X.outer i.succ : ℤ) - X.inner j.succ - i.val + j.val)
    rw [Fin.succ_succAbove_succ, Fin.zero_succAbove, capShift_succ]
    simp only [rowParam, Fin.val_succ, Nat.cast_add, Nat.cast_one]
    congr 1
    ring
  have hdet : B.det = X.deleteFirstRow.jacobiTrudiMatrix.det := by
    rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ]
    simp only [Fin.val_zero, pow_zero, one_mul, hB0,
      hBs, mul_zero, zero_mul, Finset.sum_const_zero, add_zero]
    change (B.submatrix Fin.succ Fin.succ).det = X.deleteFirstRow.jacobiTrudiMatrix.det
    rw [hminor]
  rw [cofactor, signedMaximalCofactor]
  change (-1 : CompleteRing) ^ 1 * B.det = -X.deleteFirstRow.schurFunction
  rw [hdet, schurFunction_eq_jacobiTrudiDet]
  ring

end Diagram
end SkewSchurReconstruction
