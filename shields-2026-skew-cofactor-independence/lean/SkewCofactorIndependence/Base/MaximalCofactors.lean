/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
-- TODO-COPIED: skew-boundary-reconstruction/lean/SkewSchurReconstruction/MaximalCofactors.lean
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Signed maximal cofactors

General determinant identities for "Capped cofactors and admissible convex weights"
(`sec:coordinates`): the coordinates `eq:cofactor`, the shared-row relation
`eq:common-row-relation`, and the block transform underlying `lem:extension-cofactors`.
The block transform includes the empty lower matrix. Sorry-free.
-/

namespace SkewCofactorIndependence.Base

open scoped BigOperators

variable {R : Type*} [CommRing R] {n : ℕ}

/-- The signed minor obtained by deleting column `j`. -/
noncomputable def signedMaximalCofactor
    (M : Matrix (Fin n) (Fin n.succ) R) (j : Fin n.succ) : R :=
  (-1) ^ j.val * (M.submatrix id j.succAbove).det

/-- The square matrix obtained by adjoining the top row `u`. -/
def cofactorBorderMatrix (u : Fin n.succ → R) (M : Matrix (Fin n) (Fin n.succ) R) :
    Matrix (Fin n.succ) (Fin n.succ) R :=
  Matrix.of fun i j => Matrix.vecCons (u j) (fun k => M k j) i

omit [CommRing R] in
/-- The entrywise bordering construction is the matrix represented by `vecCons u M`. -/
theorem cofactorBorderMatrix_eq_of_vecCons
    (u : Fin n.succ → R) (M : Matrix (Fin n) (Fin n.succ) R) :
    cofactorBorderMatrix u M =
      Matrix.of (Matrix.vecCons u (fun i j => M i j)) := by
  ext i j
  cases i using Fin.cases <;>
    simp only [cofactorBorderMatrix, Matrix.of_apply,
      Matrix.cons_val_zero, Matrix.cons_val_succ]

/-- Expansion of a determinant along its bordering row. -/
theorem det_vecCons_eq_sum_signedMaximalCofactor
    (u : Fin n.succ → R) (M : Matrix (Fin n) (Fin n.succ) R) :
    (cofactorBorderMatrix u M).det = ∑ j, u j * signedMaximalCofactor M j := by
  rw [Matrix.det_succ_row_zero]
  apply Finset.sum_congr rfl
  intro j _
  have hminor : (cofactorBorderMatrix u M).submatrix Fin.succ j.succAbove =
      M.submatrix id j.succAbove := by
    ext a b
    simp only [Matrix.submatrix_apply, cofactorBorderMatrix, Matrix.of_apply,
      Matrix.cons_val_succ, id_eq]
  rw [hminor]
  simp only [cofactorBorderMatrix, Matrix.of_apply, Matrix.cons_val_zero,
    signedMaximalCofactor]
  ring

/-- The bordering expansion expressed directly using the vector constructor. -/
theorem det_of_vecCons_eq_sum_signedMaximalCofactor
    (u : Fin n.succ → R) (M : Matrix (Fin n) (Fin n.succ) R) :
    Matrix.det (Matrix.of (Matrix.vecCons u (fun i j => M i j))) =
      ∑ j, u j * signedMaximalCofactor M j := by
  rw [← cofactorBorderMatrix_eq_of_vecCons]
  exact det_vecCons_eq_sum_signedMaximalCofactor u M

/-- Every row annihilates the signed maximal-cofactor vector. -/
theorem row_sum_signedMaximalCofactor_eq_zero
    (M : Matrix (Fin n) (Fin n.succ) R) (i : Fin n) :
    ∑ j, M i j * signedMaximalCofactor M j = 0 := by
  rw [← det_vecCons_eq_sum_signedMaximalCofactor]
  apply Matrix.det_zero_of_row_eq (i := 0) (j := i.succ)
  · exact (Fin.succ_ne_zero i).symm
  · funext j
    simp only [cofactorBorderMatrix, Matrix.of_apply,
      Matrix.cons_val_zero, Matrix.cons_val_succ]

/-- Cofactor differences satisfy the relation attached to any shared row. -/
theorem shared_row_sum_cofactor_sub_eq_zero
    (M N : Matrix (Fin n) (Fin n.succ) R) (i k : Fin n)
    (hrow : M i = N k) :
    ∑ j, M i j * (signedMaximalCofactor M j - signedMaximalCofactor N j) = 0 := by
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib, row_sum_signedMaximalCofactor_eq_zero]
  have hN : ∑ j, M i j * signedMaximalCofactor N j = 0 := by
    rw [hrow]
    exact row_sum_signedMaximalCofactor_eq_zero N k
  rw [hN, sub_self]

/-- The rectangular block matrix with top row `(1,u)` and lower block `(0,M)`. -/
def cofactorExtensionMatrix
    (u : Fin n.succ → R) (M : Matrix (Fin n) (Fin n.succ) R) :
    Matrix (Fin n.succ) (Fin n.succ.succ) R :=
  Matrix.of fun i j => Matrix.vecCons (Matrix.vecCons 1 u j)
    (fun k => Matrix.vecCons 0 (fun l => M k l) j) i

/-- Deleting the new first column gives the bordered determinant. -/
theorem signedMaximalCofactor_extension_zero
    (u : Fin n.succ → R) (M : Matrix (Fin n) (Fin n.succ) R) :
    signedMaximalCofactor (cofactorExtensionMatrix u M) 0 =
      (cofactorBorderMatrix u M).det := by
  have hminor : (cofactorExtensionMatrix u M).submatrix id
      (0 : Fin n.succ.succ).succAbove = cofactorBorderMatrix u M := by
    ext i j
    cases i using Fin.cases <;>
      simp only [cofactorExtensionMatrix, cofactorBorderMatrix, Matrix.submatrix_apply,
        Matrix.of_apply, id_eq, Fin.zero_succAbove,
        Matrix.cons_val_zero, Matrix.cons_val_succ]
  simp only [signedMaximalCofactor, Fin.val_zero, pow_zero, one_mul, hminor]

/-- Deleting an old column changes the sign of its old maximal cofactor. -/
theorem signedMaximalCofactor_extension_succ
    (u : Fin n.succ → R) (M : Matrix (Fin n) (Fin n.succ) R)
    (j : Fin n.succ) :
    signedMaximalCofactor (cofactorExtensionMatrix u M) j.succ =
      -signedMaximalCofactor M j := by
  let B := (cofactorExtensionMatrix u M).submatrix id j.succ.succAbove
  have hB0 : B 0 0 = 1 := by
    simp only [B, cofactorExtensionMatrix, Matrix.submatrix_apply, Matrix.of_apply, id_eq,
      Fin.succ_succAbove_zero, Matrix.cons_val_zero]
  have hBs : ∀ i : Fin n, B i.succ 0 = 0 := by
    intro i
    simp only [B, cofactorExtensionMatrix, Matrix.submatrix_apply, Matrix.of_apply, id_eq,
      Fin.succ_succAbove_zero, Matrix.cons_val_succ, Matrix.cons_val_zero]
  have hBt : B.submatrix Fin.succ Fin.succ = M.submatrix id j.succAbove := by
    ext a b
    simp only [B, cofactorExtensionMatrix, Matrix.submatrix_apply, Matrix.of_apply, id_eq,
      Fin.succ_succAbove_succ, Matrix.cons_val_succ]
  have hdet : B.det = (M.submatrix id j.succAbove).det := by
    rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ]
    simp only [hB0, hBs, Fin.succAbove_zero, hBt, Fin.val_zero, pow_zero,
      mul_one, one_mul, mul_zero, zero_mul, Finset.sum_const_zero, add_zero]
  change (-1 : R) ^ j.succ.val * B.det =
    -((-1 : R) ^ j.val * (M.submatrix id j.succAbove).det)
  rw [hdet, Fin.val_succ, pow_succ]
  ring

/-- The whole cofactor vector transforms as `(bordered determinant, -old cofactors)`. -/
theorem signedMaximalCofactor_extension
    (u : Fin n.succ → R) (M : Matrix (Fin n) (Fin n.succ) R) :
    signedMaximalCofactor (cofactorExtensionMatrix u M) =
      Matrix.vecCons (∑ j, u j * signedMaximalCofactor M j)
        (fun j => -signedMaximalCofactor M j) := by
  funext j
  cases j using Fin.cases with
  | zero =>
      simp only [signedMaximalCofactor_extension_zero, Matrix.cons_val_zero]
      exact det_vecCons_eq_sum_signedMaximalCofactor u M
  | succ j =>
      simp only [signedMaximalCofactor_extension_succ, Matrix.cons_val_succ]

end SkewCofactorIndependence.Base
