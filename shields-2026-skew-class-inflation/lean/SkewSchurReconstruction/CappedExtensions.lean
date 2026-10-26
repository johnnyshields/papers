/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
-- TODO-COPIED: skew-boundary-reconstruction/lean/SkewSchurReconstruction/CappedExtensions.lean

import SkewSchurReconstruction.CappedDiagrams
import SkewSchurReconstruction.BoundaryOperations

/-!
# Capped extension identities

Formalizes the determinant and cofactor identities in
"Capped cofactors and admissible convex weights" (`sec:coordinates`,
`lem:extension-cofactors`, `eq:Pk-is-capped`, `eq:iterated-cap`).
The matrix is the actual capped Jacobi--Trudi matrix of the extended diagram.
The identities also hold for an empty parent.  Sorry-free.
-/

namespace SkewSchurReconstruction
namespace Diagram

open scoped BigOperators

variable {n : ℕ}

/-- Every old cap column shifts by `k`, including the old zeroth column. -/
theorem extendNortheast_capShift_succ (X : Diagram n) (k : ℕ) (hk : 0 < k)
    (j : Fin (n + 1)) :
    (X.extendNortheast k hk).capShift j.succ = (k : ℤ) + X.capShift j := by
  cases j using Fin.cases with
  | zero => simpa using X.extendNortheast_capShift_one k hk
  | succ i => exact X.extendNortheast_capShift_succ_succ k hk i

/-- The extension has the block matrix `(1,u; 0,M)` in `lem:extension-cofactors`. -/
theorem capMatrix_extendNortheast (X : Diagram n) (k : ℕ) (hk : 0 < k) :
    (X.extendNortheast k hk).capMatrix =
      cofactorExtensionMatrix (fun j => complete ((k : ℤ) + X.capShift j)) X.capMatrix := by
  apply Matrix.ext
  intro i j
  cases i using Fin.cases with
  | zero =>
    cases j using Fin.cases with
    | zero =>
      simp only [capMatrix, cofactorExtensionMatrix, Matrix.of_apply,
        Matrix.cons_val_zero, extendNortheast_capShift_zero, extendNortheast_rowParam_zero,
        sub_self, complete_zero]
    | succ j =>
      simp only [capMatrix, cofactorExtensionMatrix, Matrix.of_apply,
        Matrix.cons_val_zero, Matrix.cons_val_succ, extendNortheast_rowParam_zero,
        extendNortheast_capShift_succ, sub_zero]
  | succ i =>
    cases j using Fin.cases with
    | zero =>
      simp only [capMatrix, cofactorExtensionMatrix, Matrix.of_apply,
        Matrix.cons_val_succ, Matrix.cons_val_zero, extendNortheast_capShift_zero,
        extendNortheast_rowParam_succ]
      apply complete_of_neg
      have h := X.rowParam_nonneg i
      omega
    | succ j =>
      simp only [capMatrix, cofactorExtensionMatrix, Matrix.of_apply,
        Matrix.cons_val_succ, extendNortheast_capShift_succ,
        extendNortheast_rowParam_succ]
      congr 1
      ring

/-- The extended zeroth cofactor is the parent's cap polynomial `eq:Pk-is-capped`. -/
theorem cofactor_extendNortheast_zero (X : Diagram n) (k : ℕ) (hk : 0 < k) :
    (X.extendNortheast k hk).cofactor 0 = X.capPolynomial k := by
  unfold cofactor
  rw [capMatrix_extendNortheast, signedMaximalCofactor_extension_zero,
    det_vecCons_eq_sum_signedMaximalCofactor]
  unfold capPolynomial cofactor
  apply Finset.sum_congr rfl
  intro j _
  exact mul_comm _ _

/-- Every old cofactor changes sign when the new column is inserted. -/
theorem cofactor_extendNortheast_succ (X : Diagram n) (k : ℕ) (hk : 0 < k)
    (j : Fin (n + 1)) :
    (X.extendNortheast k hk).cofactor j.succ = -X.cofactor j := by
  unfold cofactor
  rw [capMatrix_extendNortheast]
  exact signedMaximalCofactor_extension_succ _ _ j

/-- The full signed cofactor-vector transform in `lem:extension-cofactors`. -/
theorem cofactor_extendNortheast (X : Diagram n) (k : ℕ) (hk : 0 < k) :
    (X.extendNortheast k hk).cofactor =
      Matrix.vecCons (X.capPolynomial k) (fun j => -X.cofactor j) := by
  funext j
  cases j using Fin.cases with
  | zero =>
    simp only [Matrix.cons_val_zero]
    exact X.cofactor_extendNortheast_zero k hk
  | succ j =>
    simp only [Matrix.cons_val_succ]
    exact X.cofactor_extendNortheast_succ k hk j

/-- A positive cap polynomial is the skew Schur function of the actual extension. -/
theorem schurFunction_extendNortheast (X : Diagram n) (k : ℕ) (hk : 0 < k) :
    (X.extendNortheast k hk).schurFunction = X.capPolynomial k :=
  X.cofactor_extendNortheast_zero k hk

/-- Capping the extended cofactor vector gives the signed two-term identity. -/
theorem capPolynomial_extendNortheast (X : Diagram n) (k : ℕ) (hk : 0 < k)
    (a : ℤ) :
    (X.extendNortheast k hk).capPolynomial a =
      complete a * X.capPolynomial k - X.capPolynomial (a + k) := by
  change (∑ j, (X.extendNortheast k hk).cofactor j *
    complete (a + (X.extendNortheast k hk).capShift j)) =
      complete a * X.capPolynomial k - X.capPolynomial (a + k)
  rw [Fin.sum_univ_succ]
  simp only [cofactor_extendNortheast_zero, cofactor_extendNortheast_succ,
    extendNortheast_capShift_zero, extendNortheast_capShift_succ, add_zero, neg_mul]
  rw [Finset.sum_neg_distrib]
  have hsum :
      (∑ j : Fin (n + 1), X.cofactor j * complete (a + ((k : ℤ) + X.capShift j))) =
        X.capPolynomial (a + k) := by
    unfold capPolynomial
    apply Finset.sum_congr rfl
    intro j _
    rw [add_assoc]
  rw [hsum]
  ring

/-- The iterated positive-extension identity `eq:iterated-cap`. -/
theorem schurFunction_iterated_extendNortheast (X : Diagram n)
    (r a : ℕ) (hr : 0 < r) (ha : 0 < a) :
    ((X.extendNortheast r hr).extendNortheast a ha).schurFunction =
      complete a * (X.extendNortheast r hr).schurFunction -
        (X.extendNortheast (r + a) (by omega)).schurFunction := by
  rw [schurFunction_extendNortheast, capPolynomial_extendNortheast,
    schurFunction_extendNortheast, schurFunction_extendNortheast]
  congr 1
  congr 1
  omega

end Diagram
end SkewSchurReconstruction
