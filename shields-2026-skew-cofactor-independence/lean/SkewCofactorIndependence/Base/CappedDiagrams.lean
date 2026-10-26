/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
-- TODO-COPIED: skew-boundary-reconstruction/lean/SkewSchurReconstruction/CappedDiagrams.lean
import SkewCofactorIndependence.Base.CompleteRing
import SkewCofactorIndependence.Base.Diagrams
import SkewCofactorIndependence.Base.MaximalCofactors

/-!
# Capped Jacobi--Trudi diagrams

Formalizes «Capped cofactors and admissible convex weights» (`sec:coordinates`)
in `shields-2026-skew-boundary-reconstruction.tex`.  The exact row relations are
obtained from actual signed determinants, not assumed of a formal vector.  Sorry-free.
-/

namespace SkewCofactorIndependence.Base

open scoped BigOperators

namespace Diagram

variable {n : ℕ}

/-- The actual capped matrix in `eq:capmatrix`. -/
noncomputable def capMatrix (X : Diagram n) : Matrix (Fin n) (Fin (n + 1)) CompleteRing :=
  Matrix.of fun i j => complete (X.capShift j - X.rowParam i)

/-- The signed maximal cofactor `eq:cofactor` of a skew diagram. -/
noncomputable def cofactor (X : Diagram n) (j : Fin (n + 1)) : CompleteRing :=
  signedMaximalCofactor X.capMatrix j

/-- The skew Schur function in the manuscript's free-generator Jacobi--Trudi presentation. -/
noncomputable def schurFunction (X : Diagram n) : CompleteRing := X.cofactor 0

/-- A cap polynomial on its actual grid, allowing negative shifts for the row-kernel relations. -/
noncomputable def capPolynomial (X : Diagram n) (k : ℤ) : CompleteRing :=
  ∑ j, X.cofactor j * complete (k + X.capShift j)

/-- Entrywise kernel relation for every row of a diagram. -/
theorem row_cofactor_relation (X : Diagram n) (i : Fin n) :
    ∑ j, complete (X.capShift j - X.rowParam i) * X.cofactor j = 0 := by
  exact row_sum_signedMaximalCofactor_eq_zero X.capMatrix i

/-- Capping at the negative of an actual row parameter gives zero. -/
theorem capPolynomial_neg_rowParam (X : Diagram n) (i : Fin n) :
    X.capPolynomial (-X.rowParam i) = 0 := by
  unfold capPolynomial
  have he : ∀ j, X.cofactor j * complete (-X.rowParam i + X.capShift j) =
      complete (X.capShift j - X.rowParam i) * X.cofactor j := by
    intro j
    rw [show -X.rowParam i + X.capShift j = X.capShift j - X.rowParam i by ring]
    exact mul_comm _ _
  simp_rw [he]
  exact X.row_cofactor_relation i

/-- The zeroth cap vanishes for every nonempty parent, independently of skew equality. -/
theorem capPolynomial_zero (X : Diagram n) (hn : 0 < n) : X.capPolynomial 0 = 0 := by
  have h := X.capPolynomial_neg_rowParam ⟨0, hn⟩
  simpa using h

/-- On a common cap grid, common row parameters give the exact defect relation. -/
theorem common_row_defect_relation (X Y : Diagram n)
    (hgrid : X.capShift = Y.capShift) (i : Fin n)
    (hrow : X.rowParam i = Y.rowParam i) :
    ∑ j, complete (X.capShift j - X.rowParam i) * (X.cofactor j - Y.cofactor j) = 0 := by
  apply shared_row_sum_cofactor_sub_eq_zero X.capMatrix Y.capMatrix i i
  funext j
  simp [capMatrix, hgrid, hrow]

/-- The empty determinant agrees with the manuscript's empty-function convention. -/
@[simp]
theorem schurFunction_empty (X : Diagram 0) : X.schurFunction = 1 := by
  simp [schurFunction, cofactor, signedMaximalCofactor]

end Diagram

end SkewCofactorIndependence.Base
