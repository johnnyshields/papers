/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewSchurReconstruction.CofactorSchur

/-!
# Factorwise reversal is not global reversal

The explicit ribbons of `rem:factorwise` have row compositions
(1,2,1,3,2) and (1,3,2,1,2).  Their actual Jacobi--Trudi determinants agree.
The second composition is neither the first nor its global reversal.
-/

namespace SkewSchurReconstruction

open scoped Matrix BigOperators

/-- The ribbon with row lengths (1,2,1,3,2). -/
def factorwiseLeft : Diagram 5 where
  outer := ![5, 5, 4, 4, 2]
  inner := ![4, 3, 3, 1, 0]
  outer_antitone := by decide
  inner_antitone := by decide
  row_nonempty := by decide

/-- The ribbon obtained by reversing only the first composition factor. -/
def factorwiseRight : Diagram 5 where
  outer := ![5, 5, 3, 2, 2]
  inner := ![4, 2, 1, 1, 0]
  outer_antitone := by decide
  inner_antitone := by decide
  row_nonempty := by decide

theorem factorwiseLeft_connected : factorwiseLeft.Connected := by
  unfold Diagram.Connected
  decide

theorem factorwiseRight_connected : factorwiseRight.Connected := by
  unfold Diagram.Connected
  decide

theorem factorwiseLeft_rowLengths : factorwiseLeft.rowLengthList = [1, 2, 1, 3, 2] := by
  decide

theorem factorwiseRight_rowLengths : factorwiseRight.rowLengthList = [1, 3, 2, 1, 2] := by
  decide

/-- The two ribbon compositions differ and are not related by whole-word reversal. -/
theorem factorwise_not_global_reversal :
    factorwiseRight.rowLengthList ≠ factorwiseLeft.rowLengthList ∧
      factorwiseRight.rowLengthList ≠ factorwiseLeft.rowLengthList.reverse := by
  rw [factorwiseLeft_rowLengths, factorwiseRight_rowLengths]
  decide

set_option maxHeartbeats 1000000 in
-- The finite expansion normalizes two five-row Jacobi--Trudi determinants before `ring`.
/-- The Schur equality in `rem:factorwise`, on the actual ribbon diagrams. -/
theorem factorwise_schur_eq : factorwiseLeft.schurFunction = factorwiseRight.schurFunction := by
  rw [Diagram.schurFunction_eq_jacobiTrudiDet, Diagram.schurFunction_eq_jacobiTrudiDet]
  norm_num [Matrix.det_succ_row_zero, Fin.sum_univ_succ,
    Diagram.jacobiTrudiMatrix, Matrix.submatrix, Matrix.of_apply, Fin.succAbove,
    factorwiseLeft, factorwiseRight]
  ring

end SkewSchurReconstruction
