/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.SharpExamples
import SkewClassInflation.ThinMarkBoundary

/-!
# Exact profile and core coordinates in the threshold examples

The literal rows, gaps, and complete core beta lists displayed in
`eq:first-boundary-example` and `sec:examples` of
`shields-2026-skew-class-inflation.tex`.  These are the actual constructed
profiles and cores, not separately supplied example data.  Sorry-free.
-/

namespace SkewClassInflation

open SkewJacobiNegative

/-- The first inflated source profile has exactly the displayed ordered row word. -/
theorem threshold_one_first_rows :
    (Profile.inflate 1 (thresholdOne.diagram outerOneTwo (by decide)).2).r =
      ![3, 4, 3, 6, 4] := by
  funext i
  fin_cases i <;> rfl

/-- Its displayed zero-join inflation is retained at precisely the second gap. -/
theorem threshold_one_first_gaps :
    (Profile.inflate 1 (thresholdOne.diagram outerOneTwo (by decide)).2).g =
      ![2, 1, 2, 2] := by
  funext i
  fin_cases i <;> rfl

/-- Reversing the outer order produces the other displayed full row word. -/
theorem threshold_one_second_rows :
    (Profile.inflate 1 (thresholdOne.diagram outerTwoOne (by decide)).2).r =
      ![3, 6, 4, 3, 4] := by
  funext i
  fin_cases i <;> rfl

/-- The shifted smaller joining gap is in its other literal position. -/
theorem threshold_one_second_gaps :
    (Profile.inflate 1 (thresholdOne.diagram outerTwoOne (by decide)).2).g =
      ![2, 2, 1, 2] := by
  funext i
  fin_cases i <;> rfl

/-- The first actual zero-free core retains the displayed upper beta list. -/
theorem threshold_one_first_core_rows :
    (compositionCore thresholdOne.boundary (by decide) outerOneTwo).row = ![13, 12, 9, 4] := by
  decide

/-- The other actual core retains its different displayed upper beta list. -/
theorem threshold_one_second_core_rows :
    (compositionCore thresholdOne.boundary (by decide) outerTwoOne).row = ![13, 12, 8, 5] := by
  decide

/-- Both actual cores have the same displayed full lower beta list. -/
theorem threshold_one_core_cols :
    (compositionCore thresholdOne.boundary (by decide) outerOneTwo).col = ![10, 6, 2, 0] ∧
      (compositionCore thresholdOne.boundary (by decide) outerTwoOne).col = ![10, 6, 2, 0] := by
  decide

/-- The positive-width chart before threshold two has exactly the actual two-row cells. -/
theorem threshold_two_inner_cells : thresholdTwo.innerCells 1 =
    {(0, 2), (0, 3), (0, 4), (0, 5), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4)} := by
  decide

/-- Both literal one-cell marked placements are inhabited in the positive subthreshold regime. -/
theorem threshold_two_mark_cells :
    (thresholdTwo.inflationMark 1).W = {(1, 0)} ∧
      (thresholdTwo.inflationMark 1).upper = {(0, 5)} := by
  decide

/-- The actual positive chart is legal, rather than merely well typed. -/
theorem threshold_two_mark_legal : (thresholdTwo.inflationMark 1).IsLegal :=
  thresholdTwo.inflationMark_legal 1 (by decide)

/-- At its actual threshold the specified chart fails the geometric legality predicate. -/
theorem threshold_two_mark_not_legal : ¬ (thresholdTwo.inflationMark 2).IsLegal := by
  rw [thresholdTwo.inflationMark_legal_iff]
  decide

/-- The exact signed coefficient of the first core's private generator `h₉`. -/
theorem threshold_one_first_core_private_derivative :
    MvPolynomial.pderiv (9 : ℕ+)
      (compositionCore thresholdOne.boundary (by decide) outerOneTwo).schur =
        -complete 2 * (complete 3 * complete 6 - complete 2 * complete 7) := by
  let D := compositionCore thresholdOne.boundary (by decide) outerOneTwo
  have hrows : D.row = ![13, 12, 9, 4] := threshold_one_first_core_rows
  have hcols : D.col = ![10, 6, 2, 0] := threshold_one_core_cols.1
  have he : D.matrix (2 : Fin 4) (Fin.last 3) = MvPolynomial.X (9 : ℕ+) := by
    change complete (D.row 2 - D.col (Fin.last 3)) = _
    rw [hrows, hcols]
    exact complete_nat 9
  have hp : ∀ i j, i ≠ (2 : Fin 4) ∨ j ≠ Fin.last 3 →
      (9 : ℕ+) ∉ (D.matrix i j).vars := by
    intro i j hij hv
    change (9 : ℕ+) ∈ (complete (D.row i - D.col j)).vars at hv
    have hh := (mem_vars_complete_iff _ (9 : ℕ+)).mp hv
    rw [hrows, hcols] at hh
    fin_cases i <;> fin_cases j <;> norm_num at *
  change MvPolynomial.pderiv (9 : ℕ+) D.matrix.det = _
  rw [pderiv_det_private D.matrix (9 : ℕ+) (2 : Fin 4) (Fin.last 3) he hp]
  have hm : D.matrix.submatrix (2 : Fin 4).succAbove (Fin.last 3).succAbove =
      !![complete 3, complete 7, complete 11;
         complete 2, complete 6, complete 10;
         0, 0, complete 2] := by
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [BetaDiagram.matrix, hrows, hcols, Fin.succAbove, complete]
  rw [hm, Matrix.det_fin_three]
  norm_num
  ring

/-- The other actual core contains no occurrence of `h₉` anywhere in its determinant. -/
theorem threshold_one_second_core_private_absent :
    (9 : ℕ+) ∉
      (compositionCore thresholdOne.boundary (by decide) outerTwoOne).schur.vars := by
  apply not_mem_vars_det
  intro i j hv
  change (9 : ℕ+) ∈ (complete
    ((compositionCore thresholdOne.boundary (by decide) outerTwoOne).row i -
      (compositionCore thresholdOne.boundary (by decide) outerTwoOne).col j)).vars at hv
  have hh := (mem_vars_complete_iff _ (9 : ℕ+)).mp hv
  rw [threshold_one_second_core_rows, threshold_one_core_cols.2] at hh
  fin_cases i <;> fin_cases j <;> norm_num at hh

end SkewClassInflation
