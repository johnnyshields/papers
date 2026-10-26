/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewJacobiNegative.FullBoardReadings
import SkewJacobiNegative.LowNegativePatterns

/-!
# A square-pattern cofactor with two ordinary degrees

The literal common-beta example of `rem:square-degree`.
-/

namespace SkewJacobiNegative.SquareDegreeExample

/-- The full five-row beta lists in the example. -/
def diagram : BetaDiagram 5 where
  row := ![13,12,9,6,5]
  col := ![9,7,4,2,0]
  row_strictAnti := by intro i j h; fin_cases i <;> fin_cases j <;> norm_num at *
  col_strictAnti := by intro i j h; fin_cases i <;> fin_cases j <;> norm_num at *
  row_nonempty := by intro i; fin_cases i <;> norm_num

private theorem positiveCorner : diagram.PositiveCorner := by
  unfold BetaDiagram.PositiveCorner
  decide

/-- The actual maximal cofactor factors into the two stated minors. -/
theorem corner_factorization : diagram.cornerPolynomial =
    (complete 3 * complete 2 - complete 5) *
      (complete 2 * complete 3 - complete 4 * complete 1) := by
  norm_num [BetaDiagram.cornerPolynomial, BetaDiagram.cornerBoard, betaBoard, diagram,
    BetaDiagram.matrix, Matrix.det_succ_row_zero, Fin.sum_univ_succ,
    Matrix.submatrix, Fin.succAbove, Fin.succAboveOrderEmb,
    Matrix.det_fin_zero, Matrix.det_fin_one, Matrix.det_fin_two]
  ring

/-- The maximum ordinary degree still reads all four nonempty cofactor rows. -/
theorem corner_totalDegree : diagram.cornerPolynomial.totalDegree = 4 := by
  rw [← diagram.cornerDiagram_schur positiveCorner]
  exact (diagram.cornerDiagram positiveCorner).schur_totalDegree

/-- The two nonzero ordinary layers are read by the exact marking homomorphism. -/
theorem marked_corner : markOrdinary diagram.cornerPolynomial =
    Polynomial.C (complete 3 * complete 2 * complete 2 * complete 3 -
      complete 3 * complete 2 * complete 4 * complete 1) * Polynomial.X^4 +
    Polynomial.C (complete 5 * complete 4 * complete 1 -
      complete 5 * complete 2 * complete 3) * Polynomial.X^3 := by
  rw [corner_factorization]
  simp only [map_mul, map_sub, markOrdinary_complete]
  norm_num
  ring

private noncomputable def layerValue : CompleteRing →+* ℚ :=
  MvPolynomial.eval₂Hom (RingHom.id ℚ) (fun j => if j.val = 1 then 0 else 1)

/-- Both displayed ordinary layers are genuinely present, not formal summands
whose coefficients might vanish in the complete-generator algebra. -/
theorem corner_layers_nonzero :
    ordinaryComponent diagram.cornerPolynomial 3 ≠ 0 ∧
      ordinaryComponent diagram.cornerPolynomial 4 ≠ 0 := by
  have h3 : ordinaryComponent diagram.cornerPolynomial 3 =
      complete 5 * complete 4 * complete 1 -
        complete 5 * complete 2 * complete 3 := by
    rw [ordinaryComponent, marked_corner]
    norm_num only [Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow,
      ite_true, ite_false, zero_add, add_zero]
  have h4 : ordinaryComponent diagram.cornerPolynomial 4 =
      complete 3 * complete 2 * complete 2 * complete 3 -
        complete 3 * complete 2 * complete 4 * complete 1 := by
    rw [ordinaryComponent, marked_corner]
    norm_num only [Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow,
      ite_true, ite_false, zero_add, add_zero]
  constructor
  · rw [h3]
    intro hz
    have h := congrArg layerValue hz
    norm_num [layerValue, complete, integerLift, Base.complete] at h
  · rw [h4]
    intro hz
    have h := congrArg layerValue hz
    norm_num [layerValue, complete, integerLift, Base.complete] at h

end SkewJacobiNegative.SquareDegreeExample
