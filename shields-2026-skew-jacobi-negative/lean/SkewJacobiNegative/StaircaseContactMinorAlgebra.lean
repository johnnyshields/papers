/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewJacobiNegative.StaircaseFiveFamilies

/-!
# Finite algebra of the staircase contact minors

The convolution and determinant identities underlying
`cor:staircase-contact-minors` in `shields-2026-skew-jacobi-negative.tex`.
All four charts use decreasing row-beta order.  The factorization is over
an arbitrary commutative ring and requires no invertibility hypothesis.
-/

namespace SkewJacobiNegative.StaircaseContactMinors

variable {R : Type*} [CommRing R]

/-- Truncated coefficient convolution through degree four. -/
def convolutionFive (u c : Fin 5 → R) : Fin 5 → R :=
  ![u 0 * c 0,
    u 0 * c 1 + u 1 * c 0,
    u 0 * c 2 + u 1 * c 1 + u 2 * c 0,
    u 0 * c 3 + u 1 * c 2 + u 2 * c 1 + u 3 * c 0,
    u 0 * c 4 + u 1 * c 3 + u 2 * c 2 + u 3 * c 1 + u 4 * c 0]

/-- First contact chart, with the three middle columns from the second series. -/
def a1MatrixF (u v : Fin 5 → R) : Matrix (Fin 5) (Fin 5) R :=
  !![u 1, v 2, v 3, v 4, u 4;
     u 0, v 1, v 2, v 3, u 3;
     0, v 0, v 1, v 2, u 2;
     0, 0, v 0, v 1, u 1;
     0, 0, 0, v 0, u 0]

/-- The paired first contact chart. -/
def a1MatrixH (u v : Fin 5 → R) : Matrix (Fin 5) (Fin 5) R :=
  !![v 1, v 2, u 3, v 4, u 4;
     v 0, v 1, u 2, v 3, u 3;
     0, v 0, u 1, v 2, u 2;
     0, 0, u 0, v 1, u 1;
     0, 0, 0, v 0, u 0]

/-- Second contact chart, with two columns from each series before the last column. -/
def a2MatrixF (u v : Fin 5 → R) : Matrix (Fin 5) (Fin 5) R :=
  !![u 1, u 2, v 3, v 4, u 4;
     u 0, u 1, v 2, v 3, u 3;
     0, u 0, v 1, v 2, u 2;
     0, 0, v 0, v 1, u 1;
     0, 0, 0, v 0, u 0]

/-- The paired second contact chart. -/
def a2MatrixH (u v : Fin 5 → R) : Matrix (Fin 5) (Fin 5) R :=
  !![v 1, u 2, u 3, v 4, u 4;
     v 0, u 1, u 2, v 3, u 3;
     0, u 0, u 1, v 2, u 2;
     0, 0, u 0, v 1, u 1;
     0, 0, 0, v 0, u 0]

/-- The first reduced Toeplitz minor. -/
def a1MinorF (c : Fin 5 → R) : Matrix (Fin 3) (Fin 3) R :=
  !![c 1, c 0, 0; c 2, c 1, c 0; c 4, c 3, c 2]

/-- The paired first reduced Toeplitz minor. -/
def a1MinorH (c : Fin 5 → R) : Matrix (Fin 3) (Fin 3) R :=
  !![c 2, c 0, 0; c 3, c 1, c 0; c 4, c 2, c 1]

/-- The second reduced Toeplitz minor. -/
def a2MinorF (c : Fin 5 → R) : Matrix (Fin 2) (Fin 2) R :=
  !![c 1, c 0; c 4, c 3]

/-- The paired second reduced Toeplitz minor. -/
def a2MinorH (c : Fin 5 → R) : Matrix (Fin 2) (Fin 2) R :=
  !![c 3, c 0; c 4, c 1]

private def leftMatrix (u : Fin 5 → R) : Matrix (Fin 5) (Fin 5) R :=
  !![u 4, u 3, u 2, u 1, u 0;
     u 3, u 2, u 1, u 0, 0;
     u 2, u 1, u 0, 0, 0;
     u 1, u 0, 0, 0, 0;
     u 0, 0, 0, 0, 0]

private def rightA1F (c : Fin 5 → R) : Matrix (Fin 5) (Fin 5) R :=
  !![0, 0, 0, c 0, 1;
     0, 0, c 0, c 1, 0;
     0, c 0, c 1, c 2, 0;
     1, c 1, c 2, c 3, 0;
     0, c 2, c 3, c 4, 0]

private def rightA1H (c : Fin 5 → R) : Matrix (Fin 5) (Fin 5) R :=
  !![0, 0, 0, c 0, 1;
     0, 0, 1, c 1, 0;
     0, c 0, 0, c 2, 0;
     c 0, c 1, 0, c 3, 0;
     c 1, c 2, 0, c 4, 0]

private def rightA2F (c : Fin 5 → R) : Matrix (Fin 5) (Fin 5) R :=
  !![0, 0, 0, c 0, 1;
     0, 0, c 0, c 1, 0;
     0, 1, c 1, c 2, 0;
     1, 0, c 2, c 3, 0;
     0, 0, c 3, c 4, 0]

private def rightA2H (c : Fin 5 → R) : Matrix (Fin 5) (Fin 5) R :=
  !![0, 0, 0, c 0, 1;
     0, 0, 1, c 1, 0;
     0, 1, 0, c 2, 0;
     c 0, 0, 0, c 3, 0;
     c 1, 0, 0, c 4, 0]

private theorem det_leftMatrix (u : Fin 5 → R) :
    (leftMatrix u).det = u 0 ^ 5 := by
  rw [Matrix.det_succ_column _ 4]
  norm_num [leftMatrix, Fin.sum_univ_succ, Matrix.submatrix_apply, Fin.succAbove]
  norm_num [Matrix.det_succ_row_zero, Matrix.det_unique,
    Matrix.submatrix_apply, Fin.sum_univ_succ, Fin.succAbove] <;> ring

private theorem factor_a1F (u c : Fin 5 → R) :
    a1MatrixF u (convolutionFive u c) = leftMatrix u * rightA1F c := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [a1MatrixF, convolutionFive, leftMatrix, rightA1F,
      Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

private theorem factor_a1H (u c : Fin 5 → R) :
    a1MatrixH u (convolutionFive u c) = leftMatrix u * rightA1H c := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [a1MatrixH, convolutionFive, leftMatrix, rightA1H,
      Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

private theorem factor_a2F (u c : Fin 5 → R) :
    a2MatrixF u (convolutionFive u c) = leftMatrix u * rightA2F c := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [a2MatrixF, convolutionFive, leftMatrix, rightA2F,
      Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

private theorem factor_a2H (u c : Fin 5 → R) :
    a2MatrixH u (convolutionFive u c) = leftMatrix u * rightA2H c := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [a2MatrixH, convolutionFive, leftMatrix, rightA2H,
      Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

private theorem det_rightA1F (c : Fin 5 → R) :
    (rightA1F c).det = -(a1MinorF c).det := by
  rw [Matrix.det_succ_column _ 4]
  norm_num [rightA1F, Fin.sum_univ_succ, Matrix.submatrix_apply, Fin.succAbove]
  norm_num [a1MinorF, Matrix.det_fin_three, Matrix.det_succ_row_zero,
    Matrix.det_unique, Matrix.submatrix_apply, Fin.sum_univ_succ, Fin.succAbove] <;> ring

private theorem det_rightA1H (c : Fin 5 → R) :
    (rightA1H c).det = -(a1MinorH c).det := by
  rw [Matrix.det_succ_column _ 4]
  norm_num [rightA1H, Fin.sum_univ_succ, Matrix.submatrix_apply, Fin.succAbove]
  norm_num [a1MinorH, Matrix.det_fin_three, Matrix.det_succ_row_zero,
    Matrix.det_unique, Matrix.submatrix_apply, Fin.sum_univ_succ, Fin.succAbove] <;> ring

private theorem det_rightA2F (c : Fin 5 → R) :
    (rightA2F c).det = (a2MinorF c).det := by
  rw [Matrix.det_succ_column _ 4]
  norm_num [rightA2F, Fin.sum_univ_succ, Matrix.submatrix_apply, Fin.succAbove]
  norm_num [a2MinorF, Matrix.det_fin_two, Matrix.det_succ_row_zero,
    Matrix.det_unique, Matrix.submatrix_apply, Fin.sum_univ_succ, Fin.succAbove] <;> ring

private theorem det_rightA2H (c : Fin 5 → R) :
    (rightA2H c).det = (a2MinorH c).det := by
  rw [Matrix.det_succ_column _ 4]
  norm_num [rightA2H, Fin.sum_univ_succ, Matrix.submatrix_apply, Fin.succAbove]
  norm_num [a2MinorH, Matrix.det_fin_two, Matrix.det_succ_row_zero,
    Matrix.det_unique, Matrix.submatrix_apply, Fin.sum_univ_succ, Fin.succAbove] <;> ring

/-- Convolution reduces the first F chart to its three-by-three minor. -/
theorem a1_matrixF_reduction (u c : Fin 5 → R) :
    (a1MatrixF u (convolutionFive u c)).det = -(u 0) ^ 5 * (a1MinorF c).det := by
  rw [factor_a1F, Matrix.det_mul, det_leftMatrix, det_rightA1F]
  ring

/-- Convolution reduces the first H chart to its three-by-three minor. -/
theorem a1_matrixH_reduction (u c : Fin 5 → R) :
    (a1MatrixH u (convolutionFive u c)).det = -(u 0) ^ 5 * (a1MinorH c).det := by
  rw [factor_a1H, Matrix.det_mul, det_leftMatrix, det_rightA1H]
  ring

/-- Convolution reduces the second F chart to its two-by-two minor. -/
theorem a2_matrixF_reduction (u c : Fin 5 → R) :
    (a2MatrixF u (convolutionFive u c)).det = (u 0) ^ 5 * (a2MinorF c).det := by
  rw [factor_a2F, Matrix.det_mul, det_leftMatrix, det_rightA2F]

/-- Convolution reduces the second H chart to its two-by-two minor. -/
theorem a2_matrixH_reduction (u c : Fin 5 → R) :
    (a2MatrixH u (convolutionFive u c)).det = (u 0) ^ 5 * (a2MinorH c).det := by
  rw [factor_a2H, Matrix.det_mul, det_leftMatrix, det_rightA2H]

/-- The paired three-by-three minors agree over every commutative ring. -/
theorem a1_minor_eq (c : Fin 5 → R) : (a1MinorF c).det = (a1MinorH c).det := by
  simp [a1MinorF, a1MinorH, Matrix.det_fin_three] <;> ring

/-- The paired two-by-two minors agree over every commutative ring. -/
theorem a2_minor_eq (c : Fin 5 → R) : (a2MinorF c).det = (a2MinorH c).det := by
  simp [a2MinorF, a2MinorH, Matrix.det_fin_two] <;> ring

end SkewJacobiNegative.StaircaseContactMinors
