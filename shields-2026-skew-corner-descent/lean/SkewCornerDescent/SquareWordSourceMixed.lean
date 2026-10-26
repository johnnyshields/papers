/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.SquareWordRationalMatch
import SkewCornerDescent.Matrix.DeterminantDerivation

/-!
# The full original mixed source jet of the square word

Supports `shields-2026-skew-corner-descent.tex` (`rem:square-word`).
The two derivatives are taken before the h-one specialization, retaining every
original determinant path. Sorry-free.
-/

namespace SkewCornerDescent.SquareWordProfiles

open SkewGluing MvPolynomial

set_option maxHeartbeats 4000000 in
-- The full eight-row determinant is differentiated before residue specialization.
/-- The original h-seven/h-one mixed source determinant coefficient. -/
theorem source_original_mixed_jet {R : Type*} [CommRing R]
    (f : Lambda →+* R) (hf : f (X (1 : ℕ+)) = 0) :
    f (pderiv (7 : ℕ+) (pderiv (1 : ℕ+) source.schur)) =
      f (X 2) ^ 2 * f (X 4) * (2 * f (X 2) ^ 2 - 3 * f (X 4)) := by
  have hind : (Matrix.of fun i j : Fin 8 => source.xi i - source.zeta j) = !![
      2,5,6,8,9,11,14,15;
      1,4,5,7,8,10,13,14;
      -2,1,2,4,5,7,10,11;
      -4,-1,0,2,3,5,8,9;
      -5,-2,-1,1,2,4,7,8;
      -7,-4,-3,-1,0,2,5,6;
      -8,-5,-4,-2,-1,1,4,5;
      -11,-8,-7,-5,-4,-2,1,2] := by decide
  have hm : (Matrix.of fun i j : Fin 8 => hh (source.xi i - source.zeta j)) = !![
      X 2,X 5,X 6,X 8,X 9,X 11,X 14,X 15;
      X 1,X 4,X 5,X 7,X 8,X 10,X 13,X 14;
      0,X 1,X 2,X 4,X 5,X 7,X 10,X 11;
      0,0,1,X 2,X 3,X 5,X 8,X 9;
      0,0,0,X 1,X 2,X 4,X 7,X 8;
      0,0,0,0,1,X 2,X 5,X 6;
      0,0,0,0,0,X 1,X 4,X 5;
      0,0,0,0,0,0,X 1,X 2] := by
    ext i j
    have he := congrFun (congrFun hind i) j
    change source.xi i - source.zeta j = _ at he
    simp only [Matrix.of_apply, he]
    fin_cases i <;> fin_cases j <;> norm_num [hh, hPos]
  rw [Profile.schur, hm]
  repeat'
    rw [Matrix.det_succ_column_zero]
    norm_num [Fin.sum_univ_succ, Matrix.submatrix, Fin.succAbove,
      Matrix.det_unique, Derivation.leibniz, smul_eq_mul, pderiv_X, hf]
  ring

end SkewCornerDescent.SquareWordProfiles
