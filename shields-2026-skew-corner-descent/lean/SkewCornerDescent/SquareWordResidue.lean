/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.SquareWordProfiles

/-!
# Complete original residue determinants for the square word

Supports `shields-2026-skew-corner-descent.tex` (`rem:square-word`).
The actual full Jacobi--Trudi matrices are evaluated on h-one zero before
computing their determinants. No residue factorization is assumed. Sorry-free.
-/

namespace SkewCornerDescent.SquareWordProfiles

open SkewGluing MvPolynomial

set_option maxHeartbeats 2000000 in
-- Sparse Laplace expansion still normalizes all eight original matrix rows.
private theorem sparse_source_det {R : Type*} [CommRing R] (h : ℕ+ → R) :
    (Matrix.det !![
      h 2,h 5,h 6,h 8,h 9,h 11,h 14,h 15;
      0,h 4,h 5,h 7,h 8,h 10,h 13,h 14;
      0,0,h 2,h 4,h 5,h 7,h 10,h 11;
      0,0,1,h 2,h 3,h 5,h 8,h 9;
      0,0,0,0,h 2,h 4,h 7,h 8;
      0,0,0,0,1,h 2,h 5,h 6;
      0,0,0,0,0,0,h 4,h 5;
      0,0,0,0,0,0,0,h 2]) = h 2 ^ 2 * h 4 ^ 2 * (h 4 - h 2 ^ 2) ^ 2 := by
  repeat'
    rw [Matrix.det_succ_column_zero]
    norm_num [Fin.sum_univ_succ, Matrix.submatrix, Fin.succAbove, Matrix.det_unique]
  ring

/-- The full five-copy source residue, under any genuine homomorphism killing h-one. -/
theorem source_residue_determinant {R : Type*} [CommRing R]
    (f : Lambda →+* R) (hf : f (X (1 : ℕ+)) = 0) :
    f source.schur = f (X 2) ^ 2 * f (X 4) ^ 2 * (f (X 4) - f (X 2) ^ 2) ^ 2 := by
  have hind : (Matrix.of fun i j : Fin 8 => source.xi i - source.zeta j) = !![
      2,5,6,8,9,11,14,15;
      1,4,5,7,8,10,13,14;
      -2,1,2,4,5,7,10,11;
      -4,-1,0,2,3,5,8,9;
      -5,-2,-1,1,2,4,7,8;
      -7,-4,-3,-1,0,2,5,6;
      -8,-5,-4,-2,-1,1,4,5;
      -11,-8,-7,-5,-4,-2,1,2] := by decide
  have hm : (Matrix.of fun i j : Fin 8 => f (hh (source.xi i - source.zeta j))) = !![
      f (X 2),f (X 5),f (X 6),f (X 8),f (X 9),f (X 11),f (X 14),f (X 15);
      0,f (X 4),f (X 5),f (X 7),f (X 8),f (X 10),f (X 13),f (X 14);
      0,0,f (X 2),f (X 4),f (X 5),f (X 7),f (X 10),f (X 11);
      0,0,1,f (X 2),f (X 3),f (X 5),f (X 8),f (X 9);
      0,0,0,0,f (X 2),f (X 4),f (X 7),f (X 8);
      0,0,0,0,1,f (X 2),f (X 5),f (X 6);
      0,0,0,0,0,0,f (X 4),f (X 5);
      0,0,0,0,0,0,0,f (X 2)] := by
    ext i j
    have he := congrFun (congrFun hind i) j
    change source.xi i - source.zeta j = _ at he
    simp only [Matrix.of_apply, he]
    fin_cases i <;> fin_cases j <;> norm_num [hh, hPos, hf]
  rw [Profile.schur, RingHom.map_det]
  change (Matrix.of fun i j : Fin 8 => f (hh (source.xi i - source.zeta j))).det = _
  rw [hm]
  exact sparse_source_det (fun k => f (X k))

/-- The full two-copy end-window residue, with the same actual h-one chart. -/
theorem window_residue_determinant {R : Type*} [CommRing R]
    (f : Lambda →+* R) (hf : f (X (1 : ℕ+)) = 0) :
    f window.schur = f (X 2) ^ 2 * f (X 4) := by
  have hind : (Matrix.of fun i j : Fin 3 => window.xi i - window.zeta j) =
      !![2,5,6;1,4,5;-2,1,2] := by decide
  have hm : (Matrix.of fun i j : Fin 3 => f (hh (window.xi i - window.zeta j))) =
      !![f (X 2),f (X 5),f (X 6);0,f (X 4),f (X 5);0,0,f (X 2)] := by
    ext i j
    have he := congrFun (congrFun hind i) j
    change window.xi i - window.zeta j = _ at he
    simp only [Matrix.of_apply, he]
    fin_cases i <;> fin_cases j <;> norm_num [hh, hPos, hf]
  rw [Profile.schur, RingHom.map_det]
  change (Matrix.of fun i j : Fin 3 => f (hh (window.xi i - window.zeta j))).det = _
  rw [hm, Matrix.det_fin_three]
  simp
  ring

end SkewCornerDescent.SquareWordProfiles
