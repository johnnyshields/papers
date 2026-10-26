/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.SquareWordResidue

/-!
# Full original square-word amalgamation and closure residues

Supports `shields-2026-skew-corner-descent.tex` (`rem:square-word`).
The literal shared-window union and full horizontal closure supply these
Jacobi--Trudi determinants. No residue factorization is assumed. Sorry-free.
-/

namespace SkewCornerDescent.SquareWordProfiles

open SkewGluing MvPolynomial

set_option maxHeartbeats 4000000 in
-- Sparse Laplace expansion normalizes the thirteen-row complete matrix.
private theorem sparse_amalgamation_det {R : Type*} [CommRing R] (h : ℕ+ → R) :
    (Matrix.det !![
      h 2,h 5,h 6,h 8,h 9,h 11,h 14,h 15,h 17,h 18,h 20,h 23,h 24;
      0,h 4,h 5,h 7,h 8,h 10,h 13,h 14,h 16,h 17,h 19,h 22,h 23;
      0,0,h 2,h 4,h 5,h 7,h 10,h 11,h 13,h 14,h 16,h 19,h 20;
      0,0,1,h 2,h 3,h 5,h 8,h 9,h 11,h 12,h 14,h 17,h 18;
      0,0,0,0,h 2,h 4,h 7,h 8,h 10,h 11,h 13,h 16,h 17;
      0,0,0,0,1,h 2,h 5,h 6,h 8,h 9,h 11,h 14,h 15;
      0,0,0,0,0,0,h 4,h 5,h 7,h 8,h 10,h 13,h 14;
      0,0,0,0,0,0,0,h 2,h 4,h 5,h 7,h 10,h 11;
      0,0,0,0,0,0,0,1,h 2,h 3,h 5,h 8,h 9;
      0,0,0,0,0,0,0,0,0,h 2,h 4,h 7,h 8;
      0,0,0,0,0,0,0,0,0,1,h 2,h 5,h 6;
      0,0,0,0,0,0,0,0,0,0,0,h 4,h 5;
      0,0,0,0,0,0,0,0,0,0,0,0,h 2]) = h 2 ^ 2 * h 4 ^ 3 * (h 4 - h 2 ^ 2) ^ 4 := by
  repeat'
    rw [Matrix.det_succ_column_zero]
    norm_num [Fin.sum_univ_succ, Matrix.submatrix, Fin.succAbove, Matrix.det_unique]
  ring

set_option maxHeartbeats 1000000 in
-- The entry bridge checks the complete thirteen-by-thirteen integer index matrix.
/-- The complete original amalgamation residue, under any homomorphism killing h-one. -/
theorem amalgamation_residue_determinant {R : Type*} [CommRing R]
    (f : Lambda →+* R) (hf : f (X (1 : ℕ+)) = 0) :
    f amalgamation.schur = f (X 2) ^ 2 * f (X 4) ^ 3 * (f (X 4) - f (X 2) ^ 2) ^ 4 := by
  have hind : (Matrix.of fun i j : Fin 13 => amalgamation.xi i - amalgamation.zeta j) = !![
      2,5,6,8,9,11,14,15,17,18,20,23,24;
      1,4,5,7,8,10,13,14,16,17,19,22,23;
      -2,1,2,4,5,7,10,11,13,14,16,19,20;
      -4,-1,0,2,3,5,8,9,11,12,14,17,18;
      -5,-2,-1,1,2,4,7,8,10,11,13,16,17;
      -7,-4,-3,-1,0,2,5,6,8,9,11,14,15;
      -8,-5,-4,-2,-1,1,4,5,7,8,10,13,14;
      -11,-8,-7,-5,-4,-2,1,2,4,5,7,10,11;
      -13,-10,-9,-7,-6,-4,-1,0,2,3,5,8,9;
      -14,-11,-10,-8,-7,-5,-2,-1,1,2,4,7,8;
      -16,-13,-12,-10,-9,-7,-4,-3,-1,0,2,5,6;
      -17,-14,-13,-11,-10,-8,-5,-4,-2,-1,1,4,5;
      -20,-17,-16,-14,-13,-11,-8,-7,-5,-4,-2,1,2] := by decide
  have hm : (Matrix.of fun i j : Fin 13 => f (hh (amalgamation.xi i - amalgamation.zeta j))) = !![
      f (X 2),f (X 5),f (X 6),f (X 8),f (X 9),f (X 11),f (X 14),
        f (X 15),f (X 17),f (X 18),f (X 20),f (X 23),f (X 24);
      0,f (X 4),f (X 5),f (X 7),f (X 8),f (X 10),f (X 13),
        f (X 14),f (X 16),f (X 17),f (X 19),f (X 22),f (X 23);
      0,0,f (X 2),f (X 4),f (X 5),f (X 7),f (X 10),
        f (X 11),f (X 13),f (X 14),f (X 16),f (X 19),f (X 20);
      0,0,1,f (X 2),f (X 3),f (X 5),f (X 8),f (X 9),f (X 11),f (X 12),f (X 14),f (X 17),f (X 18);
      0,0,0,0,f (X 2),f (X 4),f (X 7),f (X 8),f (X 10),f (X 11),f (X 13),f (X 16),f (X 17);
      0,0,0,0,1,f (X 2),f (X 5),f (X 6),f (X 8),f (X 9),f (X 11),f (X 14),f (X 15);
      0,0,0,0,0,0,f (X 4),f (X 5),f (X 7),f (X 8),f (X 10),f (X 13),f (X 14);
      0,0,0,0,0,0,0,f (X 2),f (X 4),f (X 5),f (X 7),f (X 10),f (X 11);
      0,0,0,0,0,0,0,1,f (X 2),f (X 3),f (X 5),f (X 8),f (X 9);
      0,0,0,0,0,0,0,0,0,f (X 2),f (X 4),f (X 7),f (X 8);
      0,0,0,0,0,0,0,0,0,1,f (X 2),f (X 5),f (X 6);
      0,0,0,0,0,0,0,0,0,0,0,f (X 4),f (X 5);
      0,0,0,0,0,0,0,0,0,0,0,0,f (X 2)] := by
    ext i j
    have he := congrFun (congrFun hind i) j
    change amalgamation.xi i - amalgamation.zeta j = _ at he
    simp only [Matrix.of_apply, he]
    fin_cases i <;> fin_cases j <;> norm_num [hh, hPos, hf]
  rw [Profile.schur, RingHom.map_det]
  change (Matrix.of fun i j : Fin 13 => f (hh (amalgamation.xi i - amalgamation.zeta j))).det = _
  rw [hm]
  exact sparse_amalgamation_det (fun k => f (X k))

set_option maxHeartbeats 4000000 in
-- Sparse Laplace expansion normalizes the fifteen-row complete matrix.
private theorem sparse_closure_det {R : Type*} [CommRing R] (h : ℕ+ → R) :
    (Matrix.det !![
      h 2,h 5,h 6,h 8,h 9,h 11,h 14,h 17,h 20,h 21,h 23,h 24,h 26,h 29,h 30;
      0,h 4,h 5,h 7,h 8,h 10,h 13,h 16,h 19,h 20,h 22,h 23,h 25,h 28,h 29;
      0,0,h 2,h 4,h 5,h 7,h 10,h 13,h 16,h 17,h 19,h 20,h 22,h 25,h 26;
      0,0,1,h 2,h 3,h 5,h 8,h 11,h 14,h 15,h 17,h 18,h 20,h 23,h 24;
      0,0,0,0,h 2,h 4,h 7,h 10,h 13,h 14,h 16,h 17,h 19,h 22,h 23;
      0,0,0,0,1,h 2,h 5,h 8,h 11,h 12,h 14,h 15,h 17,h 20,h 21;
      0,0,0,0,0,0,h 4,h 7,h 10,h 11,h 13,h 14,h 16,h 19,h 20;
      0,0,0,0,0,0,0,h 4,h 7,h 8,h 10,h 11,h 13,h 16,h 17;
      0,0,0,0,0,0,0,0,h 4,h 5,h 7,h 8,h 10,h 13,h 14;
      0,0,0,0,0,0,0,0,0,h 2,h 4,h 5,h 7,h 10,h 11;
      0,0,0,0,0,0,0,0,0,1,h 2,h 3,h 5,h 8,h 9;
      0,0,0,0,0,0,0,0,0,0,0,h 2,h 4,h 7,h 8;
      0,0,0,0,0,0,0,0,0,0,0,1,h 2,h 5,h 6;
      0,0,0,0,0,0,0,0,0,0,0,0,0,h 4,h 5;
      0,0,0,0,0,0,0,0,0,0,0,0,0,0,h 2]) = h 2 ^ 2 * h 4 ^ 5 * (h 4 - h 2 ^ 2) ^ 4 := by
  repeat'
    rw [Matrix.det_succ_column_zero]
    norm_num [Fin.sum_univ_succ, Matrix.submatrix, Fin.succAbove, Matrix.det_unique]
  ring

set_option maxHeartbeats 1000000 in
-- The entry bridge checks the complete fifteen-by-fifteen integer index matrix.
/-- The complete original closure residue, under any homomorphism killing h-one. -/
theorem closure_residue_determinant {R : Type*} [CommRing R]
    (f : Lambda →+* R) (hf : f (X (1 : ℕ+)) = 0) :
    f closure.schur = f (X 2) ^ 2 * f (X 4) ^ 5 * (f (X 4) - f (X 2) ^ 2) ^ 4 := by
  have hind : (Matrix.of fun i j : Fin 15 => closure.xi i - closure.zeta j) = !![
      2,5,6,8,9,11,14,17,20,21,23,24,26,29,30;
      1,4,5,7,8,10,13,16,19,20,22,23,25,28,29;
      -2,1,2,4,5,7,10,13,16,17,19,20,22,25,26;
      -4,-1,0,2,3,5,8,11,14,15,17,18,20,23,24;
      -5,-2,-1,1,2,4,7,10,13,14,16,17,19,22,23;
      -7,-4,-3,-1,0,2,5,8,11,12,14,15,17,20,21;
      -8,-5,-4,-2,-1,1,4,7,10,11,13,14,16,19,20;
      -11,-8,-7,-5,-4,-2,1,4,7,8,10,11,13,16,17;
      -14,-11,-10,-8,-7,-5,-2,1,4,5,7,8,10,13,14;
      -17,-14,-13,-11,-10,-8,-5,-2,1,2,4,5,7,10,11;
      -19,-16,-15,-13,-12,-10,-7,-4,-1,0,2,3,5,8,9;
      -20,-17,-16,-14,-13,-11,-8,-5,-2,-1,1,2,4,7,8;
      -22,-19,-18,-16,-15,-13,-10,-7,-4,-3,-1,0,2,5,6;
      -23,-20,-19,-17,-16,-14,-11,-8,-5,-4,-2,-1,1,4,5;
      -26,-23,-22,-20,-19,-17,-14,-11,-8,-7,-5,-4,-2,1,2] := by decide
  have hm : (Matrix.of fun i j : Fin 15 => f (hh (closure.xi i - closure.zeta j))) = !![
      f (X 2),f (X 5),f (X 6),f (X 8),f (X 9),f (X 11),f (X 14),
        f (X 17),f (X 20),f (X 21),f (X 23),f (X 24),f (X 26),f (X 29),f (X 30);
      0,f (X 4),f (X 5),f (X 7),f (X 8),f (X 10),f (X 13),f (X 16),
        f (X 19),f (X 20),f (X 22),f (X 23),f (X 25),f (X 28),f (X 29);
      0,0,f (X 2),f (X 4),f (X 5),f (X 7),f (X 10),f (X 13),
        f (X 16),f (X 17),f (X 19),f (X 20),f (X 22),f (X 25),f (X 26);
      0,0,1,f (X 2),f (X 3),f (X 5),f (X 8),f (X 11),f (X 14),
        f (X 15),f (X 17),f (X 18),f (X 20),f (X 23),f (X 24);
      0,0,0,0,f (X 2),f (X 4),f (X 7),f (X 10),f (X 13),f (X 14),
        f (X 16),f (X 17),f (X 19),f (X 22),f (X 23);
      0,0,0,0,1,f (X 2),f (X 5),f (X 8),f (X 11),f (X 12),
        f (X 14),f (X 15),f (X 17),f (X 20),f (X 21);
      0,0,0,0,0,0,f (X 4),f (X 7),f (X 10),f (X 11),f (X 13),f (X 14),f (X 16),f (X 19),f (X 20);
      0,0,0,0,0,0,0,f (X 4),f (X 7),f (X 8),f (X 10),f (X 11),f (X 13),f (X 16),f (X 17);
      0,0,0,0,0,0,0,0,f (X 4),f (X 5),f (X 7),f (X 8),f (X 10),f (X 13),f (X 14);
      0,0,0,0,0,0,0,0,0,f (X 2),f (X 4),f (X 5),f (X 7),f (X 10),f (X 11);
      0,0,0,0,0,0,0,0,0,1,f (X 2),f (X 3),f (X 5),f (X 8),f (X 9);
      0,0,0,0,0,0,0,0,0,0,0,f (X 2),f (X 4),f (X 7),f (X 8);
      0,0,0,0,0,0,0,0,0,0,0,1,f (X 2),f (X 5),f (X 6);
      0,0,0,0,0,0,0,0,0,0,0,0,0,f (X 4),f (X 5);
      0,0,0,0,0,0,0,0,0,0,0,0,0,0,f (X 2)] := by
    ext i j
    have he := congrFun (congrFun hind i) j
    change closure.xi i - closure.zeta j = _ at he
    simp only [Matrix.of_apply, he]
    fin_cases i <;> fin_cases j <;> norm_num [hh, hPos, hf]
  rw [Profile.schur, RingHom.map_det]
  change (Matrix.of fun i j : Fin 15 => f (hh (closure.xi i - closure.zeta j))).det = _
  rw [hm]
  exact sparse_closure_det (fun k => f (X k))

end SkewCornerDescent.SquareWordProfiles
