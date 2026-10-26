/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.FiniteColumnReplacement

/-!
# Complete mixed amalgamation cofactor certificates

Supports `shields-2026-skew-corner-descent.tex` (`rem:square-word`).
Every original h-seven/h-one column pair is evaluated through its complete
double cofactor. Zero terms are proved, not omitted. Sorry-free.
-/

namespace SkewCornerDescent.SquareWordProfiles

open SkewCornerDescent.Matrix

/-- The complete actual amalgamation matrix on h-one zero. -/
def amalgamationResidueMatrix {R : Type*} [CommRing R] (h : ℕ+ → R) :
    Matrix (Fin 13) (Fin 13) R := !![
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
      0,0,0,0,0,0,0,0,0,0,0,0,h 2]


/-- Complete original mixed column pair (3,0). -/
theorem amalgamation_mixed_term_3_0 {R : Type*} [CommRing R] (h : ℕ+ → R) :
    (((amalgamationResidueMatrix h).updateCol 0 (Pi.single 1 1)).updateCol 3
      (Pi.single 1 1)).det = 0 := by
  exact det_same_basis_row _ _ _ _ (by decide)

set_option maxHeartbeats 4000000 in
-- The complete original double cofactor is normalized through two deletion maps.
/-- Complete original mixed column pair (3,1). -/
theorem amalgamation_mixed_term_3_1 {R : Type*} [CommRing R] (h : ℕ+ → R) :
    (((amalgamationResidueMatrix h).updateCol 1 (Pi.single 2 1)).updateCol 3
      (Pi.single 1 1)).det = (h 2) ^ 2 * (h 4) ^ 2 * ((h 2) ^ 2 - (h 4)) ^ 3 := by
  have hr : (1 : Fin 13).succAbove 1 = 2 := by decide
  have hc : (3 : Fin 13).succAbove 1 = 1 := by decide
  have he := det_two_basis_columns (amalgamationResidueMatrix h) 1 3 1 1
  rw [hr, hc] at he
  rw [he]
  norm_num
  repeat'
    rw [Matrix.det_succ_column_zero]
    norm_num [Fin.sum_univ_succ, Matrix.submatrix, Fin.succAbove,
      amalgamationResidueMatrix, Matrix.det_unique]
  all_goals ring

set_option maxHeartbeats 4000000 in
-- The complete original double cofactor is normalized through two deletion maps.
/-- Complete original mixed column pair (3,5). -/
theorem amalgamation_mixed_term_3_5 {R : Type*} [CommRing R] (h : ℕ+ → R) :
    (((amalgamationResidueMatrix h).updateCol 5 (Pi.single 6 1)).updateCol 3
      (Pi.single 1 1)).det = 0 := by
  have hr : (1 : Fin 13).succAbove 5 = 6 := by decide
  have hc : (3 : Fin 13).succAbove 4 = 5 := by decide
  have he := det_two_basis_columns (amalgamationResidueMatrix h) 1 3 5 4
  rw [hr, hc] at he
  rw [he]
  norm_num
  repeat'
    rw [Matrix.det_succ_column_zero]
    norm_num [Fin.sum_univ_succ, Matrix.submatrix, Fin.succAbove,
      amalgamationResidueMatrix, Matrix.det_unique]

set_option maxHeartbeats 4000000 in
-- The complete original double cofactor is normalized through two deletion maps.
/-- Complete original mixed column pair (3,6). -/
theorem amalgamation_mixed_term_3_6 {R : Type*} [CommRing R] (h : ℕ+ → R) :
    (((amalgamationResidueMatrix h).updateCol 6 (Pi.single 7 1)).updateCol 3
      (Pi.single 1 1)).det = 0 := by
  have hr : (1 : Fin 13).succAbove 6 = 7 := by decide
  have hc : (3 : Fin 13).succAbove 5 = 6 := by decide
  have he := det_two_basis_columns (amalgamationResidueMatrix h) 1 3 6 5
  rw [hr, hc] at he
  rw [he]
  norm_num
  repeat'
    rw [Matrix.det_succ_column_zero]
    norm_num [Fin.sum_univ_succ, Matrix.submatrix, Fin.succAbove,
      amalgamationResidueMatrix, Matrix.det_unique]

set_option maxHeartbeats 4000000 in
-- The complete original double cofactor is normalized through two deletion maps.
/-- Complete original mixed column pair (3,8). -/
theorem amalgamation_mixed_term_3_8 {R : Type*} [CommRing R] (h : ℕ+ → R) :
    (((amalgamationResidueMatrix h).updateCol 8 (Pi.single 9 1)).updateCol 3
      (Pi.single 1 1)).det = 0 := by
  have hr : (1 : Fin 13).succAbove 8 = 9 := by decide
  have hc : (3 : Fin 13).succAbove 7 = 8 := by decide
  have he := det_two_basis_columns (amalgamationResidueMatrix h) 1 3 8 7
  rw [hr, hc] at he
  rw [he]
  norm_num
  repeat'
    rw [Matrix.det_succ_column_zero]
    norm_num [Fin.sum_univ_succ, Matrix.submatrix, Fin.succAbove,
      amalgamationResidueMatrix, Matrix.det_unique]

set_option maxHeartbeats 4000000 in
-- The complete original double cofactor is normalized through two deletion maps.
/-- Complete original mixed column pair (3,10). -/
theorem amalgamation_mixed_term_3_10 {R : Type*} [CommRing R] (h : ℕ+ → R) :
    (((amalgamationResidueMatrix h).updateCol 10 (Pi.single 11 1)).updateCol 3
      (Pi.single 1 1)).det = 0 := by
  have hr : (1 : Fin 13).succAbove 10 = 11 := by decide
  have hc : (3 : Fin 13).succAbove 9 = 10 := by decide
  have he := det_two_basis_columns (amalgamationResidueMatrix h) 1 3 10 9
  rw [hr, hc] at he
  rw [he]
  norm_num
  repeat'
    rw [Matrix.det_succ_column_zero]
    norm_num [Fin.sum_univ_succ, Matrix.submatrix, Fin.succAbove,
      amalgamationResidueMatrix, Matrix.det_unique]

set_option maxHeartbeats 4000000 in
-- The complete original double cofactor is normalized through two deletion maps.
/-- Complete original mixed column pair (3,11). -/
theorem amalgamation_mixed_term_3_11 {R : Type*} [CommRing R] (h : ℕ+ → R) :
    (((amalgamationResidueMatrix h).updateCol 11 (Pi.single 12 1)).updateCol 3
      (Pi.single 1 1)).det = 0 := by
  have hr : (1 : Fin 13).succAbove 11 = 12 := by decide
  have hc : (3 : Fin 13).succAbove 10 = 11 := by decide
  have he := det_two_basis_columns (amalgamationResidueMatrix h) 1 3 11 10
  rw [hr, hc] at he
  rw [he]
  norm_num
  repeat'
    rw [Matrix.det_succ_column_zero]
    norm_num [Fin.sum_univ_succ, Matrix.submatrix, Fin.succAbove,
      amalgamationResidueMatrix, Matrix.det_unique]

set_option maxHeartbeats 4000000 in
-- The complete original double cofactor is normalized through two deletion maps.
/-- Complete original mixed column pair (5,0). -/
theorem amalgamation_mixed_term_5_0 {R : Type*} [CommRing R] (h : ℕ+ → R) :
    (((amalgamationResidueMatrix h).updateCol 0 (Pi.single 1 1)).updateCol 5
      (Pi.single 2 1)).det = 0 := by
  have hr : (2 : Fin 13).succAbove 1 = 1 := by decide
  have hc : (5 : Fin 13).succAbove 0 = 0 := by decide
  have he := det_two_basis_columns (amalgamationResidueMatrix h) 2 5 1 0
  rw [hr, hc] at he
  rw [he]
  norm_num
  repeat'
    rw [Matrix.det_succ_column_zero]
    norm_num [Fin.sum_univ_succ, Matrix.submatrix, Fin.succAbove,
      amalgamationResidueMatrix, Matrix.det_unique]

/-- Complete original mixed column pair (5,1). -/
theorem amalgamation_mixed_term_5_1 {R : Type*} [CommRing R] (h : ℕ+ → R) :
    (((amalgamationResidueMatrix h).updateCol 1 (Pi.single 2 1)).updateCol 5
      (Pi.single 2 1)).det = 0 := by
  exact det_same_basis_row _ _ _ _ (by decide)

set_option maxHeartbeats 4000000 in
-- The complete original double cofactor is normalized through two deletion maps.
/-- Complete original mixed column pair (5,3). -/
theorem amalgamation_mixed_term_5_3 {R : Type*} [CommRing R] (h : ℕ+ → R) :
    (((amalgamationResidueMatrix h).updateCol 3 (Pi.single 4 1)).updateCol 5
      (Pi.single 2 1)).det = -(h 2) ^ 2 * (h 4) ^ 3 * ((h 2) ^ 2 - (h 4)) ^ 2 := by
  have hr : (2 : Fin 13).succAbove 3 = 4 := by decide
  have hc : (5 : Fin 13).succAbove 3 = 3 := by decide
  have he := det_two_basis_columns (amalgamationResidueMatrix h) 2 5 3 3
  rw [hr, hc] at he
  rw [he]
  norm_num
  repeat'
    rw [Matrix.det_succ_column_zero]
    norm_num [Fin.sum_univ_succ, Matrix.submatrix, Fin.succAbove,
      amalgamationResidueMatrix, Matrix.det_unique]
  all_goals ring

set_option maxHeartbeats 4000000 in
-- The complete original double cofactor is normalized through two deletion maps.
/-- Complete original mixed column pair (5,6). -/
theorem amalgamation_mixed_term_5_6 {R : Type*} [CommRing R] (h : ℕ+ → R) :
    (((amalgamationResidueMatrix h).updateCol 6 (Pi.single 7 1)).updateCol 5
      (Pi.single 2 1)).det = 0 := by
  have hr : (2 : Fin 13).succAbove 6 = 7 := by decide
  have hc : (5 : Fin 13).succAbove 5 = 6 := by decide
  have he := det_two_basis_columns (amalgamationResidueMatrix h) 2 5 6 5
  rw [hr, hc] at he
  rw [he]
  norm_num
  repeat'
    rw [Matrix.det_succ_column_zero]
    norm_num [Fin.sum_univ_succ, Matrix.submatrix, Fin.succAbove,
      amalgamationResidueMatrix, Matrix.det_unique]

set_option maxHeartbeats 4000000 in
-- The complete original double cofactor is normalized through two deletion maps.
/-- Complete original mixed column pair (5,8). -/
theorem amalgamation_mixed_term_5_8 {R : Type*} [CommRing R] (h : ℕ+ → R) :
    (((amalgamationResidueMatrix h).updateCol 8 (Pi.single 9 1)).updateCol 5
      (Pi.single 2 1)).det = 0 := by
  have hr : (2 : Fin 13).succAbove 8 = 9 := by decide
  have hc : (5 : Fin 13).succAbove 7 = 8 := by decide
  have he := det_two_basis_columns (amalgamationResidueMatrix h) 2 5 8 7
  rw [hr, hc] at he
  rw [he]
  norm_num
  repeat'
    rw [Matrix.det_succ_column_zero]
    norm_num [Fin.sum_univ_succ, Matrix.submatrix, Fin.succAbove,
      amalgamationResidueMatrix, Matrix.det_unique]

set_option maxHeartbeats 4000000 in
-- The complete original double cofactor is normalized through two deletion maps.
/-- Complete original mixed column pair (5,10). -/
theorem amalgamation_mixed_term_5_10 {R : Type*} [CommRing R] (h : ℕ+ → R) :
    (((amalgamationResidueMatrix h).updateCol 10 (Pi.single 11 1)).updateCol 5
      (Pi.single 2 1)).det = 0 := by
  have hr : (2 : Fin 13).succAbove 10 = 11 := by decide
  have hc : (5 : Fin 13).succAbove 9 = 10 := by decide
  have he := det_two_basis_columns (amalgamationResidueMatrix h) 2 5 10 9
  rw [hr, hc] at he
  rw [he]
  norm_num
  repeat'
    rw [Matrix.det_succ_column_zero]
    norm_num [Fin.sum_univ_succ, Matrix.submatrix, Fin.succAbove,
      amalgamationResidueMatrix, Matrix.det_unique]

set_option maxHeartbeats 4000000 in
-- The complete original double cofactor is normalized through two deletion maps.
/-- Complete original mixed column pair (5,11). -/
theorem amalgamation_mixed_term_5_11 {R : Type*} [CommRing R] (h : ℕ+ → R) :
    (((amalgamationResidueMatrix h).updateCol 11 (Pi.single 12 1)).updateCol 5
      (Pi.single 2 1)).det = 0 := by
  have hr : (2 : Fin 13).succAbove 11 = 12 := by decide
  have hc : (5 : Fin 13).succAbove 10 = 11 := by decide
  have he := det_two_basis_columns (amalgamationResidueMatrix h) 2 5 11 10
  rw [hr, hc] at he
  rw [he]
  norm_num
  repeat'
    rw [Matrix.det_succ_column_zero]
    norm_num [Fin.sum_univ_succ, Matrix.submatrix, Fin.succAbove,
      amalgamationResidueMatrix, Matrix.det_unique]

set_option maxHeartbeats 4000000 in
-- The complete original double cofactor is normalized through two deletion maps.
/-- Complete original mixed column pair (6,0). -/
theorem amalgamation_mixed_term_6_0 {R : Type*} [CommRing R] (h : ℕ+ → R) :
    (((amalgamationResidueMatrix h).updateCol 0 (Pi.single 1 1)).updateCol 6
      (Pi.single 4 1)).det = 0 := by
  have hr : (4 : Fin 13).succAbove 1 = 1 := by decide
  have hc : (6 : Fin 13).succAbove 0 = 0 := by decide
  have he := det_two_basis_columns (amalgamationResidueMatrix h) 4 6 1 0
  rw [hr, hc] at he
  rw [he]
  norm_num
  repeat'
    rw [Matrix.det_succ_column_zero]
    norm_num [Fin.sum_univ_succ, Matrix.submatrix, Fin.succAbove,
      amalgamationResidueMatrix, Matrix.det_unique]

set_option maxHeartbeats 4000000 in
-- The complete original double cofactor is normalized through two deletion maps.
/-- Complete original mixed column pair (6,1). -/
theorem amalgamation_mixed_term_6_1 {R : Type*} [CommRing R] (h : ℕ+ → R) :
    (((amalgamationResidueMatrix h).updateCol 1 (Pi.single 2 1)).updateCol 6
      (Pi.single 4 1)).det = 0 := by
  have hr : (4 : Fin 13).succAbove 2 = 2 := by decide
  have hc : (6 : Fin 13).succAbove 1 = 1 := by decide
  have he := det_two_basis_columns (amalgamationResidueMatrix h) 4 6 2 1
  rw [hr, hc] at he
  rw [he]
  norm_num
  repeat'
    rw [Matrix.det_succ_column_zero]
    norm_num [Fin.sum_univ_succ, Matrix.submatrix, Fin.succAbove,
      amalgamationResidueMatrix, Matrix.det_unique]

/-- Complete original mixed column pair (6,3). -/
theorem amalgamation_mixed_term_6_3 {R : Type*} [CommRing R] (h : ℕ+ → R) :
    (((amalgamationResidueMatrix h).updateCol 3 (Pi.single 4 1)).updateCol 6
      (Pi.single 4 1)).det = 0 := by
  exact det_same_basis_row _ _ _ _ (by decide)

set_option maxHeartbeats 4000000 in
-- The complete original double cofactor is normalized through two deletion maps.
/-- Complete original mixed column pair (6,5). -/
theorem amalgamation_mixed_term_6_5 {R : Type*} [CommRing R] (h : ℕ+ → R) :
    (((amalgamationResidueMatrix h).updateCol 5 (Pi.single 6 1)).updateCol 6
      (Pi.single 4 1)).det = (h 2) ^ 2 * (h 4) ^ 2 * ((h 2) ^ 2 - (h 4)) ^ 3 := by
  have hr : (4 : Fin 13).succAbove 5 = 6 := by decide
  have hc : (6 : Fin 13).succAbove 5 = 5 := by decide
  have he := det_two_basis_columns (amalgamationResidueMatrix h) 4 6 5 5
  rw [hr, hc] at he
  rw [he]
  norm_num
  repeat'
    rw [Matrix.det_succ_column_zero]
    norm_num [Fin.sum_univ_succ, Matrix.submatrix, Fin.succAbove,
      amalgamationResidueMatrix, Matrix.det_unique]
  all_goals ring

set_option maxHeartbeats 4000000 in
-- The complete original double cofactor is normalized through two deletion maps.
/-- Complete original mixed column pair (6,8). -/
theorem amalgamation_mixed_term_6_8 {R : Type*} [CommRing R] (h : ℕ+ → R) :
    (((amalgamationResidueMatrix h).updateCol 8 (Pi.single 9 1)).updateCol 6
      (Pi.single 4 1)).det = 0 := by
  have hr : (4 : Fin 13).succAbove 8 = 9 := by decide
  have hc : (6 : Fin 13).succAbove 7 = 8 := by decide
  have he := det_two_basis_columns (amalgamationResidueMatrix h) 4 6 8 7
  rw [hr, hc] at he
  rw [he]
  norm_num
  repeat'
    rw [Matrix.det_succ_column_zero]
    norm_num [Fin.sum_univ_succ, Matrix.submatrix, Fin.succAbove,
      amalgamationResidueMatrix, Matrix.det_unique]

set_option maxHeartbeats 4000000 in
-- The complete original double cofactor is normalized through two deletion maps.
/-- Complete original mixed column pair (6,10). -/
theorem amalgamation_mixed_term_6_10 {R : Type*} [CommRing R] (h : ℕ+ → R) :
    (((amalgamationResidueMatrix h).updateCol 10 (Pi.single 11 1)).updateCol 6
      (Pi.single 4 1)).det = 0 := by
  have hr : (4 : Fin 13).succAbove 10 = 11 := by decide
  have hc : (6 : Fin 13).succAbove 9 = 10 := by decide
  have he := det_two_basis_columns (amalgamationResidueMatrix h) 4 6 10 9
  rw [hr, hc] at he
  rw [he]
  norm_num
  repeat'
    rw [Matrix.det_succ_column_zero]
    norm_num [Fin.sum_univ_succ, Matrix.submatrix, Fin.succAbove,
      amalgamationResidueMatrix, Matrix.det_unique]

set_option maxHeartbeats 4000000 in
-- The complete original double cofactor is normalized through two deletion maps.
/-- Complete original mixed column pair (6,11). -/
theorem amalgamation_mixed_term_6_11 {R : Type*} [CommRing R] (h : ℕ+ → R) :
    (((amalgamationResidueMatrix h).updateCol 11 (Pi.single 12 1)).updateCol 6
      (Pi.single 4 1)).det = 0 := by
  have hr : (4 : Fin 13).succAbove 11 = 12 := by decide
  have hc : (6 : Fin 13).succAbove 10 = 11 := by decide
  have he := det_two_basis_columns (amalgamationResidueMatrix h) 4 6 11 10
  rw [hr, hc] at he
  rw [he]
  norm_num
  repeat'
    rw [Matrix.det_succ_column_zero]
    norm_num [Fin.sum_univ_succ, Matrix.submatrix, Fin.succAbove,
      amalgamationResidueMatrix, Matrix.det_unique]

set_option maxHeartbeats 4000000 in
-- The complete original double cofactor is normalized through two deletion maps.
/-- Complete original mixed column pair (8,0). -/
theorem amalgamation_mixed_term_8_0 {R : Type*} [CommRing R] (h : ℕ+ → R) :
    (((amalgamationResidueMatrix h).updateCol 0 (Pi.single 1 1)).updateCol 8
      (Pi.single 6 1)).det = 0 := by
  have hr : (6 : Fin 13).succAbove 1 = 1 := by decide
  have hc : (8 : Fin 13).succAbove 0 = 0 := by decide
  have he := det_two_basis_columns (amalgamationResidueMatrix h) 6 8 1 0
  rw [hr, hc] at he
  rw [he]
  norm_num
  repeat'
    rw [Matrix.det_succ_column_zero]
    norm_num [Fin.sum_univ_succ, Matrix.submatrix, Fin.succAbove,
      amalgamationResidueMatrix, Matrix.det_unique]

set_option maxHeartbeats 4000000 in
-- The complete original double cofactor is normalized through two deletion maps.
/-- Complete original mixed column pair (8,1). -/
theorem amalgamation_mixed_term_8_1 {R : Type*} [CommRing R] (h : ℕ+ → R) :
    (((amalgamationResidueMatrix h).updateCol 1 (Pi.single 2 1)).updateCol 8
      (Pi.single 6 1)).det = 0 := by
  have hr : (6 : Fin 13).succAbove 2 = 2 := by decide
  have hc : (8 : Fin 13).succAbove 1 = 1 := by decide
  have he := det_two_basis_columns (amalgamationResidueMatrix h) 6 8 2 1
  rw [hr, hc] at he
  rw [he]
  norm_num
  repeat'
    rw [Matrix.det_succ_column_zero]
    norm_num [Fin.sum_univ_succ, Matrix.submatrix, Fin.succAbove,
      amalgamationResidueMatrix, Matrix.det_unique]

set_option maxHeartbeats 4000000 in
-- The complete original double cofactor is normalized through two deletion maps.
/-- Complete original mixed column pair (8,3). -/
theorem amalgamation_mixed_term_8_3 {R : Type*} [CommRing R] (h : ℕ+ → R) :
    (((amalgamationResidueMatrix h).updateCol 3 (Pi.single 4 1)).updateCol 8
      (Pi.single 6 1)).det = 0 := by
  have hr : (6 : Fin 13).succAbove 4 = 4 := by decide
  have hc : (8 : Fin 13).succAbove 3 = 3 := by decide
  have he := det_two_basis_columns (amalgamationResidueMatrix h) 6 8 4 3
  rw [hr, hc] at he
  rw [he]
  norm_num
  repeat'
    rw [Matrix.det_succ_column_zero]
    norm_num [Fin.sum_univ_succ, Matrix.submatrix, Fin.succAbove,
      amalgamationResidueMatrix, Matrix.det_unique]

/-- Complete original mixed column pair (8,5). -/
theorem amalgamation_mixed_term_8_5 {R : Type*} [CommRing R] (h : ℕ+ → R) :
    (((amalgamationResidueMatrix h).updateCol 5 (Pi.single 6 1)).updateCol 8
      (Pi.single 6 1)).det = 0 := by
  exact det_same_basis_row _ _ _ _ (by decide)

set_option maxHeartbeats 4000000 in
-- The complete original double cofactor is normalized through two deletion maps.
/-- Complete original mixed column pair (8,6). -/
theorem amalgamation_mixed_term_8_6 {R : Type*} [CommRing R] (h : ℕ+ → R) :
    (((amalgamationResidueMatrix h).updateCol 6 (Pi.single 7 1)).updateCol 8
      (Pi.single 6 1)).det = (h 2) ^ 2 * (h 4) ^ 2 * ((h 2) ^ 2 - (h 4)) ^ 3 := by
  have hr : (6 : Fin 13).succAbove 6 = 7 := by decide
  have hc : (8 : Fin 13).succAbove 6 = 6 := by decide
  have he := det_two_basis_columns (amalgamationResidueMatrix h) 6 8 6 6
  rw [hr, hc] at he
  rw [he]
  norm_num
  repeat'
    rw [Matrix.det_succ_column_zero]
    norm_num [Fin.sum_univ_succ, Matrix.submatrix, Fin.succAbove,
      amalgamationResidueMatrix, Matrix.det_unique]
  all_goals ring

set_option maxHeartbeats 4000000 in
-- The complete original double cofactor is normalized through two deletion maps.
/-- Complete original mixed column pair (8,10). -/
theorem amalgamation_mixed_term_8_10 {R : Type*} [CommRing R] (h : ℕ+ → R) :
    (((amalgamationResidueMatrix h).updateCol 10 (Pi.single 11 1)).updateCol 8
      (Pi.single 6 1)).det = 0 := by
  have hr : (6 : Fin 13).succAbove 10 = 11 := by decide
  have hc : (8 : Fin 13).succAbove 9 = 10 := by decide
  have he := det_two_basis_columns (amalgamationResidueMatrix h) 6 8 10 9
  rw [hr, hc] at he
  rw [he]
  norm_num
  repeat'
    rw [Matrix.det_succ_column_zero]
    norm_num [Fin.sum_univ_succ, Matrix.submatrix, Fin.succAbove,
      amalgamationResidueMatrix, Matrix.det_unique]

set_option maxHeartbeats 4000000 in
-- The complete original double cofactor is normalized through two deletion maps.
/-- Complete original mixed column pair (8,11). -/
theorem amalgamation_mixed_term_8_11 {R : Type*} [CommRing R] (h : ℕ+ → R) :
    (((amalgamationResidueMatrix h).updateCol 11 (Pi.single 12 1)).updateCol 8
      (Pi.single 6 1)).det = 0 := by
  have hr : (6 : Fin 13).succAbove 11 = 12 := by decide
  have hc : (8 : Fin 13).succAbove 10 = 11 := by decide
  have he := det_two_basis_columns (amalgamationResidueMatrix h) 6 8 11 10
  rw [hr, hc] at he
  rw [he]
  norm_num
  repeat'
    rw [Matrix.det_succ_column_zero]
    norm_num [Fin.sum_univ_succ, Matrix.submatrix, Fin.succAbove,
      amalgamationResidueMatrix, Matrix.det_unique]

set_option maxHeartbeats 4000000 in
-- The complete original double cofactor is normalized through two deletion maps.
/-- Complete original mixed column pair (10,0). -/
theorem amalgamation_mixed_term_10_0 {R : Type*} [CommRing R] (h : ℕ+ → R) :
    (((amalgamationResidueMatrix h).updateCol 0 (Pi.single 1 1)).updateCol 10
      (Pi.single 7 1)).det = 0 := by
  have hr : (7 : Fin 13).succAbove 1 = 1 := by decide
  have hc : (10 : Fin 13).succAbove 0 = 0 := by decide
  have he := det_two_basis_columns (amalgamationResidueMatrix h) 7 10 1 0
  rw [hr, hc] at he
  rw [he]
  norm_num
  repeat'
    rw [Matrix.det_succ_column_zero]
    norm_num [Fin.sum_univ_succ, Matrix.submatrix, Fin.succAbove,
      amalgamationResidueMatrix, Matrix.det_unique]

set_option maxHeartbeats 4000000 in
-- The complete original double cofactor is normalized through two deletion maps.
/-- Complete original mixed column pair (10,1). -/
theorem amalgamation_mixed_term_10_1 {R : Type*} [CommRing R] (h : ℕ+ → R) :
    (((amalgamationResidueMatrix h).updateCol 1 (Pi.single 2 1)).updateCol 10
      (Pi.single 7 1)).det = 0 := by
  have hr : (7 : Fin 13).succAbove 2 = 2 := by decide
  have hc : (10 : Fin 13).succAbove 1 = 1 := by decide
  have he := det_two_basis_columns (amalgamationResidueMatrix h) 7 10 2 1
  rw [hr, hc] at he
  rw [he]
  norm_num
  repeat'
    rw [Matrix.det_succ_column_zero]
    norm_num [Fin.sum_univ_succ, Matrix.submatrix, Fin.succAbove,
      amalgamationResidueMatrix, Matrix.det_unique]

set_option maxHeartbeats 4000000 in
-- The complete original double cofactor is normalized through two deletion maps.
/-- Complete original mixed column pair (10,3). -/
theorem amalgamation_mixed_term_10_3 {R : Type*} [CommRing R] (h : ℕ+ → R) :
    (((amalgamationResidueMatrix h).updateCol 3 (Pi.single 4 1)).updateCol 10
      (Pi.single 7 1)).det = 0 := by
  have hr : (7 : Fin 13).succAbove 4 = 4 := by decide
  have hc : (10 : Fin 13).succAbove 3 = 3 := by decide
  have he := det_two_basis_columns (amalgamationResidueMatrix h) 7 10 4 3
  rw [hr, hc] at he
  rw [he]
  norm_num
  repeat'
    rw [Matrix.det_succ_column_zero]
    norm_num [Fin.sum_univ_succ, Matrix.submatrix, Fin.succAbove,
      amalgamationResidueMatrix, Matrix.det_unique]

set_option maxHeartbeats 4000000 in
-- The complete original double cofactor is normalized through two deletion maps.
/-- Complete original mixed column pair (10,5). -/
theorem amalgamation_mixed_term_10_5 {R : Type*} [CommRing R] (h : ℕ+ → R) :
    (((amalgamationResidueMatrix h).updateCol 5 (Pi.single 6 1)).updateCol 10
      (Pi.single 7 1)).det = 0 := by
  have hr : (7 : Fin 13).succAbove 6 = 6 := by decide
  have hc : (10 : Fin 13).succAbove 5 = 5 := by decide
  have he := det_two_basis_columns (amalgamationResidueMatrix h) 7 10 6 5
  rw [hr, hc] at he
  rw [he]
  norm_num
  repeat'
    rw [Matrix.det_succ_column_zero]
    norm_num [Fin.sum_univ_succ, Matrix.submatrix, Fin.succAbove,
      amalgamationResidueMatrix, Matrix.det_unique]

/-- Complete original mixed column pair (10,6). -/
theorem amalgamation_mixed_term_10_6 {R : Type*} [CommRing R] (h : ℕ+ → R) :
    (((amalgamationResidueMatrix h).updateCol 6 (Pi.single 7 1)).updateCol 10
      (Pi.single 7 1)).det = 0 := by
  exact det_same_basis_row _ _ _ _ (by decide)

set_option maxHeartbeats 4000000 in
-- The complete original double cofactor is normalized through two deletion maps.
/-- Complete original mixed column pair (10,8). -/
theorem amalgamation_mixed_term_10_8 {R : Type*} [CommRing R] (h : ℕ+ → R) :
    (((amalgamationResidueMatrix h).updateCol 8 (Pi.single 9 1)).updateCol 10
      (Pi.single 7 1)).det = -(h 2) ^ 2 * (h 4) ^ 3 * ((h 2) ^ 2 - (h 4)) ^ 2 := by
  have hr : (7 : Fin 13).succAbove 8 = 9 := by decide
  have hc : (10 : Fin 13).succAbove 8 = 8 := by decide
  have he := det_two_basis_columns (amalgamationResidueMatrix h) 7 10 8 8
  rw [hr, hc] at he
  rw [he]
  norm_num
  repeat'
    rw [Matrix.det_succ_column_zero]
    norm_num [Fin.sum_univ_succ, Matrix.submatrix, Fin.succAbove,
      amalgamationResidueMatrix, Matrix.det_unique]
  all_goals ring

set_option maxHeartbeats 4000000 in
-- The complete original double cofactor is normalized through two deletion maps.
/-- Complete original mixed column pair (10,11). -/
theorem amalgamation_mixed_term_10_11 {R : Type*} [CommRing R] (h : ℕ+ → R) :
    (((amalgamationResidueMatrix h).updateCol 11 (Pi.single 12 1)).updateCol 10
      (Pi.single 7 1)).det = 0 := by
  have hr : (7 : Fin 13).succAbove 11 = 12 := by decide
  have hc : (10 : Fin 13).succAbove 10 = 11 := by decide
  have he := det_two_basis_columns (amalgamationResidueMatrix h) 7 10 11 10
  rw [hr, hc] at he
  rw [he]
  norm_num
  repeat'
    rw [Matrix.det_succ_column_zero]
    norm_num [Fin.sum_univ_succ, Matrix.submatrix, Fin.succAbove,
      amalgamationResidueMatrix, Matrix.det_unique]

set_option maxHeartbeats 4000000 in
-- The complete original double cofactor is normalized through two deletion maps.
/-- Complete original mixed column pair (11,0). -/
theorem amalgamation_mixed_term_11_0 {R : Type*} [CommRing R] (h : ℕ+ → R) :
    (((amalgamationResidueMatrix h).updateCol 0 (Pi.single 1 1)).updateCol 11
      (Pi.single 9 1)).det = 0 := by
  have hr : (9 : Fin 13).succAbove 1 = 1 := by decide
  have hc : (11 : Fin 13).succAbove 0 = 0 := by decide
  have he := det_two_basis_columns (amalgamationResidueMatrix h) 9 11 1 0
  rw [hr, hc] at he
  rw [he]
  norm_num
  repeat'
    rw [Matrix.det_succ_column_zero]
    norm_num [Fin.sum_univ_succ, Matrix.submatrix, Fin.succAbove,
      amalgamationResidueMatrix, Matrix.det_unique]

set_option maxHeartbeats 4000000 in
-- The complete original double cofactor is normalized through two deletion maps.
/-- Complete original mixed column pair (11,1). -/
theorem amalgamation_mixed_term_11_1 {R : Type*} [CommRing R] (h : ℕ+ → R) :
    (((amalgamationResidueMatrix h).updateCol 1 (Pi.single 2 1)).updateCol 11
      (Pi.single 9 1)).det = 0 := by
  have hr : (9 : Fin 13).succAbove 2 = 2 := by decide
  have hc : (11 : Fin 13).succAbove 1 = 1 := by decide
  have he := det_two_basis_columns (amalgamationResidueMatrix h) 9 11 2 1
  rw [hr, hc] at he
  rw [he]
  norm_num
  repeat'
    rw [Matrix.det_succ_column_zero]
    norm_num [Fin.sum_univ_succ, Matrix.submatrix, Fin.succAbove,
      amalgamationResidueMatrix, Matrix.det_unique]

set_option maxHeartbeats 4000000 in
-- The complete original double cofactor is normalized through two deletion maps.
/-- Complete original mixed column pair (11,3). -/
theorem amalgamation_mixed_term_11_3 {R : Type*} [CommRing R] (h : ℕ+ → R) :
    (((amalgamationResidueMatrix h).updateCol 3 (Pi.single 4 1)).updateCol 11
      (Pi.single 9 1)).det = 0 := by
  have hr : (9 : Fin 13).succAbove 4 = 4 := by decide
  have hc : (11 : Fin 13).succAbove 3 = 3 := by decide
  have he := det_two_basis_columns (amalgamationResidueMatrix h) 9 11 4 3
  rw [hr, hc] at he
  rw [he]
  norm_num
  repeat'
    rw [Matrix.det_succ_column_zero]
    norm_num [Fin.sum_univ_succ, Matrix.submatrix, Fin.succAbove,
      amalgamationResidueMatrix, Matrix.det_unique]

set_option maxHeartbeats 4000000 in
-- The complete original double cofactor is normalized through two deletion maps.
/-- Complete original mixed column pair (11,5). -/
theorem amalgamation_mixed_term_11_5 {R : Type*} [CommRing R] (h : ℕ+ → R) :
    (((amalgamationResidueMatrix h).updateCol 5 (Pi.single 6 1)).updateCol 11
      (Pi.single 9 1)).det = 0 := by
  have hr : (9 : Fin 13).succAbove 6 = 6 := by decide
  have hc : (11 : Fin 13).succAbove 5 = 5 := by decide
  have he := det_two_basis_columns (amalgamationResidueMatrix h) 9 11 6 5
  rw [hr, hc] at he
  rw [he]
  norm_num
  repeat'
    rw [Matrix.det_succ_column_zero]
    norm_num [Fin.sum_univ_succ, Matrix.submatrix, Fin.succAbove,
      amalgamationResidueMatrix, Matrix.det_unique]

set_option maxHeartbeats 4000000 in
-- The complete original double cofactor is normalized through two deletion maps.
/-- Complete original mixed column pair (11,6). -/
theorem amalgamation_mixed_term_11_6 {R : Type*} [CommRing R] (h : ℕ+ → R) :
    (((amalgamationResidueMatrix h).updateCol 6 (Pi.single 7 1)).updateCol 11
      (Pi.single 9 1)).det = 0 := by
  have hr : (9 : Fin 13).succAbove 7 = 7 := by decide
  have hc : (11 : Fin 13).succAbove 6 = 6 := by decide
  have he := det_two_basis_columns (amalgamationResidueMatrix h) 9 11 7 6
  rw [hr, hc] at he
  rw [he]
  norm_num
  repeat'
    rw [Matrix.det_succ_column_zero]
    norm_num [Fin.sum_univ_succ, Matrix.submatrix, Fin.succAbove,
      amalgamationResidueMatrix, Matrix.det_unique]

/-- Complete original mixed column pair (11,8). -/
theorem amalgamation_mixed_term_11_8 {R : Type*} [CommRing R] (h : ℕ+ → R) :
    (((amalgamationResidueMatrix h).updateCol 8 (Pi.single 9 1)).updateCol 11
      (Pi.single 9 1)).det = 0 := by
  exact det_same_basis_row _ _ _ _ (by decide)

set_option maxHeartbeats 4000000 in
-- The complete original double cofactor is normalized through two deletion maps.
/-- Complete original mixed column pair (11,10). -/
theorem amalgamation_mixed_term_11_10 {R : Type*} [CommRing R] (h : ℕ+ → R) :
    (((amalgamationResidueMatrix h).updateCol 10 (Pi.single 11 1)).updateCol 11
      (Pi.single 9 1)).det = (h 2) ^ 2 * (h 4) ^ 2 * ((h 2) ^ 2 - (h 4)) ^ 3 := by
  have hr : (9 : Fin 13).succAbove 10 = 11 := by decide
  have hc : (11 : Fin 13).succAbove 10 = 10 := by decide
  have he := det_two_basis_columns (amalgamationResidueMatrix h) 9 11 10 10
  rw [hr, hc] at he
  rw [he]
  norm_num
  repeat'
    rw [Matrix.det_succ_column_zero]
    norm_num [Fin.sum_univ_succ, Matrix.submatrix, Fin.succAbove,
      amalgamationResidueMatrix, Matrix.det_unique]
  all_goals ring

end SkewCornerDescent.SquareWordProfiles
