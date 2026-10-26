/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.SquareWordSourceMixed
import SkewCornerDescent.SquareWordMixed
import SkewCornerDescent.SquareWordAmalgamationMixedTerms
import SkewCornerDescent.SquareWordClosureMixedTerms

/-!
# Full original mixed union and closure jets of the square word

Supports `shields-2026-skew-corner-descent.tex` (`rem:square-word`).
Both derivatives use complete column replacements before h-one specialization.
No inverse or denominator is frozen. Sorry-free.
-/

namespace SkewCornerDescent.SquareWordProfiles

open SkewGluing MvPolynomial
open scoped BigOperators

@[simp]
private theorem det_zero_column_update {ν R : Type*} [Fintype ν] [DecidableEq ν]
    [CommRing R] (M : Matrix ν ν R) (j : ν) : (M.updateCol j 0).det = 0 := by
  apply Matrix.det_eq_zero_of_column_eq_zero j
  intro r
  simp

@[simp]
private theorem det_zero_column_update_other {ν R : Type*}
    [Fintype ν] [DecidableEq ν] [CommRing R]
    (M : Matrix ν ν R) (i j : ν) (v : ν → R) :
    ((M.updateCol j 0).updateCol i v).det =
      if i = j then (M.updateCol i v).det else 0 := by
  by_cases hij : i = j
  · subst i
    simp
  · rw [ite_eq_right hij]
    apply Matrix.det_eq_zero_of_column_eq_zero j
    intro r
    simp only [Matrix.updateCol_apply, ite_eq_right (Ne.symm hij), ite_true,
      Pi.zero_apply]

set_option maxHeartbeats 8000000 in
-- The full mixed path sum retains both complete 13-row column replacements.
/-- The actual h-seven/h-one mixed amalgamation determinant coefficient. -/
theorem amalgamation_original_mixed_jet {R : Type*} [CommRing R]
    (f : Lambda →+* R) (hf : f (X (1 : ℕ+)) = 0) :
    f (pderiv (7 : ℕ+) (pderiv (1 : ℕ+) amalgamation.schur)) =
      2 * f (X 2) ^ 2 * f (X 4) ^ 2 * (f (X 4) - f (X 2) ^ 2) ^ 2 *
        (2 * f (X 2) ^ 2 - 3 * f (X 4)) := by
  let M : Matrix (Fin 13) (Fin 13) R := !![
      f (X 2),f (X 5),f (X 6),f (X 8),f (X 9),f (X 11),f (X 14),f (X 15),f (X 17),f (X 18),
        f (X 20),f (X 23),f (X 24);
      0,f (X 4),f (X 5),f (X 7),f (X 8),f (X 10),f (X 13),f (X 14),f (X 16),f (X 17),f (X 19),
        f (X 22),f (X 23);
      0,0,f (X 2),f (X 4),f (X 5),f (X 7),f (X 10),f (X 11),f (X 13),f (X 14),f (X 16),f (X 19),
        f (X 20);
      0,0,1,f (X 2),f (X 3),f (X 5),f (X 8),f (X 9),f (X 11),f (X 12),f (X 14),f (X 17),f (X 18);
      0,0,0,0,f (X 2),f (X 4),f (X 7),f (X 8),f (X 10),f (X 11),f (X 13),f (X 16),f (X 17);
      0,0,0,0,1,f (X 2),f (X 5),f (X 6),f (X 8),f (X 9),f (X 11),f (X 14),f (X 15);
      0,0,0,0,0,0,f (X 4),f (X 5),f (X 7),f (X 8),f (X 10),f (X 13),f (X 14);
      0,0,0,0,0,0,0,f (X 2),f (X 4),f (X 5),f (X 7),f (X 10),f (X 11);
      0,0,0,0,0,0,0,1,f (X 2),f (X 3),f (X 5),f (X 8),f (X 9);
      0,0,0,0,0,0,0,0,0,f (X 2),f (X 4),f (X 7),f (X 8);
      0,0,0,0,0,0,0,0,0,1,f (X 2),f (X 5),f (X 6);
      0,0,0,0,0,0,0,0,0,0,0,f (X 4),f (X 5);
      0,0,0,0,0,0,0,0,0,0,0,0,f (X 2)]
  let e : Fin 13 → Fin 13 → R := ![Pi.single 1 1,Pi.single 2 1,0,Pi.single 4 1,0,Pi.single 6 1,
    Pi.single 7 1,0,Pi.single 9 1,0,Pi.single 11 1,Pi.single 12 1,0 ]
  let d : Fin 13 → Fin 13 → R := ![0,0,0,Pi.single 1 1,0,Pi.single 2 1,Pi.single 4 1,0,
    Pi.single 6 1,0,Pi.single 7 1,Pi.single 9 1,0 ]
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
  have hval (i j : Fin 13) : f (hh (amalgamation.xi i - amalgamation.zeta j)) = M i j := by
    have he := congrFun (congrFun hind i) j
    change amalgamation.xi i - amalgamation.zeta j = _ at he
    rw [he]
    fin_cases i <;> fin_cases j <;> norm_num [M, hh, hPos, hf]
  have he (i j : Fin 13) :
      (if amalgamation.xi i - amalgamation.zeta j = (1 : ℤ) then 1 else 0 : R) = e j i := by
    have hi := congrFun (congrFun hind i) j
    change amalgamation.xi i - amalgamation.zeta j = _ at hi
    rw [hi]
    fin_cases i <;> fin_cases j <;> norm_num [e, Pi.single_apply]
  have hd (i j : Fin 13) :
      (if amalgamation.xi i - amalgamation.zeta j = (7 : ℤ) then 1 else 0 : R) = d j i := by
    have hi := congrFun (congrFun hind i) j
    change amalgamation.xi i - amalgamation.zeta j = _ at hi
    rw [hi]
    fin_cases i <;> fin_cases j <;> norm_num [d, Pi.single_apply]
  let idx : Matrix (Fin 13) (Fin 13) ℤ := fun i j =>
    amalgamation.xi i - amalgamation.zeta j
  have hpoly : amalgamation.schur = (Matrix.of fun i j => hh (idx i j)).det := rfl
  rw [hpoly, hom_mixed_hh_det f idx 7 1]
  have hterm (i j : Fin 13) :
      (((Matrix.of fun r s => f (hh (idx r s))).updateCol j
        (fun r => if idx r j = ((1 : ℕ+) : ℤ) then 1 else 0)).updateCol i
        (fun r => if idx r i = ((7 : ℕ+) : ℤ) then 1 else 0)) =
      (M.updateCol j (e j)).updateCol i (d i) := by
    ext r s
    simp only [Matrix.updateCol_apply, Matrix.of_apply]
    by_cases hsi : s = i
    · simp only [ite_eq_left hsi]
      exact hd r i
    · simp only [ite_eq_right hsi]
      by_cases hsj : s = j
      · simp only [ite_eq_left hsj]
        exact he r j
      · simp only [ite_eq_right hsj]
        exact hval r s
  simp_rw [hterm]
  change (∑ j : Fin 13, ∑ i : Fin 13, if i = j then 0 else
    ((M.updateCol j (e j)).updateCol i (d i)).det) = _
  have hM : M = amalgamationResidueMatrix (fun k => f (X k)) := rfl
  rw [hM]
  norm_num [Fin.sum_univ_succ, e, d,
    amalgamation_mixed_term_3_0, amalgamation_mixed_term_3_1,
    amalgamation_mixed_term_3_5, amalgamation_mixed_term_3_6,
    amalgamation_mixed_term_3_8, amalgamation_mixed_term_3_10,
    amalgamation_mixed_term_3_11, amalgamation_mixed_term_5_0,
    amalgamation_mixed_term_5_1, amalgamation_mixed_term_5_3,
    amalgamation_mixed_term_5_6, amalgamation_mixed_term_5_8,
    amalgamation_mixed_term_5_10, amalgamation_mixed_term_5_11,
    amalgamation_mixed_term_6_0, amalgamation_mixed_term_6_1,
    amalgamation_mixed_term_6_3, amalgamation_mixed_term_6_5,
    amalgamation_mixed_term_6_8, amalgamation_mixed_term_6_10,
    amalgamation_mixed_term_6_11, amalgamation_mixed_term_8_0,
    amalgamation_mixed_term_8_1, amalgamation_mixed_term_8_3,
    amalgamation_mixed_term_8_5, amalgamation_mixed_term_8_6,
    amalgamation_mixed_term_8_10, amalgamation_mixed_term_8_11,
    amalgamation_mixed_term_10_0, amalgamation_mixed_term_10_1,
    amalgamation_mixed_term_10_3, amalgamation_mixed_term_10_5,
    amalgamation_mixed_term_10_6, amalgamation_mixed_term_10_8,
    amalgamation_mixed_term_10_11, amalgamation_mixed_term_11_0,
    amalgamation_mixed_term_11_1, amalgamation_mixed_term_11_3,
    amalgamation_mixed_term_11_5, amalgamation_mixed_term_11_6,
    amalgamation_mixed_term_11_8, amalgamation_mixed_term_11_10]
  ring

set_option maxHeartbeats 8000000 in
-- The full mixed path sum retains both complete 15-row column replacements.
/-- The actual h-seven/h-one mixed closure determinant coefficient. -/
theorem closure_original_mixed_jet {R : Type*} [CommRing R]
    (f : Lambda →+* R) (hf : f (X (1 : ℕ+)) = 0) :
    f (pderiv (7 : ℕ+) (pderiv (1 : ℕ+) closure.schur)) =
      -2 * f (X 2) ^ 2 * f (X 4) ^ 3 * (f (X 2) ^ 2 - 2 * f (X 4)) ^ 2 *
        (f (X 4) - f (X 2) ^ 2) ^ 2 := by
  let M : Matrix (Fin 15) (Fin 15) R := !![
      f (X 2),f (X 5),f (X 6),f (X 8),f (X 9),f (X 11),f (X 14),f (X 17),f (X 20),f (X 21),
        f (X 23),f (X 24),f (X 26),f (X 29),f (X 30);
      0,f (X 4),f (X 5),f (X 7),f (X 8),f (X 10),f (X 13),f (X 16),f (X 19),f (X 20),f (X 22),
        f (X 23),f (X 25),f (X 28),f (X 29);
      0,0,f (X 2),f (X 4),f (X 5),f (X 7),f (X 10),f (X 13),f (X 16),f (X 17),f (X 19),f (X 20),
        f (X 22),f (X 25),f (X 26);
      0,0,1,f (X 2),f (X 3),f (X 5),f (X 8),f (X 11),f (X 14),f (X 15),f (X 17),f (X 18),f (X 20),
        f (X 23),f (X 24);
      0,0,0,0,f (X 2),f (X 4),f (X 7),f (X 10),f (X 13),f (X 14),f (X 16),f (X 17),f (X 19),
        f (X 22),f (X 23);
      0,0,0,0,1,f (X 2),f (X 5),f (X 8),f (X 11),f (X 12),f (X 14),f (X 15),f (X 17),f (X 20),
        f (X 21);
      0,0,0,0,0,0,f (X 4),f (X 7),f (X 10),f (X 11),f (X 13),f (X 14),f (X 16),f (X 19),f (X 20);
      0,0,0,0,0,0,0,f (X 4),f (X 7),f (X 8),f (X 10),f (X 11),f (X 13),f (X 16),f (X 17);
      0,0,0,0,0,0,0,0,f (X 4),f (X 5),f (X 7),f (X 8),f (X 10),f (X 13),f (X 14);
      0,0,0,0,0,0,0,0,0,f (X 2),f (X 4),f (X 5),f (X 7),f (X 10),f (X 11);
      0,0,0,0,0,0,0,0,0,1,f (X 2),f (X 3),f (X 5),f (X 8),f (X 9);
      0,0,0,0,0,0,0,0,0,0,0,f (X 2),f (X 4),f (X 7),f (X 8);
      0,0,0,0,0,0,0,0,0,0,0,1,f (X 2),f (X 5),f (X 6);
      0,0,0,0,0,0,0,0,0,0,0,0,0,f (X 4),f (X 5);
      0,0,0,0,0,0,0,0,0,0,0,0,0,0,f (X 2)]
  let e : Fin 15 → Fin 15 → R := ![Pi.single 1 1,Pi.single 2 1,0,Pi.single 4 1,0,Pi.single 6 1,
    Pi.single 7 1,Pi.single 8 1,Pi.single 9 1,0,Pi.single 11 1,0,Pi.single 13 1,Pi.single 14 1,0 ]
  let d : Fin 15 → Fin 15 → R := ![0,0,0,Pi.single 1 1,0,Pi.single 2 1,Pi.single 4 1,
    Pi.single 6 1,Pi.single 7 1,0,Pi.single 8 1,0,Pi.single 9 1,Pi.single 11 1,0 ]
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
  have hval (i j : Fin 15) : f (hh (closure.xi i - closure.zeta j)) = M i j := by
    have he := congrFun (congrFun hind i) j
    change closure.xi i - closure.zeta j = _ at he
    rw [he]
    fin_cases i <;> fin_cases j <;> norm_num [M, hh, hPos, hf]
  have he (i j : Fin 15) :
      (if closure.xi i - closure.zeta j = (1 : ℤ) then 1 else 0 : R) = e j i := by
    have hi := congrFun (congrFun hind i) j
    change closure.xi i - closure.zeta j = _ at hi
    rw [hi]
    fin_cases i <;> fin_cases j <;> norm_num [e, Pi.single_apply]
  have hd (i j : Fin 15) :
      (if closure.xi i - closure.zeta j = (7 : ℤ) then 1 else 0 : R) = d j i := by
    have hi := congrFun (congrFun hind i) j
    change closure.xi i - closure.zeta j = _ at hi
    rw [hi]
    fin_cases i <;> fin_cases j <;> norm_num [d, Pi.single_apply]
  let idx : Matrix (Fin 15) (Fin 15) ℤ := fun i j =>
    closure.xi i - closure.zeta j
  have hpoly : closure.schur = (Matrix.of fun i j => hh (idx i j)).det := rfl
  rw [hpoly, hom_mixed_hh_det f idx 7 1]
  have hterm (i j : Fin 15) :
      (((Matrix.of fun r s => f (hh (idx r s))).updateCol j
        (fun r => if idx r j = ((1 : ℕ+) : ℤ) then 1 else 0)).updateCol i
        (fun r => if idx r i = ((7 : ℕ+) : ℤ) then 1 else 0)) =
      (M.updateCol j (e j)).updateCol i (d i) := by
    ext r s
    simp only [Matrix.updateCol_apply, Matrix.of_apply]
    by_cases hsi : s = i
    · simp only [ite_eq_left hsi]
      exact hd r i
    · simp only [ite_eq_right hsi]
      by_cases hsj : s = j
      · simp only [ite_eq_left hsj]
        exact he r j
      · simp only [ite_eq_right hsj]
        exact hval r s
  simp_rw [hterm]
  change (∑ j : Fin 15, ∑ i : Fin 15, if i = j then 0 else
    ((M.updateCol j (e j)).updateCol i (d i)).det) = _
  have hM : M = closureResidueMatrix (fun k => f (X k)) := rfl
  rw [hM]
  norm_num [Fin.sum_univ_succ, e, d,
    closure_mixed_term_3_0, closure_mixed_term_3_1,
    closure_mixed_term_3_5, closure_mixed_term_3_6,
    closure_mixed_term_3_7, closure_mixed_term_3_8,
    closure_mixed_term_3_10, closure_mixed_term_3_12,
    closure_mixed_term_3_13, closure_mixed_term_5_0,
    closure_mixed_term_5_1, closure_mixed_term_5_3,
    closure_mixed_term_5_6, closure_mixed_term_5_7,
    closure_mixed_term_5_8, closure_mixed_term_5_10,
    closure_mixed_term_5_12, closure_mixed_term_5_13,
    closure_mixed_term_6_0, closure_mixed_term_6_1,
    closure_mixed_term_6_3, closure_mixed_term_6_5,
    closure_mixed_term_6_7, closure_mixed_term_6_8,
    closure_mixed_term_6_10, closure_mixed_term_6_12,
    closure_mixed_term_6_13, closure_mixed_term_7_0,
    closure_mixed_term_7_1, closure_mixed_term_7_3,
    closure_mixed_term_7_5, closure_mixed_term_7_6,
    closure_mixed_term_7_8, closure_mixed_term_7_10,
    closure_mixed_term_7_12, closure_mixed_term_7_13,
    closure_mixed_term_8_0, closure_mixed_term_8_1,
    closure_mixed_term_8_3, closure_mixed_term_8_5,
    closure_mixed_term_8_6, closure_mixed_term_8_7,
    closure_mixed_term_8_10, closure_mixed_term_8_12,
    closure_mixed_term_8_13, closure_mixed_term_10_0,
    closure_mixed_term_10_1, closure_mixed_term_10_3,
    closure_mixed_term_10_5, closure_mixed_term_10_6,
    closure_mixed_term_10_7, closure_mixed_term_10_8,
    closure_mixed_term_10_12, closure_mixed_term_10_13,
    closure_mixed_term_12_0, closure_mixed_term_12_1,
    closure_mixed_term_12_3, closure_mixed_term_12_5,
    closure_mixed_term_12_6, closure_mixed_term_12_7,
    closure_mixed_term_12_8, closure_mixed_term_12_10,
    closure_mixed_term_12_13, closure_mixed_term_13_0,
    closure_mixed_term_13_1, closure_mixed_term_13_3,
    closure_mixed_term_13_5, closure_mixed_term_13_6,
    closure_mixed_term_13_7, closure_mixed_term_13_8,
    closure_mixed_term_13_10, closure_mixed_term_13_12]
  ring

end SkewCornerDescent.SquareWordProfiles
