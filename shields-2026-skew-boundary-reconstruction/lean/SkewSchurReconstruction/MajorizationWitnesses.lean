/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewSchurReconstruction.Majorization

/-!
# Limits of peel majorization

Formalizes "Majorization of the peel multisets, and its limits"
(`subsec:majorization`, `rem:higher-strata`) and its adjacent moving-cap witness.
The six-row parents have a common grid, equal row-length multisets, and first
changed row three.  Their actual cofactor defect has the stated square-weight
43 component.  The four-row parents have different grids and their actual
cofactors at shift nine have the stated expansions and incomparable minimal
peels.  Finite Laplace expansion computes the determinants.  Sorry-free.
-/

namespace SkewSchurReconstruction

open scoped BigOperators

namespace Diagram

/-- The first six-row parent of `rem:higher-strata`. -/
def higherStratumX : Diagram 6 where
  outer := ![15, 15, 14, 10, 10, 5]
  inner := ![12, 10, 6, 6, 4, 0]
  outer_antitone := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  inner_antitone := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  row_nonempty := by
    intro i
    fin_cases i <;> norm_num

/-- The second six-row parent of `rem:higher-strata`. -/
def higherStratumY : Diagram 6 where
  outer := ![15, 15, 14, 11, 8, 6]
  inner := ![12, 10, 6, 6, 4, 0]
  outer_antitone := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  inner_antitone := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  row_nonempty := by
    intro i
    fin_cases i <;> norm_num

theorem higherStratumX_connected : higherStratumX.Connected := by
  unfold Connected
  decide

theorem higherStratumY_connected : higherStratumY.Connected := by
  unfold Connected
  decide

theorem higherStratumX_capShift (j : Fin 7) :
    higherStratumX.capShift j = ![0, 3, 6, 11, 12, 15, 20] j := by
  fin_cases j <;> norm_num [capShift, top, higherStratumX]

theorem higherStratumY_capShift (j : Fin 7) :
    higherStratumY.capShift j = ![0, 3, 6, 11, 12, 15, 20] j := by
  fin_cases j <;> norm_num [capShift, top, higherStratumY]

theorem higherStratum_common_grid : higherStratumX.capShift = higherStratumY.capShift := by
  funext j
  rw [higherStratumX_capShift, higherStratumY_capShift]

theorem higherStratum_rowLengthMultiset :
    higherStratumX.rowLengthMultiset = higherStratumY.rowLengthMultiset := by
  simp only [rowLengthMultiset, Fin.univ_val_map]
  decide

/-- Row three is genuinely the first changed normalized row. -/
theorem higherStratum_first_changed :
    (∀ i : Fin 6, i.val < 3 → higherStratumX.rowParam i = higherStratumY.rowParam i) ∧
      higherStratumX.rowParam 3 = 8 ∧ higherStratumY.rowParam 3 = 7 := by
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    fin_cases i <;> simp_all [rowParam, top, higherStratumX, higherStratumY]
  · norm_num [rowParam, top, higherStratumX]
  · norm_num [rowParam, top, higherStratumY]

private theorem det_unit_first_column (M : Matrix (Fin 6) (Fin 6) CompleteRing)
    (h : ∀ i, M i 0 = if i = 0 then 1 else 0) :
    M.det = (M.submatrix Fin.succ Fin.succ).det := by
  rw [Matrix.det_succ_column_zero]
  simp [h]

private theorem det_last_row_five (M : Matrix (Fin 5) (Fin 5) CompleteRing)
    (a : CompleteRing) (h : ∀ j, M 4 j = if j = 4 then a else 0) :
    M.det = a * (M.submatrix Fin.castSucc Fin.castSucc).det := by
  have h4 : (4 : Fin 5).succAbove = (Fin.castSucc : Fin 4 → Fin 5) :=
    Fin.succAbove_last
  rw [Matrix.det_succ_row M 4]
  norm_num [h, h4]

private theorem det_four_blocks (a b c d e f g h u v x y : CompleteRing) :
    (Matrix.of ![![a, b, u, v], ![c, d, x, y], ![0, 0, e, f], ![0, 0, g, h]]).det =
      (a * d - b * c) * (e * h - f * g) := by
  let N : Matrix (Fin 4) (Fin 4) CompleteRing :=
    Matrix.of ![![a, b, u, v], ![c, d, x, y], ![0, 0, e, f], ![0, 0, g, h]]
  have hb : N.submatrix (finSumFinEquiv : Fin 2 ⊕ Fin 2 ≃ Fin 4) finSumFinEquiv =
      Matrix.fromBlocks (Matrix.of ![![a, b], ![c, d]])
        (Matrix.of ![![u, v], ![x, y]]) 0 (Matrix.of ![![e, f], ![g, h]]) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      fin_cases i <;> fin_cases j <;> rfl
  change N.det = _
  rw [← Matrix.det_submatrix_equiv_self
    (finSumFinEquiv : Fin 2 ⊕ Fin 2 ≃ Fin 4) N, hb,
    Matrix.det_fromBlocks_zero₂₁, Matrix.det_fin_two, Matrix.det_fin_two]
  rfl

set_option maxRecDepth 4096 in
/-- Exact expansion of the actual signed maximal determinant, not its initial form. -/
theorem higherStratumX_cofactor_six :
    higherStratumX.cofactor 6 =
      (complete 2 * complete 3 - complete 5) *
        (complete 3 ^ 2 - complete 2 * complete 4) := by
  let M := higherStratumX.capMatrix.submatrix id (6 : Fin 7).succAbove
  have hfirst : ∀ i, M i 0 = if i = 0 then 1 else 0 := by
    intro i
    fin_cases i <;> norm_num [M, capMatrix, capShift, rowParam, top,
      higherStratumX, Matrix.submatrix_apply, Fin.succAbove, complete]
  have hlast : ∀ j, (M.submatrix Fin.succ Fin.succ) 4 j =
      if j = 4 then 1 else 0 := by
    intro j
    fin_cases j <;> norm_num [M, capMatrix, capShift, rowParam, top,
      higherStratumX, Matrix.submatrix_apply, Fin.succAbove, complete]
  change (-1 : CompleteRing) ^ 6 * M.det = _
  rw [show (-1 : CompleteRing) ^ 6 = 1 by norm_num, one_mul,
    det_unit_first_column M hfirst,
    det_last_row_five (M.submatrix Fin.succ Fin.succ) 1 hlast, one_mul]
  have hm : (M.submatrix Fin.succ Fin.succ).submatrix Fin.castSucc Fin.castSucc =
      Matrix.of ![![complete 2, complete 5, complete 10, complete 11],
        ![1, complete 3, complete 8, complete 9],
        ![0, 0, complete 3, complete 4], ![0, 0, complete 2, complete 3]] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [M, capMatrix, capShift, rowParam, top, higherStratumX,
        Matrix.submatrix_apply, Matrix.of_apply, Fin.succAbove, complete]
  rw [hm, det_four_blocks]
  ring

set_option maxRecDepth 4096 in
/-- Exact expansion for the other six-row parent. -/
theorem higherStratumY_cofactor_six :
    higherStratumY.cofactor 6 =
      complete 1 * (complete 2 * complete 3 - complete 5) *
        (complete 4 * complete 1 - complete 5) := by
  let M := higherStratumY.capMatrix.submatrix id (6 : Fin 7).succAbove
  have hfirst : ∀ i, M i 0 = if i = 0 then 1 else 0 := by
    intro i
    fin_cases i <;> norm_num [M, capMatrix, capShift, rowParam, top,
      higherStratumY, Matrix.submatrix_apply, Fin.succAbove, complete]
  have hlast : ∀ j, (M.submatrix Fin.succ Fin.succ) 4 j =
      if j = 4 then complete 1 else 0 := by
    intro j
    fin_cases j <;> norm_num [M, capMatrix, capShift, rowParam, top,
      higherStratumY, Matrix.submatrix_apply, Fin.succAbove, complete]
  change (-1 : CompleteRing) ^ 6 * M.det = _
  rw [show (-1 : CompleteRing) ^ 6 = 1 by norm_num, one_mul,
    det_unit_first_column M hfirst,
    det_last_row_five (M.submatrix Fin.succ Fin.succ) (complete 1) hlast]
  have hm : (M.submatrix Fin.succ Fin.succ).submatrix Fin.castSucc Fin.castSucc =
      Matrix.of ![![complete 2, complete 5, complete 10, complete 11],
        ![1, complete 3, complete 8, complete 9],
        ![0, 0, complete 4, complete 5], ![0, 0, 1, complete 1]] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [M, capMatrix, capShift, rowParam, top, higherStratumY,
        Matrix.submatrix_apply, Matrix.of_apply, Fin.succAbove, complete]
  rw [hm, det_four_blocks]
  ring

/-- Every term is obtained from the actual cofactor difference. -/
theorem higherStratum_defect_six :
    cofactorDefect higherStratumX higherStratumY 6 =
      complete 2 * complete 3 ^ 3 -
      complete 2 ^ 2 * complete 3 * complete 4 -
      complete 1 ^ 2 * complete 2 * complete 3 * complete 4 +
      complete 1 * complete 2 * complete 3 * complete 5 -
      complete 3 ^ 2 * complete 5 +
      complete 2 * complete 4 * complete 5 +
      complete 1 ^ 2 * complete 4 * complete 5 -
      complete 1 * complete 5 ^ 2 := by
  rw [cofactorDefect, higherStratumX_cofactor_six, higherStratumY_cofactor_six]
  ring

/-- The weight 43 residual stratum of `rem:higher-strata`. -/
theorem higherStratum_weight_forty_three :
    MvPolynomial.weightedHomogeneousComponent squareWeight.generatorWeight 43
        (cofactorDefect higherStratumX higherStratumY 6) =
      complete 1 ^ 2 * complete 4 * complete 5 - complete 3 ^ 2 * complete 5 := by
  have h1 : MvPolynomial.IsWeightedHomogeneous squareWeight.generatorWeight (complete 1) 1 := by
    convert complete_convex_homogeneous squareWeight 1 (by norm_num) using 1
    norm_num [squareWeight]
  have h2 : MvPolynomial.IsWeightedHomogeneous squareWeight.generatorWeight (complete 2) 4 := by
    convert complete_convex_homogeneous squareWeight 2 (by norm_num) using 1
    norm_num [squareWeight]
  have h3 : MvPolynomial.IsWeightedHomogeneous squareWeight.generatorWeight (complete 3) 9 := by
    convert complete_convex_homogeneous squareWeight 3 (by norm_num) using 1
    norm_num [squareWeight]
  have h4 : MvPolynomial.IsWeightedHomogeneous squareWeight.generatorWeight (complete 4) 16 := by
    convert complete_convex_homogeneous squareWeight 4 (by norm_num) using 1
    norm_num [squareWeight]
  have h5 : MvPolynomial.IsWeightedHomogeneous squareWeight.generatorWeight (complete 5) 25 := by
    convert complete_convex_homogeneous squareWeight 5 (by norm_num) using 1
    norm_num [squareWeight]
  have ha : MvPolynomial.IsWeightedHomogeneous squareWeight.generatorWeight
      (complete 2 * complete 3 ^ 3) 31 := by
    convert h2.mul (h3.pow 3) using 1
    norm_num
  have hb : MvPolynomial.IsWeightedHomogeneous squareWeight.generatorWeight
      (complete 2 ^ 2 * complete 3 * complete 4) 33 := by
    convert ((h2.pow 2).mul h3).mul h4 using 1
    norm_num
  have hc : MvPolynomial.IsWeightedHomogeneous squareWeight.generatorWeight
      (complete 1 ^ 2 * complete 2 * complete 3 * complete 4) 31 := by
    convert (((h1.pow 2).mul h2).mul h3).mul h4 using 1
    norm_num
  have hd : MvPolynomial.IsWeightedHomogeneous squareWeight.generatorWeight
      (complete 1 * complete 2 * complete 3 * complete 5) 39 := by
    convert ((h1.mul h2).mul h3).mul h5 using 1
    norm_num
  have he : MvPolynomial.IsWeightedHomogeneous squareWeight.generatorWeight
      (complete 3 ^ 2 * complete 5) 43 := by
    convert (h3.pow 2).mul h5 using 1
    norm_num
  have hf : MvPolynomial.IsWeightedHomogeneous squareWeight.generatorWeight
      (complete 2 * complete 4 * complete 5) 45 := by
    convert (h2.mul h4).mul h5 using 1
    norm_num
  have hg : MvPolynomial.IsWeightedHomogeneous squareWeight.generatorWeight
      (complete 1 ^ 2 * complete 4 * complete 5) 43 := by
    convert ((h1.pow 2).mul h4).mul h5 using 1
    norm_num
  have hh : MvPolynomial.IsWeightedHomogeneous squareWeight.generatorWeight
      (complete 1 * complete 5 ^ 2) 51 := by
    convert h1.mul (h5.pow 2) using 1
    norm_num
  rw [higherStratum_defect_six]
  simp only [map_add, map_sub]
  rw [ha.weightedHomogeneousComponent_ne 43 (by norm_num),
    hb.weightedHomogeneousComponent_ne 43 (by norm_num),
    hc.weightedHomogeneousComponent_ne 43 (by norm_num),
    hd.weightedHomogeneousComponent_ne 43 (by norm_num),
    he.weightedHomogeneousComponent_same,
    hf.weightedHomogeneousComponent_ne 43 (by norm_num),
    hg.weightedHomogeneousComponent_same,
    hh.weightedHomogeneousComponent_ne 43 (by norm_num)]
  ring

/-- The first moving-cap parent, with the outer boundary exactly as in the manuscript. -/
def movingCapX : Diagram 4 where
  outer := ![6, 6, 4, 1]
  inner := ![2, 0, 0, 0]
  outer_antitone := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  inner_antitone := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  row_nonempty := by
    intro i
    fin_cases i <;> norm_num

/-- The second moving-cap parent. -/
def movingCapY : Diagram 4 where
  outer := ![8, 4, 4, 1]
  inner := ![2, 0, 0, 0]
  outer_antitone := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  inner_antitone := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  row_nonempty := by
    intro i
    fin_cases i <;> norm_num

theorem movingCapX_connected : movingCapX.Connected := by
  unfold Connected
  decide

theorem movingCapY_connected : movingCapY.Connected := by
  unfold Connected
  decide

theorem movingCap_cell_counts :
    (∑ i, movingCapX.rowLength i) = 15 ∧ (∑ i, movingCapY.rowLength i) = 15 := by
  norm_num [rowLength, movingCapX, movingCapY, Fin.sum_univ_succ]

theorem movingCapX_capShift (j : Fin 5) :
    movingCapX.capShift j = ![0, 4, 7, 8, 9] j := by
  fin_cases j <;> norm_num [capShift, top, movingCapX]

theorem movingCapY_capShift (j : Fin 5) :
    movingCapY.capShift j = ![0, 6, 9, 10, 11] j := by
  fin_cases j <;> norm_num [capShift, top, movingCapY]

theorem movingCap_grids_differ : movingCapX.capShift ≠ movingCapY.capShift := by
  intro h
  have h1 := congrFun h 1
  norm_num [movingCapX_capShift, movingCapY_capShift] at h1

/-- Shift nine deletes column four in the first parent and column two in the second. -/
theorem movingCap_shift_nine : movingCapX.capShift 4 = 9 ∧ movingCapY.capShift 2 = 9 := by
  norm_num [movingCapX_capShift, movingCapY_capShift]

set_option maxRecDepth 4096 in
/-- The manuscript's actual first cofactor at shift nine. -/
theorem movingCapX_cofactor_nine :
    movingCapX.cofactor 4 = complete 3 ^ 2 - complete 6 := by
  norm_num [cofactor, signedMaximalCofactor, capMatrix, capShift, rowParam, top,
    movingCapX, Matrix.det_succ_row_zero, Fin.sum_univ_succ,
    Matrix.submatrix_apply, Matrix.of_apply, Fin.succAbove, complete]
  ring

set_option maxRecDepth 4096 in
/-- The manuscript's actual second cofactor at the same shift nine. -/
theorem movingCapY_cofactor_nine :
    movingCapY.cofactor 2 =
      complete 4 * complete 1 ^ 2 - 2 * complete 5 * complete 1 + complete 6 := by
  norm_num [cofactor, signedMaximalCofactor, capMatrix, capShift, rowParam, top,
    movingCapY, Matrix.det_succ_row_zero, Fin.sum_univ_succ,
    Matrix.submatrix_apply, Matrix.of_apply, Fin.succAbove, complete]
  ring

theorem movingCapX_peel_nine :
    movingCapX.peelMultiset 4 = ([0, 3, 3, 0] : List ℤ) := by
  simp only [peelMultiset, Fin.univ_val_map]
  decide

theorem movingCapY_peel_nine :
    movingCapY.peelMultiset 2 = ([0, 1, 4, 1] : List ℤ) := by
  simp only [peelMultiset, Fin.univ_val_map]
  decide

/-- The common zero-index factor is retained by the actual peels and can be removed. -/
theorem movingCap_padded_peels :
    movingCapX.peelMultiset 4 = ({0} : Multiset ℤ) + ([3, 3, 0] : List ℤ) ∧
      movingCapY.peelMultiset 2 = ({0} : Multiset ℤ) + ([4, 1, 1] : List ℤ) := by
  rw [movingCapX_peel_nine, movingCapY_peel_nine]
  decide

/-- These are minimal monomials of the actual determinants for every admissible weight. -/
theorem movingCap_initialForms (w : ConvexWeight) :
    initialForm w.generatorWeight (movingCapX.cofactor 4) = complete 3 ^ 2 ∧
      initialForm w.generatorWeight (movingCapY.cofactor 2) = complete 4 * complete 1 ^ 2 := by
  constructor
  · rw [cofactor_initialForm w movingCapX movingCapX_connected]
    norm_num [peelIndex, capShift, rowParam, top, movingCapX,
      Fin.prod_univ_succ, Fin.succAbove, complete]
    ring
  · rw [cofactor_initialForm w movingCapY movingCapY_connected]
    norm_num [peelIndex, capShift, rowParam, top, movingCapY,
      Fin.prod_univ_succ, Fin.succAbove, complete]
    ring

theorem movingCap_least_square_weights :
    leastWeight squareWeight.generatorWeight (movingCapX.cofactor 4) = 18 ∧
      leastWeight squareWeight.generatorWeight (movingCapY.cofactor 2) = 18 := by
  constructor
  · rw [cofactor_leastWeight squareWeight movingCapX movingCapX_connected]
    norm_num [peelIndex, capShift, rowParam, top, movingCapX,
      Fin.sum_univ_succ, Fin.succAbove, squareWeight]
  · rw [cofactor_leastWeight squareWeight movingCapY movingCapY_connected]
    norm_num [peelIndex, capShift, rowParam, top, movingCapY,
      Fin.sum_univ_succ, Fin.succAbove, squareWeight]

end Diagram

/-- The residual monomials have equal ordinary degree, even after zero padding. -/
theorem higherStratum_padded_degrees :
    (([5, 4, 1, 1] : List ℤ) : Multiset ℤ).sum = 11 ∧
      (([5, 3, 3, 0] : List ℤ) : Multiset ℤ).sum = 11 := by
  norm_num

/-- Their square weights coincide with the projected stratum. -/
theorem higherStratum_padded_square_weights :
    (([5, 4, 1, 1] : List ℤ).map (fun k => k ^ 2)).sum = 43 ∧
      (([5, 3, 3, 0] : List ℤ).map (fun k => k ^ 2)).sum = 43 := by
  norm_num

/-- Prefix three rules out one direction; prefix two rules out the other. -/
theorem higherStratum_padded_incomparable :
    ¬ Dominates ([5, 4, 1, 1] : List ℤ) ([5, 3, 3, 0] : List ℤ) ∧
      ¬ Dominates ([5, 3, 3, 0] : List ℤ) ([5, 4, 1, 1] : List ℤ) := by
  constructor
  · intro h
    exact (by
      unfold sortedPrefixSum
      simp only [Multiset.coe_sort, List.mergeSort_eq_insertionSort]
      decide :
      ¬ sortedPrefixSum ([5, 3, 3, 0] : List ℤ) 3 ≤
      sortedPrefixSum ([5, 4, 1, 1] : List ℤ) 3) (h.2.2 3)
  · intro h
    exact (by
      unfold sortedPrefixSum
      simp only [Multiset.coe_sort, List.mergeSort_eq_insertionSort]
      decide :
      ¬ sortedPrefixSum ([5, 4, 1, 1] : List ℤ) 2 ≤
      sortedPrefixSum ([5, 3, 3, 0] : List ℤ) 2) (h.2.2 2)

/-- The moving-cap minimal peels have equal degree six and square weight eighteen. -/
theorem movingCap_padded_degrees_and_weights :
    ([3, 3, 0] : List ℤ).sum = 6 ∧ ([4, 1, 1] : List ℤ).sum = 6 ∧
      (([3, 3, 0] : List ℤ).map (fun k => k ^ 2)).sum = 18 ∧
      (([4, 1, 1] : List ℤ).map (fun k => k ^ 2)).sum = 18 := by
  norm_num

/-- Equal degree and square weight do not imply dominance. -/
theorem movingCap_padded_incomparable :
    ¬ Dominates ([3, 3, 0] : List ℤ) ([4, 1, 1] : List ℤ) ∧
      ¬ Dominates ([4, 1, 1] : List ℤ) ([3, 3, 0] : List ℤ) := by
  constructor
  · intro h
    exact (by
      unfold sortedPrefixSum
      simp only [Multiset.coe_sort, List.mergeSort_eq_insertionSort]
      decide :
      ¬ sortedPrefixSum ([4, 1, 1] : List ℤ) 1 ≤
      sortedPrefixSum ([3, 3, 0] : List ℤ) 1) (h.2.2 1)
  · intro h
    exact (by
      unfold sortedPrefixSum
      simp only [Multiset.coe_sort, List.mergeSort_eq_insertionSort]
      decide :
      ¬ sortedPrefixSum ([3, 3, 0] : List ℤ) 2 ≤
      sortedPrefixSum ([4, 1, 1] : List ℤ) 2) (h.2.2 2)

/-- Incomparability holds for the actual four-entry peels, including their common zero. -/
theorem movingCap_actual_peels_incomparable :
    ¬ Dominates (Diagram.movingCapX.peelMultiset 4) (Diagram.movingCapY.peelMultiset 2) ∧
      ¬ Dominates (Diagram.movingCapY.peelMultiset 2) (Diagram.movingCapX.peelMultiset 4) := by
  rw [Diagram.movingCapX_peel_nine, Diagram.movingCapY_peel_nine]
  constructor
  · intro h
    exact (by
      unfold sortedPrefixSum
      simp only [Multiset.coe_sort, List.mergeSort_eq_insertionSort]
      decide :
      ¬ sortedPrefixSum ([0, 1, 4, 1] : List ℤ) 1 ≤
      sortedPrefixSum ([0, 3, 3, 0] : List ℤ) 1) (h.2.2 1)
  · intro h
    exact (by
      unfold sortedPrefixSum
      simp only [Multiset.coe_sort, List.mergeSort_eq_insertionSort]
      decide :
      ¬ sortedPrefixSum ([0, 3, 3, 0] : List ℤ) 2 ≤
      sortedPrefixSum ([0, 1, 4, 1] : List ℤ) 2) (h.2.2 2)

end SkewSchurReconstruction
