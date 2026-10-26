/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewSchurReconstruction.StaircaseBoundary

/-!
# The smallest endpoint-three residual witness

Formalizes the literal word `(3,2,3,3)` and its actual reversal in
"Reversal pairs on the locus" (`subsec:locus-family`, `rem:staircase-boundary`).
Actual four-row capped determinants produce the closed defect coordinates;
their square-weight initial forms then identify the residual monomial.
Sorry-free.
-/

namespace SkewSchurReconstruction

open scoped BigOperators

/-- The literal nonpalindromic endpoint-three word. -/
def endpointThreeWitnessWord : Fin 4 → ℕ := ![3, 2, 3, 3]

private theorem endpointThreeWitnessWord_binary :
    ∀ i, endpointThreeWitnessWord i = 2 ∨ endpointThreeWitnessWord i = 3 := by
  intro i
  fin_cases i <;> norm_num [endpointThreeWitnessWord]

/-- The actual diagram with outer `(6,4,4,3)` and inner `(3,2,1,0)`. -/
def endpointThreeWitnessLeft : Diagram 4 :=
  staircaseDiagram endpointThreeWitnessWord endpointThreeWitnessWord_binary

/-- Its actual row-word reversal, with outer `(6,5,3,3)` on the same inner boundary. -/
def endpointThreeWitnessRight : Diagram 4 :=
  staircaseDiagram (reversedWord endpointThreeWitnessWord)
    (reversedWord_binary _ endpointThreeWitnessWord_binary)

private theorem witness_first : endpointThreeWitnessWord (0 : Fin 4) = 3 := rfl

private theorem witness_reverse_first : reversedWord endpointThreeWitnessWord (0 : Fin 4) = 3 := rfl

private noncomputable def witnessBorder : Fin 4 → CompleteRing :=
  ![complete 3, complete 5, complete 7, complete 9]

private noncomputable def witnessLowerLeft : Matrix (Fin 3) (Fin 4) CompleteRing :=
  ![![1, complete 2, complete 4, complete 6],
    ![0, complete 1, complete 3, complete 5],
    ![0, 0, complete 1, complete 3]]

private noncomputable def witnessLowerRight : Matrix (Fin 3) (Fin 4) CompleteRing :=
  ![![complete 1, complete 3, complete 5, complete 7],
    ![0, 1, complete 2, complete 4],
    ![0, 0, complete 1, complete 3]]

private theorem witness_grid_left : endpointThreeWitnessLeft.capShift = ![0, 3, 5, 7, 9] := by
  funext j
  have h := staircase_capShift_three endpointThreeWitnessWord endpointThreeWitnessWord_binary
    (by norm_num) witness_first j
  change endpointThreeWitnessLeft.capShift j = _ at h
  fin_cases j <;> norm_num at h ⊢ <;> exact h

private theorem witness_grid_right : endpointThreeWitnessRight.capShift = ![0, 3, 5, 7, 9] := by
  funext j
  have h := staircase_capShift_three (reversedWord endpointThreeWitnessWord)
    (reversedWord_binary _ endpointThreeWitnessWord_binary) (by norm_num) witness_reverse_first j
  change endpointThreeWitnessRight.capShift j = _ at h
  fin_cases j <;> norm_num at h ⊢ <;> exact h

private theorem witness_cap_left : endpointThreeWitnessLeft.capMatrix =
    cofactorExtensionMatrix witnessBorder witnessLowerLeft := by
  apply Matrix.ext
  intro i j
  change complete (endpointThreeWitnessLeft.capShift j - endpointThreeWitnessLeft.rowParam i) = _
  rw [congrFun witness_grid_left j]
  have hA := staircase_rowParam_three endpointThreeWitnessWord endpointThreeWitnessWord_binary
    (by norm_num) witness_first i
  change endpointThreeWitnessLeft.rowParam i = _ at hA
  rw [hA]
  fin_cases i <;> fin_cases j <;>
    norm_num [endpointThreeWitnessWord, cofactorExtensionMatrix, witnessBorder, witnessLowerLeft,
      complete_zero, complete_of_neg]

private theorem witness_cap_right : endpointThreeWitnessRight.capMatrix =
    cofactorExtensionMatrix witnessBorder witnessLowerRight := by
  apply Matrix.ext
  intro i j
  change complete (endpointThreeWitnessRight.capShift j - endpointThreeWitnessRight.rowParam i) = _
  rw [congrFun witness_grid_right j]
  have hA := staircase_rowParam_three (reversedWord endpointThreeWitnessWord)
    (reversedWord_binary _ endpointThreeWitnessWord_binary) (by norm_num) witness_reverse_first i
  change endpointThreeWitnessRight.rowParam i = _ at hA
  rw [hA]
  fin_cases i <;> fin_cases j <;>
    norm_num [endpointThreeWitnessWord, reversedWord, cofactorExtensionMatrix, witnessBorder,
      witnessLowerRight, complete_zero, complete_of_neg]

private noncomputable def witnessG1 : CompleteRing :=
  complete 1 * complete 2 * complete 5 - complete 1 ^ 2 * complete 6 -
    complete 3 * complete 5 + complete 1 * complete 7

private noncomputable def witnessG2 : CompleteRing :=
  complete 3 ^ 2 - complete 1 * complete 5 - complete 1 * complete 2 * complete 3 +
    complete 1 ^ 2 * complete 4

private noncomputable def witnessG0 : CompleteRing :=
  complete 1 ^ 2 * complete 3 * complete 6 - complete 1 * complete 3 * complete 7 +
    complete 1 * complete 5 ^ 2 - complete 1 ^ 2 * complete 4 * complete 5

private noncomputable def witnessMinorLeft : Fin 4 → Matrix (Fin 3) (Fin 3) CompleteRing := ![
  Matrix.of ![![complete 2, complete 4, complete 6],
    ![complete 1, complete 3, complete 5], ![0, complete 1, complete 3]],
  Matrix.of ![![1, complete 4, complete 6],
    ![0, complete 3, complete 5], ![0, complete 1, complete 3]],
  Matrix.of ![![1, complete 2, complete 6],
    ![0, complete 1, complete 5], ![0, 0, complete 3]],
  Matrix.of ![![1, complete 2, complete 4],
    ![0, complete 1, complete 3], ![0, 0, complete 1]]]

private noncomputable def witnessMinorRight : Fin 4 → Matrix (Fin 3) (Fin 3) CompleteRing := ![
  Matrix.of ![![complete 3, complete 5, complete 7],
    ![1, complete 2, complete 4], ![0, complete 1, complete 3]],
  Matrix.of ![![complete 1, complete 5, complete 7],
    ![0, complete 2, complete 4], ![0, complete 1, complete 3]],
  Matrix.of ![![complete 1, complete 3, complete 7],
    ![0, 1, complete 4], ![0, 0, complete 3]],
  Matrix.of ![![complete 1, complete 3, complete 5],
    ![0, 1, complete 2], ![0, 0, complete 1]]]

private theorem witness_minor_left (j : Fin 4) :
    witnessLowerLeft.submatrix id j.succAbove = witnessMinorLeft j := by
  apply Matrix.ext
  intro i k
  fin_cases j <;> fin_cases i <;> fin_cases k <;>
    norm_num [witnessLowerLeft, witnessMinorLeft, Matrix.submatrix, Fin.succAbove]

private theorem witness_minor_right (j : Fin 4) :
    witnessLowerRight.submatrix id j.succAbove = witnessMinorRight j := by
  apply Matrix.ext
  intro i k
  fin_cases j <;> fin_cases i <;> fin_cases k <;>
    norm_num [witnessLowerRight, witnessMinorRight, Matrix.submatrix, Fin.succAbove]

/-- Positive-column differences are derived from the signed three-row complementary minors. -/
private theorem witness_positive_cofactors (j : Fin 4) :
    Diagram.cofactorDefect endpointThreeWitnessLeft endpointThreeWitnessRight j.succ =
      ![witnessG1, witnessG2, 0, 0] j := by
  unfold Diagram.cofactorDefect Diagram.cofactor
  rw [witness_cap_left, witness_cap_right, signedMaximalCofactor_extension_succ,
    signedMaximalCofactor_extension_succ]
  unfold signedMaximalCofactor
  rw [witness_minor_left, witness_minor_right]
  fin_cases j <;>
    simp [witnessMinorLeft, witnessMinorRight, Matrix.det_fin_three, witnessG1, witnessG2] <;> ring

private theorem witness_common_grid :
    ∀ j, endpointThreeWitnessLeft.capShift j = endpointThreeWitnessRight.capShift j := by
  intro j
  rw [congrFun witness_grid_left j, congrFun witness_grid_right j]

/-- The zeroth difference is forced by the actual top-row kernel relation. -/
private theorem witness_zero_cofactor :
    Diagram.cofactorDefect endpointThreeWitnessLeft endpointThreeWitnessRight 0 = witnessG0 := by
  have h := gridDefect_response_zero endpointThreeWitnessLeft endpointThreeWitnessRight
    (by norm_num) (by norm_num)
  rw [Diagram.gridDefect_response_eq_sum _ _ witness_common_grid] at h
  simp only [zero_add] at h
  rw [Fin.sum_univ_succ] at h
  simp only [witness_positive_cofactors] at h
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_one] at h
  simp only [witness_grid_left, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Diagram.capShift_zero, complete_zero, mul_one, zero_mul, add_zero] at h
  dsimp [witnessG0, witnessG1, witnessG2] at h ⊢
  linear_combination h

/-- The complete vector difference is that of the literal diagrams, not a prescribed toy vector. -/
theorem endpointThreeWitness_cofactor_difference :
    Diagram.cofactorDefect endpointThreeWitnessLeft endpointThreeWitnessRight =
      ![witnessG0, witnessG1, witnessG2, 0, 0] := by
  funext j
  cases j using Fin.cases with
  | zero => exact witness_zero_cofactor
  | succ j => exact witness_positive_cofactors j

private theorem complete_list_product_data (l : List ℕ) :
    (l.map (fun k : ℕ => complete (k : ℤ))).prod ≠ 0 ∧
      MvPolynomial.IsWeightedHomogeneous squareWeight.generatorWeight
        (l.map (fun k : ℕ => complete (k : ℤ))).prod
        (l.map (fun k : ℕ => (k : ℝ) ^ 2)).sum := by
  induction l with
  | nil =>
    simp only [List.map_nil, List.prod_nil, List.sum_nil]
    exact ⟨one_ne_zero, MvPolynomial.isWeightedHomogeneous_one ℤ _⟩
  | cons k l ih =>
    simp only [List.map_cons, List.prod_cons, List.sum_cons]
    have hk := complete_convex_homogeneous squareWeight (k : ℤ) (by omega)
    rw [Int.toNat_natCast] at hk
    change MvPolynomial.IsWeightedHomogeneous squareWeight.generatorWeight
      (complete (k : ℤ)) ((k : ℝ) ^ 2) at hk
    exact ⟨mul_ne_zero (complete_ne_zero_of_nonneg _ (by omega)) ih.1, hk.mul ih.2⟩

private theorem initialForm_negation (p : CompleteRing) :
    initialForm squareWeight.generatorWeight (-p) =
      -initialForm squareWeight.generatorWeight p := by
  by_cases hp : p = 0
  · simp [hp]
  · have hn := neg_ne_zero.mpr hp
    have hc : (leastWeight squareWeight.generatorWeight (-p) : WithTop ℝ) =
        (leastWeight squareWeight.generatorWeight p : WithTop ℝ) := by
      rw [← monomialValuation_eq_coe hn, ← monomialValuation_eq_coe hp, monomialValuation_neg]
    have hw := WithTop.coe_injective hc
    unfold initialForm
    rw [hw]
    exact map_neg _ p

private theorem four_terms_initial (f : Fin 4 → CompleteRing) (d : Fin 4 → ℝ)
    (hf : ∀ j, f j ≠ 0 ∧
      MvPolynomial.IsWeightedHomogeneous squareWeight.generatorWeight (f j) (d j))
    (hd : ∀ j, j ≠ 0 → d 0 < d j) :
    initialForm squareWeight.generatorWeight (∑ j, f j) = f 0 ∧
      monomialValuation squareWeight.generatorWeight (∑ j, f j) = (d 0 : WithTop ℝ) := by
  have hm : ∀ j ∈ (Finset.univ : Finset (Fin 4)), j ≠ 0 →
      monomialValuation squareWeight.generatorWeight (f 0) <
        monomialValuation squareWeight.generatorWeight (f j) := by
    intro j _ hj
    rw [monomialValuation_eq_of_homogeneous (hf 0).1 (hf 0).2,
      monomialValuation_eq_of_homogeneous (hf j).1 (hf j).2]
    exact WithTop.coe_lt_coe.mpr (hd j hj)
  have hn := sum_ne_zero_of_unique_min Finset.univ f (Finset.mem_univ 0) (hf 0).1 hm
  have hh := initialForm_sum_unique Finset.univ f (Finset.mem_univ 0) (hf 0).1 hm
  refine ⟨hh.1.trans (initialForm_eq_of_homogeneous (hf 0).1 (hf 0).2), ?_⟩
  rw [monomialValuation_eq_coe hn, hh.2,
    leastWeight_eq_of_homogeneous (hf 0).1 (hf 0).2]

private theorem negative_list_product_data (l : List ℕ) :
    -(l.map (fun k : ℕ => complete (k : ℤ))).prod ≠ 0 ∧
      MvPolynomial.IsWeightedHomogeneous squareWeight.generatorWeight
        (-(l.map (fun k : ℕ => complete (k : ℤ))).prod)
        (l.map (fun k : ℕ => (k : ℝ) ^ 2)).sum :=
  ⟨neg_ne_zero.mpr (complete_list_product_data l).1,
    (complete_list_product_data l).2.neg⟩

private theorem witnessG0_initial :
    initialForm squareWeight.generatorWeight witnessG0 =
      -(complete 1 ^ 2 * complete 4 * complete 5) ∧
    monomialValuation squareWeight.generatorWeight witnessG0 = ((43 : ℝ) : WithTop ℝ) := by
  let F : Fin 4 → CompleteRing := ![
    -([1, 1, 4, 5].map (fun k : ℕ => complete (k : ℤ))).prod,
    ([1, 1, 3, 6].map (fun k : ℕ => complete (k : ℤ))).prod,
    -([1, 3, 7].map (fun k : ℕ => complete (k : ℤ))).prod,
    ([1, 5, 5].map (fun k : ℕ => complete (k : ℤ))).prod]
  let D : Fin 4 → ℝ := ![43, 47, 59, 51]
  have hdata : ∀ j, F j ≠ 0 ∧
      MvPolynomial.IsWeightedHomogeneous squareWeight.generatorWeight (F j) (D j) := by
    intro j
    fin_cases j
    · have h := negative_list_product_data [1, 1, 4, 5]
      norm_num only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        Nat.cast_ofNat] at h
      exact h
    · have h := complete_list_product_data [1, 1, 3, 6]
      norm_num only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        Nat.cast_ofNat] at h
      exact h
    · have h := negative_list_product_data [1, 3, 7]
      norm_num only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        Nat.cast_ofNat] at h
      exact h
    · have h := complete_list_product_data [1, 5, 5]
      norm_num only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        Nat.cast_ofNat] at h
      exact h
  have hD : ∀ j, j ≠ 0 → D 0 < D j := by
    intro j hj
    fin_cases j <;> norm_num [D] at *
  have he : (∑ j, F j) = witnessG0 := by
    simp only [F, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero,
      Matrix.cons_val_succ, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      Nat.cast_ofNat, add_zero, witnessG0]
    ring
  have h := four_terms_initial F D hdata hD
  rw [he] at h
  refine ⟨?_, h.2⟩
  rw [h.1]
  simp only [F, Matrix.cons_val_zero, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, Nat.cast_ofNat]
  ring

private theorem witnessG1_valuation :
    monomialValuation squareWeight.generatorWeight witnessG1 = ((30 : ℝ) : WithTop ℝ) := by
  let F : Fin 4 → CompleteRing := ![
    ([1, 2, 5].map (fun k : ℕ => complete (k : ℤ))).prod,
    -([1, 1, 6].map (fun k : ℕ => complete (k : ℤ))).prod,
    -([3, 5].map (fun k : ℕ => complete (k : ℤ))).prod,
    ([1, 7].map (fun k : ℕ => complete (k : ℤ))).prod]
  let D : Fin 4 → ℝ := ![30, 38, 34, 50]
  have hdata : ∀ j, F j ≠ 0 ∧
      MvPolynomial.IsWeightedHomogeneous squareWeight.generatorWeight (F j) (D j) := by
    intro j
    fin_cases j
    · have h := complete_list_product_data [1, 2, 5]
      norm_num only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        Nat.cast_ofNat] at h
      exact h
    · have h := negative_list_product_data [1, 1, 6]
      norm_num only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        Nat.cast_ofNat] at h
      exact h
    · have h := negative_list_product_data [3, 5]
      norm_num only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        Nat.cast_ofNat] at h
      exact h
    · have h := complete_list_product_data [1, 7]
      norm_num only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        Nat.cast_ofNat] at h
      exact h
  have hD : ∀ j, j ≠ 0 → D 0 < D j := by intro j hj; fin_cases j <;> norm_num [D] at *
  have he : (∑ j, F j) = witnessG1 := by
    simp only [F, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero,
      Matrix.cons_val_succ, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      Nat.cast_ofNat, add_zero, witnessG1]
    ring
  have h := (four_terms_initial F D hdata hD).2
  rwa [he] at h

private theorem witnessG2_valuation :
    monomialValuation squareWeight.generatorWeight witnessG2 = ((14 : ℝ) : WithTop ℝ) := by
  let F : Fin 4 → CompleteRing := ![
    -([1, 2, 3].map (fun k : ℕ => complete (k : ℤ))).prod,
    ([3, 3].map (fun k : ℕ => complete (k : ℤ))).prod,
    -([1, 5].map (fun k : ℕ => complete (k : ℤ))).prod,
    ([1, 1, 4].map (fun k : ℕ => complete (k : ℤ))).prod]
  let D : Fin 4 → ℝ := ![14, 18, 26, 18]
  have hdata : ∀ j, F j ≠ 0 ∧
      MvPolynomial.IsWeightedHomogeneous squareWeight.generatorWeight (F j) (D j) := by
    intro j
    fin_cases j
    · have h := negative_list_product_data [1, 2, 3]
      norm_num only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        Nat.cast_ofNat] at h
      exact h
    · have h := complete_list_product_data [3, 3]
      norm_num only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        Nat.cast_ofNat] at h
      exact h
    · have h := negative_list_product_data [1, 5]
      norm_num only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        Nat.cast_ofNat] at h
      exact h
    · have h := complete_list_product_data [1, 1, 4]
      norm_num only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        Nat.cast_ofNat] at h
      exact h
  have hD : ∀ j, j ≠ 0 → D 0 < D j := by intro j hj; fin_cases j <;> norm_num [D] at *
  have he : (∑ j, F j) = witnessG2 := by
    simp only [F, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero,
      Matrix.cons_val_succ, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      Nat.cast_ofNat, add_zero, witnessG2]
    ring
  have h := (four_terms_initial F D hdata hD).2
  rwa [he] at h

private noncomputable def witnessKernel (d : ℤ) : CompleteRing :=
  complete (3 + d) - complete 1 * complete (2 + d)

private theorem witnessKernel_data (d : ℤ) (hd : 0 ≤ d) :
    witnessKernel d ≠ 0 ∧
      initialForm squareWeight.generatorWeight (witnessKernel d) =
        -(complete 1 * complete (2 + d)) ∧
      monomialValuation squareWeight.generatorWeight (witnessKernel d) =
        ((1 + ((2 + d).toNat : ℝ) ^ 2 : ℝ) : WithTop ℝ) := by
  have h := boundary_ratio_kernel squareWeight 2 1 d (by norm_num) (by norm_num) hd
  have hw : ∀ k, squareWeight.weight k = (k : ℝ) ^ 2 := fun _ => rfl
  norm_num only [Int.toNat_one, Nat.cast_one, one_pow] at h
  simpa only [witnessKernel, hw, Nat.cast_one, one_pow, ← WithTop.coe_add] using h

private theorem witness_response_sum :
    gridResponse (gridDefect endpointThreeWitnessLeft endpointThreeWitnessRight) 3 -
      complete 1 * gridResponse (gridDefect endpointThreeWitnessLeft endpointThreeWitnessRight) 2 =
        witnessG0 * witnessKernel 0 + witnessG1 * witnessKernel 3 +
          witnessG2 * witnessKernel 5 := by
  have h := Diagram.gridDefect_ratio_response_eq_sum
    endpointThreeWitnessLeft endpointThreeWitnessRight witness_common_grid 2 1
  rw [endpointThreeWitness_cofactor_difference] at h
  simp only [witness_grid_left, Fin.sum_univ_succ, Fin.sum_univ_zero,
    Matrix.cons_val_zero, Matrix.cons_val_succ, zero_mul, add_zero] at h
  change gridResponse (gridDefect endpointThreeWitnessLeft endpointThreeWitnessRight) 3 -
    complete 1 * gridResponse (gridDefect endpointThreeWitnessLeft endpointThreeWitnessRight) 2 =
      _ at h
  rw [h]
  unfold witnessKernel
  norm_num only
  ring

/-- The smallest endpoint-three residual has the exact initial monomial stated in the remark. -/
theorem endpointThreeWitness_residual_initialForm :
    initialForm squareWeight.generatorWeight
      (complete 1 * gridResponse (gridDefect endpointThreeWitnessLeft endpointThreeWitnessRight) 2 -
        gridResponse (gridDefect endpointThreeWitnessLeft endpointThreeWitnessRight) 3) =
      -(complete 1 ^ 3 * complete 2 * complete 4 * complete 5) := by
  let F : Fin 3 → CompleteRing := ![
    witnessG0 * witnessKernel 0, witnessG1 * witnessKernel 3, witnessG2 * witnessKernel 5]
  have hg0 : witnessG0 ≠ 0 := by
    intro hz
    have h := witnessG0_initial.2
    rw [hz, monomialValuation_zero] at h
    exact WithTop.top_ne_coe h
  have hf0 : F 0 ≠ 0 := mul_ne_zero hg0 (witnessKernel_data 0 (by omega)).1
  have hv0 : monomialValuation squareWeight.generatorWeight (F 0) = ((48 : ℝ) : WithTop ℝ) := by
    change monomialValuation squareWeight.generatorWeight (witnessG0 * witnessKernel 0) = _
    rw [monomialValuation_mul, witnessG0_initial.2, (witnessKernel_data 0 (by omega)).2.2]
    norm_num
  have hv1 : monomialValuation squareWeight.generatorWeight (F ⟨1, by omega⟩) =
      ((56 : ℝ) : WithTop ℝ) := by
    change monomialValuation squareWeight.generatorWeight (witnessG1 * witnessKernel 3) = _
    rw [monomialValuation_mul, witnessG1_valuation, (witnessKernel_data 3 (by omega)).2.2]
    norm_num
  have hv2 : monomialValuation squareWeight.generatorWeight (F ⟨2, by omega⟩) =
      ((64 : ℝ) : WithTop ℝ) := by
    change monomialValuation squareWeight.generatorWeight (witnessG2 * witnessKernel 5) = _
    rw [monomialValuation_mul, witnessG2_valuation, (witnessKernel_data 5 (by omega)).2.2]
    norm_num
  have hmin : ∀ j ∈ (Finset.univ : Finset (Fin 3)), j ≠ 0 →
      monomialValuation squareWeight.generatorWeight (F 0) <
        monomialValuation squareWeight.generatorWeight (F j) := by
    intro j _ hj
    fin_cases j
    · exact (hj rfl).elim
    · rw [hv0, hv1]
      exact WithTop.coe_lt_coe.mpr (by norm_num)
    · rw [hv0, hv2]
      exact WithTop.coe_lt_coe.mpr (by norm_num)
  have hi := (initialForm_sum_unique Finset.univ F (Finset.mem_univ 0) hf0 hmin).1
  have he : (∑ j, F j) = witnessG0 * witnessKernel 0 +
      witnessG1 * witnessKernel 3 + witnessG2 * witnessKernel 5 := by
    simp [F, Fin.sum_univ_succ]
    ring
  have hres : complete 1 *
      gridResponse (gridDefect endpointThreeWitnessLeft endpointThreeWitnessRight) 2 -
      gridResponse (gridDefect endpointThreeWitnessLeft endpointThreeWitnessRight) 3 =
        -(∑ j, F j) := by
    rw [he, ← witness_response_sum]
    ring
  rw [hres, initialForm_negation, hi]
  change -initialForm squareWeight.generatorWeight (witnessG0 * witnessKernel 0) = _
  rw [initialForm_mul hg0 (witnessKernel_data 0 (by omega)).1,
    witnessG0_initial.1, (witnessKernel_data 0 (by omega)).2.1]
  norm_num only [add_zero]
  ring

/-- The actual residual is nonzero and has finite square valuation48. -/
theorem endpointThreeWitness_residual_valuation :
    monomialValuation squareWeight.generatorWeight
      (complete 1 * gridResponse (gridDefect endpointThreeWitnessLeft endpointThreeWitnessRight) 2 -
        gridResponse (gridDefect endpointThreeWitnessLeft endpointThreeWitnessRight) 3) =
      ((48 : ℝ) : WithTop ℝ) := by
  let R := complete 1 *
    gridResponse (gridDefect endpointThreeWitnessLeft endpointThreeWitnessRight) 2 -
      gridResponse (gridDefect endpointThreeWitnessLeft endpointThreeWitnessRight) 3
  have h := negative_list_product_data [1, 1, 1, 2, 4, 5]
  have he : -([1, 1, 1, 2, 4, 5].map (fun k : ℕ => complete (k : ℤ))).prod =
      -(complete 1 ^ 3 * complete 2 * complete 4 * complete 5) := by
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, Nat.cast_ofNat]
    ring
  rw [he] at h
  norm_num only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Nat.cast_ofNat] at h
  have hi : initialForm squareWeight.generatorWeight R =
      -(complete 1 ^ 3 * complete 2 * complete 4 * complete 5) :=
    endpointThreeWitness_residual_initialForm
  have hn : R ≠ 0 := by
    intro hz
    rw [hz, initialForm_zero] at hi
    exact h.1 hi.symm
  have hh : MvPolynomial.IsWeightedHomogeneous squareWeight.generatorWeight
      (initialForm squareWeight.generatorWeight R) (leastWeight squareWeight.generatorWeight R) :=
    MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous _ _
  rw [hi] at hh
  have hw := MvPolynomial.IsWeightedHomogeneous.inj_right h.1 hh h.2
  change monomialValuation squareWeight.generatorWeight R = _
  rw [monomialValuation_eq_coe hn, hw]

end SkewSchurReconstruction
