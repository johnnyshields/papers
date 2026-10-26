/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewSchurReconstruction.StaircaseReversal
import SkewSchurReconstruction.RatioRigidity

/-!
# The endpoint-three staircase boundary

Formalizes "Reversal pairs on the locus" (`subsec:locus-family`) and its boundary
limitation `rem:staircase-boundary`.  The boundary-three cap grid is derived from
actual diagrams.  First-column determinant identities and formal word reversal
produce the three-term response relation.  No floor, gap, or minimizing coordinate
is an input to the boundary statements.  Sorry-free.
-/

namespace SkewSchurReconstruction

open scoped BigOperators

variable {N : ℕ}

/-- The endpoint-three boundary has a genuinely different cap origin. -/
theorem staircase_top_three (w : Fin N → ℕ) (hw : ∀ i, w i = 2 ∨ w i = 3)
    (hN : 0 < N) (hfirst : w ⟨0, hN⟩ = 3) : (staircaseDiagram w hw).top = N + 2 := by
  rw [Diagram.top_of_pos _ hN]
  change N - 1 - 0 + w ⟨0, hN⟩ = N + 2
  rw [hfirst]
  omega

theorem staircase_rowParam_three (w : Fin N → ℕ) (hw : ∀ i, w i = 2 ∨ w i = 3)
    (hN : 0 < N) (hfirst : w ⟨0, hN⟩ = 3) (i : Fin N) :
    (staircaseDiagram w hw).rowParam i = 2 * (i.val : ℤ) + 3 - w i := by
  have hi := i.isLt
  unfold Diagram.rowParam
  rw [staircase_top_three w hw hN hfirst]
  change ((N + 2 : ℕ) : ℤ) - ((N - 1 - i.val + w i : ℕ) : ℤ) + i.val = _
  omega

theorem staircase_capShift_three_succ (w : Fin N → ℕ) (hw : ∀ i, w i = 2 ∨ w i = 3)
    (hN : 0 < N) (hfirst : w ⟨0, hN⟩ = 3) (i : Fin N) :
    (staircaseDiagram w hw).capShift i.succ = 2 * ((i.val : ℤ) + 1) + 1 := by
  have hi := i.isLt
  rw [Diagram.capShift_succ, staircase_top_three w hw hN hfirst]
  change ((N + 2 : ℕ) : ℤ) - ((N - 1 - i.val : ℕ) : ℤ) + i.val = _
  omega

/-- The zero column remains zero; every positive cap shift is `2*j+1`. -/
theorem staircase_capShift_three (w : Fin N → ℕ) (hw : ∀ i, w i = 2 ∨ w i = 3)
    (hN : 0 < N) (hfirst : w ⟨0, hN⟩ = 3) (j : Fin (N + 1)) :
    (staircaseDiagram w hw).capShift j = if j.val = 0 then 0 else 2 * (j.val : ℤ) + 1 := by
  cases j using Fin.cases with
  | zero => simp only [Diagram.capShift_zero, Fin.val_zero, ite_true]
  | succ i =>
    rw [staircase_capShift_three_succ w hw hN hfirst]
    have hi : i.succ.val ≠ 0 := by change i.val + 1 ≠ 0; omega
    rw [ite_eq_right hi]
    simp only [Fin.val_succ, Nat.cast_add, Nat.cast_one]

/-- Ordinary staircase Jacobi--Trudi determinants do not depend on the boundary letter. -/
theorem staircase_ordinaryMatrix_any_front (w : Fin N → ℕ) (hw : ∀ i, w i = 2 ∨ w i = 3) :
    (staircaseDiagram w hw).ordinaryMatrix = completeWordMatrix w := by
  apply Matrix.ext
  intro i j
  have hi := i.isLt
  have hj := j.isLt
  simp only [Diagram.ordinaryMatrix, staircaseMatrix, Matrix.of_apply, completeWordMatrix,
    Diagram.capShift_succ, Diagram.rowParam]
  have ho : (staircaseDiagram w hw).outer i = N - 1 - i.val + w i := rfl
  have hm : (staircaseDiagram w hw).inner j = N - 1 - j.val := rfl
  rw [ho, hm]
  apply congrArg complete
  omega

theorem staircase_schurFunction_any_front (w : Fin N → ℕ) (hw : ∀ i, w i = 2 ∨ w i = 3) :
    (staircaseDiagram w hw).schurFunction = (completeWordMatrix w).det := by
  rw [Diagram.schurFunction_eq_det_ordinaryMatrix, staircase_ordinaryMatrix_any_front]

private theorem det_first_column_comparison {n : ℕ}
    (M Q : Matrix (Fin (n + 1)) (Fin (n + 1)) CompleteRing) (h : CompleteRing)
    (hcols : ∀ (i : Fin (n + 1)) (j : Fin n), M i j.succ = Q i j.succ)
    (hfirst : ∀ i, i ≠ 0 → Q i 0 = h * M i 0) :
    Q.det = h * M.det + (Q 0 0 - h * M 0 0) * (M.submatrix Fin.succ Fin.succ).det := by
  classical
  have hskip : (0 : Fin (n + 1)).succAbove = Fin.succ := by
    funext j
    exact Fin.zero_succAbove j
  have hminor : ∀ i : Fin (n + 1),
      Q.submatrix i.succAbove Fin.succ = M.submatrix i.succAbove Fin.succ := by
    intro i
    apply Matrix.ext
    intro k j
    exact (hcols _ _).symm
  rw [Matrix.det_succ_column_zero Q, Matrix.det_succ_column_zero M, Finset.mul_sum]
  have he : (∑ i : Fin (n + 1),
      ((-1 : CompleteRing) ^ i.val * Q i 0 * (Q.submatrix i.succAbove Fin.succ).det -
        h * ((-1 : CompleteRing) ^ i.val * M i 0 *
          (M.submatrix i.succAbove Fin.succ).det))) =
      (Q 0 0 - h * M 0 0) * (M.submatrix Fin.succ Fin.succ).det := by
    rw [Finset.sum_eq_single 0]
    · rw [hminor]
      simp only [Fin.val_zero, pow_zero, one_mul, hskip]
      ring
    · intro i _ hi
      rw [hminor, hfirst i hi]
      ring
    · intro hnot
      exact (hnot (Finset.mem_univ 0)).elim
  rw [Finset.sum_sub_distrib] at he
  linear_combination he

theorem capPolynomial_eq_border_det (X : Diagram N) (r : ℤ) :
    X.capPolynomial r =
      (cofactorBorderMatrix (fun j => complete (r + X.capShift j)) X.capMatrix).det := by
  rw [det_vecCons_eq_sum_signedMaximalCofactor]
  unfold Diagram.capPolynomial Diagram.cofactor
  apply Finset.sum_congr rfl
  intro j _
  exact mul_comm _ _

/-- Exact boundary-three capped relation, including the parent function correction. -/
theorem staircase_capPolynomial_three (w : Fin N → ℕ) (hw : ∀ i, w i = 2 ∨ w i = 3)
    (hN : 0 < N) (hfirst : w ⟨0, hN⟩ = 3) (r : ℕ) :
    complete 1 * (staircaseDiagram w hw).capPolynomial r =
      (completeWordMatrix (Fin.cases (r + 1) w)).det +
        (complete 1 * complete r - complete (r + 1)) * (completeWordMatrix w).det := by
  let X := staircaseDiagram w hw
  let M := cofactorBorderMatrix (fun j => complete ((r : ℤ) + X.capShift j)) X.capMatrix
  let Q := completeWordMatrix (Fin.cases (r + 1) w)
  have hcols : ∀ (i : Fin (N + 1)) (j : Fin N), M i j.succ = Q i j.succ := by
    intro i j
    cases i using Fin.cases with
    | zero =>
      simp only [M, cofactorBorderMatrix, Matrix.of_apply, Matrix.cons_val_zero, Q,
        completeWordMatrix, Fin.cases_zero, Fin.val_zero, Fin.val_succ]
      rw [staircase_capShift_three_succ w hw hN hfirst]
      apply congrArg complete
      push_cast
      ring
    | succ i =>
      simp only [M, cofactorBorderMatrix, Matrix.of_apply, Matrix.cons_val_succ,
        Diagram.capMatrix, Q, completeWordMatrix, Fin.cases_succ, Fin.val_succ]
      rw [staircase_capShift_three_succ w hw hN hfirst,
        staircase_rowParam_three w hw hN hfirst]
      apply congrArg complete
      push_cast
      ring
  have hfirstcol : ∀ i : Fin (N + 1), i ≠ 0 → Q i 0 = complete 1 * M i 0 := by
    intro i hi
    cases i using Fin.cases with
    | zero => exact (hi rfl).elim
    | succ i =>
      have hib := i.isLt
      simp only [Q, completeWordMatrix, Matrix.of_apply, Fin.cases_succ, Fin.val_zero,
        Fin.val_succ, M, cofactorBorderMatrix, Matrix.cons_val_succ, Diagram.capMatrix,
        Diagram.capShift_zero]
      rw [staircase_rowParam_three w hw hN hfirst]
      by_cases hi0 : i.val = 0
      · have he : i = ⟨0, hN⟩ := Fin.ext hi0
        subst i
        rw [hfirst]
        norm_num
      · have hq : complete ((w i : ℤ) + 2 * (0 - ((i.val + 1 : ℕ) : ℤ))) = 0 := by
          apply complete_of_neg
          rcases hw i with h | h <;> omega
        have hm : complete (0 - (2 * (i.val : ℤ) + 3 - w i)) = 0 := by
          apply complete_of_neg
          rcases hw i with h | h <;> omega
        simp only [Nat.cast_zero]
        rw [hq, hm, mul_zero]
  have hminor : M.submatrix Fin.succ Fin.succ = completeWordMatrix w := by
    apply Matrix.ext
    intro i j
    simp only [M, cofactorBorderMatrix, Matrix.submatrix_apply, Matrix.of_apply,
      Matrix.cons_val_succ, Diagram.capMatrix, completeWordMatrix]
    rw [staircase_capShift_three_succ w hw hN hfirst,
      staircase_rowParam_three w hw hN hfirst]
    apply congrArg complete
    ring
  have h := det_first_column_comparison M Q (complete 1) hcols hfirstcol
  have hM : M.det = X.capPolynomial r := (capPolynomial_eq_border_det X r).symm
  have hm0 : M 0 0 = complete r := by
    simp only [M, cofactorBorderMatrix, Matrix.of_apply, Matrix.cons_val_zero,
      Diagram.capShift_zero, add_zero]
  have hq0 : Q 0 0 = complete (r + 1) := by
    simp only [Q, completeWordMatrix, Matrix.of_apply, Fin.cases_zero,
      Fin.val_zero, sub_self, mul_zero, add_zero, Nat.cast_add, Nat.cast_one]
  rw [hM, hminor, hm0, hq0] at h
  change complete 1 * X.capPolynomial r = _
  linear_combination -h

private theorem complete_word_two_prefix (w : Fin N → ℕ) (hw : ∀ i, w i = 2 ∨ w i = 3) :
    (completeWordMatrix (Fin.cases 1 (Fin.cases 2 w))).det =
      complete 1 * (completeWordMatrix (Fin.cases 2 w)).det -
        (completeWordMatrix (Fin.cases 3 w)).det := by
  let M := completeWordMatrix (Fin.cases 1 (Fin.cases 2 w))
  have h0 : M 0 0 = complete 1 := by simp [M, completeWordMatrix]
  have h1 : M (0 : Fin (N + 1)).succ 0 = 1 := by
    simp only [M, completeWordMatrix, Matrix.of_apply, Fin.cases_succ, Fin.cases_zero,
      Fin.val_succ, Fin.val_zero]
    norm_num
  have htail : ∀ i : Fin N, M i.succ.succ 0 = 0 := by
    intro i
    simp only [M, completeWordMatrix, Matrix.of_apply, Fin.cases_succ, Fin.val_succ,
      Fin.val_zero]
    apply complete_of_neg
    rcases hw i with h | h <;> omega
  have hminor0 : M.submatrix Fin.succ Fin.succ = completeWordMatrix (Fin.cases 2 w) := by
    apply Matrix.ext
    intro i j
    cases i using Fin.cases <;>
      simp only [M, completeWordMatrix, Matrix.submatrix_apply, Matrix.of_apply,
        Fin.cases_succ, Fin.cases_zero, Fin.val_succ] <;>
      apply congrArg complete <;> push_cast <;> ring
  have hminor1 : M.submatrix (0 : Fin (N + 1)).succ.succAbove Fin.succ =
      completeWordMatrix (Fin.cases 3 w) := by
    apply Matrix.ext
    intro i j
    cases i using Fin.cases with
    | zero =>
      simp only [M, completeWordMatrix, Matrix.submatrix_apply, Matrix.of_apply,
        Fin.succ_succAbove_zero, Fin.cases_zero, Fin.val_zero, Fin.val_succ]
      apply congrArg complete
      push_cast
      ring
    | succ i =>
      simp only [M, completeWordMatrix, Matrix.submatrix_apply, Matrix.of_apply,
        Fin.succ_succAbove_succ, Fin.zero_succAbove, Fin.cases_succ, Fin.val_succ]
      apply congrArg complete
      push_cast
      ring
  have hskip : (0 : Fin (N + 2)).succAbove = Fin.succ := by
    funext j
    exact Fin.zero_succAbove j
  rw [Matrix.det_succ_column_zero M, Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp only [h0, h1, htail, hskip, hminor0, hminor1, Fin.val_zero, Fin.val_succ,
    pow_zero, one_mul, mul_one, mul_zero, zero_mul, Finset.sum_const_zero, add_zero]
  ring

/-- Formal word reversal still holds at boundary three, despite its different cap origin. -/
theorem complete_word_two_prefix_reversal (w : Fin N → ℕ) (hw : ∀ i, w i = 2 ∨ w i = 3) :
    (completeWordMatrix (Fin.cases 1 (Fin.cases 2 w))).det =
      (completeWordMatrix (Fin.cases 1 (Fin.cases 2 (reversedWord w)))).det := by
  let x : Fin N → Bool := fun i => decide (w i = 3)
  have hx : binaryLength x = w := by
    funext i
    rcases hw i with h | h <;> simp [binaryLength, x, h]
  have h := TwoSeries.wordMatrix_det_reversal evenCompleteSeries oddCompleteSeries
    evenCompleteSeries_constant x
  rw [← completeWordMatrix_two_series, ← completeWordMatrix_two_series] at h
  simpa only [binaryLength_wordReverse, hx] using h

/-- The third elementary polynomial, expressed in the free complete generators. -/
noncomputable def elementaryThree : CompleteRing :=
  complete 1 ^ 3 - 2 * complete 1 * complete 2 + complete 3

private theorem gridDefect_zero_schur (X Y : Diagram N) :
    gridDefect X Y 0 = X.schurFunction - Y.schurFunction := by
  have hx := X.cofactorGridVector_apply_capShift 0
  have hy := Y.cofactorGridVector_apply_capShift 0
  simp only [Diagram.capShift_zero] at hx hy
  simp only [gridDefect, Finsupp.sub_apply, hx, hy, Diagram.schurFunction]

/-- The actual three-term capped relation in `rem:staircase-boundary`. -/
theorem staircase_boundary_three_relation (w : Fin N → ℕ)
    (hw : ∀ i, w i = 2 ∨ w i = 3) (hN : 0 < N)
    (hfirst : w ⟨0, hN⟩ = 3) (hlast : w ⟨N - 1, by omega⟩ = 3) :
    let X := staircaseDiagram w hw
    let Y := staircaseDiagram (reversedWord w) (reversedWord_binary w hw)
    let G := gridDefect X Y
    complete 1 * gridResponse G 2 - complete 1 ^ 2 * gridResponse G 1 +
      elementaryThree * G 0 = 0 := by
  let X := staircaseDiagram w hw
  let Y := staircaseDiagram (reversedWord w) (reversedWord_binary w hw)
  have hrevfirst : reversedWord w ⟨0, hN⟩ = 3 := by
    change w ⟨N - (0 + 1), by omega⟩ = 3
    exact hlast
  have hrev := complete_word_two_prefix_reversal w hw
  rw [complete_word_two_prefix w hw,
    complete_word_two_prefix (reversedWord w) (reversedWord_binary w hw)] at hrev
  have hx1 := staircase_capPolynomial_three w hw hN hfirst 1
  have hx2 := staircase_capPolynomial_three w hw hN hfirst 2
  have hy1 := staircase_capPolynomial_three (reversedWord w) (reversedWord_binary w hw)
    hN hrevfirst 1
  have hy2 := staircase_capPolynomial_three (reversedWord w) (reversedWord_binary w hw)
    hN hrevfirst 2
  have hc2 : complete (((1 : ℕ) : ℤ) + 1) = complete 2 := by
    apply congrArg complete
    norm_num
  have hc3 : complete (((2 : ℕ) : ℤ) + 1) = complete 3 := by
    apply congrArg complete
    norm_num
  rw [hc2] at hx1 hy1
  rw [hc3] at hx2 hy2
  change complete 1 * gridResponse (gridDefect X Y) 2 -
    complete 1 ^ 2 * gridResponse (gridDefect X Y) 1 + elementaryThree * gridDefect X Y 0 = 0
  rw [gridDefect_response, gridDefect_response, gridDefect_zero_schur,
    staircase_schurFunction_any_front, staircase_schurFunction_any_front]
  unfold elementaryThree
  linear_combination -hrev - complete 1 * hx1 + hx2 + complete 1 * hy1 - hy2

/-- Endpoint-three nonpalindromic parents are skew-Schur inequivalent, not merely distinct words. -/
theorem staircase_boundary_three_schur_ne (w : Fin N → ℕ)
    (hw : ∀ i, w i = 2 ∨ w i = 3) (hN : 0 < N)
    (hfirst : w ⟨0, hN⟩ = 3) (hlast : w ⟨N - 1, by omega⟩ = 3)
    (hne : w ≠ reversedWord w) :
    (staircaseDiagram w hw).schurFunction ≠
      (staircaseDiagram (reversedWord w) (reversedWord_binary w hw)).schurFunction := by
  intro heq
  let X := staircaseDiagram w hw
  let Y := staircaseDiagram (reversedWord w) (reversedWord_binary w hw)
  let G := gridDefect X Y
  have hzero : G 0 = 0 := by
    rw [gridDefect_zero_schur]
    exact sub_eq_zero.mpr heq
  have hrel := staircase_boundary_three_relation w hw hN hfirst hlast
  change complete 1 * gridResponse G 2 - complete 1 ^ 2 * gridResponse G 1 +
    elementaryThree * G 0 = 0 at hrel
  rw [hzero, mul_zero, add_zero] at hrel
  have hp : gridResponse G 2 = complete 1 * gridResponse G 1 := by
    apply mul_left_cancel₀ (complete_ne_zero_of_nonneg 1 (by omega))
    linear_combination hrel
  have hex := Diagram.equal_pair_ratio_exclusion X Y
    (staircase_connected w hw hN) (staircase_connected _ (reversedWord_binary w hw) hN)
    (staircase_common_inner _ _ hw (reversedWord_binary w hw))
    (staircase_ne_of_word_ne _ _ hw (reversedWord_binary w hw) hne) heq 1 1
    (by norm_num) (by norm_num)
  change gridResponse G 2 ≠ complete 1 * gridResponse G 1 at hex
  exact hex hp

theorem staircase_boundary_three_defect_zero_ne (w : Fin N → ℕ)
    (hw : ∀ i, w i = 2 ∨ w i = 3) (hN : 0 < N)
    (hfirst : w ⟨0, hN⟩ = 3) (hlast : w ⟨N - 1, by omega⟩ = 3)
    (hne : w ≠ reversedWord w) :
    gridDefect (staircaseDiagram w hw)
      (staircaseDiagram (reversedWord w) (reversedWord_binary w hw)) 0 ≠ 0 := by
  rw [gridDefect_zero_schur]
  exact sub_ne_zero.mpr (staircase_boundary_three_schur_ne w hw hN hfirst hlast hne)

private theorem square_weight_nat (i : ℕ) : squareWeight.weight i = (i : ℝ) ^ 2 := rfl

private theorem int_toNat_two : (2 : ℤ).toNat = 2 := rfl

private theorem int_toNat_three : (3 : ℤ).toNat = 3 := rfl

private theorem square_weight_int (i : ℤ) (hi : 0 ≤ i) :
    squareWeight.weight i.toNat = (i : ℝ) ^ 2 := by
  have h : (i.toNat : ℤ) = i := by omega
  have hc : (i.toNat : ℝ) = (i : ℝ) := by exact_mod_cast h
  rw [square_weight_nat, hc]

/-- The third elementary polynomial has its genuine cubic initial monomial. -/
theorem elementaryThree_initial_valuation :
    elementaryThree ≠ 0 ∧
      initialForm squareWeight.generatorWeight elementaryThree = complete 1 ^ 3 ∧
      monomialValuation squareWeight.generatorWeight elementaryThree =
        ((3 : ℝ) : WithTop ℝ) := by
  let p : CompleteRing := complete 1 ^ 3
  let q : CompleteRing := -(2 * complete 1 * complete 2)
  let r : CompleteRing := complete 3
  have hh1 : MvPolynomial.IsWeightedHomogeneous squareWeight.generatorWeight
      (complete 1) 1 := by
    have h := complete_convex_homogeneous squareWeight 1 (by omega)
    simpa only [square_weight_nat, Int.toNat_one, Nat.cast_one, one_pow] using h
  have hh2 : MvPolynomial.IsWeightedHomogeneous squareWeight.generatorWeight
      (complete 2) 4 := by
    have h := complete_convex_homogeneous squareWeight 2 (by omega)
    rw [int_toNat_two, square_weight_nat] at h
    norm_num only [Nat.cast_ofNat] at h
    exact h
  have hhC : MvPolynomial.IsWeightedHomogeneous squareWeight.generatorWeight
      (2 : CompleteRing) 0 := by
    simpa using MvPolynomial.isWeightedHomogeneous_C squareWeight.generatorWeight (2 : ℤ)
  have hhp : MvPolynomial.IsWeightedHomogeneous squareWeight.generatorWeight p 3 := by
    simpa [p] using hh1.pow 3
  have hhq : MvPolynomial.IsWeightedHomogeneous squareWeight.generatorWeight q 5 := by
    have h := ((hhC.mul hh1).mul hh2).neg
    norm_num only [zero_add] at h
    simpa [q] using h
  have hp : p ≠ 0 := pow_ne_zero 3 (complete_ne_zero_of_nonneg 1 (by omega))
  have hq : q ≠ 0 := by
    apply neg_ne_zero.mpr
    exact mul_ne_zero (mul_ne_zero (by norm_num) (complete_ne_zero_of_nonneg 1 (by omega)))
      (complete_ne_zero_of_nonneg 2 (by omega))
  have hpval := monomialValuation_eq_of_homogeneous hp hhp
  have hqval := monomialValuation_eq_of_homogeneous hq hhq
  have hrval : monomialValuation squareWeight.generatorWeight r = ((9 : ℝ) : WithTop ℝ) := by
    have h := complete_monomialValuation squareWeight 3 (by omega)
    rw [int_toNat_three, square_weight_nat] at h
    norm_num only [Nat.cast_ofNat] at h
    change monomialValuation squareWeight.generatorWeight (complete 3) = _
    exact h
  have hqr := monomialValuation_add_ge squareWeight.generatorWeight q r
  rw [hqval, hrval] at hqr
  have hlt : monomialValuation squareWeight.generatorWeight p <
      monomialValuation squareWeight.generatorWeight (q + r) := by
    apply lt_of_lt_of_le _ hqr
    rw [hpval]
    exact lt_min (WithTop.coe_lt_coe.mpr (by norm_num : (3 : ℝ) < 5))
      (WithTop.coe_lt_coe.mpr (by norm_num : (3 : ℝ) < 9))
  have he : p + (q + r) = elementaryThree := by dsimp [p, q, r, elementaryThree]; ring
  have hv := monomialValuation_add_eq_left hlt
  rw [he, hpval] at hv
  have hn : elementaryThree ≠ 0 := by
    intro hz
    rw [hz, monomialValuation_zero] at hv
    exact WithTop.top_ne_coe hv
  refine ⟨hn, ?_, hv⟩
  have hi := initialForm_add_eq_left hp (strict_lowerBound_of_valuation_lt hp hlt)
  rw [he, initialForm_eq_of_homogeneous hp hhp] at hi
  exact hi

private theorem cap_summand_square_value (X Y : Diagram N) (k : ℕ) (j : Fin (N + 1)) :
    monomialValuation squareWeight.generatorWeight
      (Diagram.cofactorDefect X Y j * complete ((k : ℤ) + X.capShift j)) =
        Diagram.defectAction squareWeight X Y j +
          ((2 * (k : ℝ) * (X.capShift j : ℝ) + (k : ℝ) ^ 2 : ℝ) : WithTop ℝ) := by
  have hd := X.capShift_nonneg j
  have hk : 0 ≤ (k : ℤ) + X.capShift j := by omega
  rw [monomialValuation_mul, complete_monomialValuation squareWeight _ hk]
  unfold Diagram.defectAction
  rw [square_weight_int _ hk, square_weight_int _ hd, add_assoc, ← WithTop.coe_add]
  apply congrArg (fun c : ℝ =>
    monomialValuation squareWeight.generatorWeight (Diagram.cofactorDefect X Y j) +
      (c : WithTop ℝ))
  push_cast
  ring

private theorem valuation_sum_lower_bound {ι : Type*} (s : Finset ι)
    (f : ι → CompleteRing) (b : ℝ)
    (hf : ∀ i ∈ s, (b : WithTop ℝ) ≤ monomialValuation squareWeight.generatorWeight (f i)) :
    (b : WithTop ℝ) ≤ monomialValuation squareWeight.generatorWeight (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, monomialValuation_zero, le_top]
  | @insert i s his ih =>
    rw [Finset.sum_insert his]
    have hi := hf i (Finset.mem_insert_self _ _)
    have hrest := ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
    exact (le_min hi hrest).trans
      (monomialValuation_add_ge squareWeight.generatorWeight _ _)

set_option maxHeartbeats 1000000 in
-- The assembly normalizes the exact three-term relation and both full finite response sums.
/-- No nonpalindromic endpoint-three word lies on the `(2,1)` ratio locus. -/
theorem staircase_boundary_three_ratio_exclusion (w : Fin N → ℕ)
    (hw : ∀ i, w i = 2 ∨ w i = 3) (hN : 2 ≤ N)
    (hfirst : w ⟨0, by omega⟩ = 3) (hlast : w ⟨N - 1, by omega⟩ = 3)
    (hne : w ≠ reversedWord w) :
    ¬ RatioIdentity
      (gridDefect (staircaseDiagram w hw)
        (staircaseDiagram (reversedWord w) (reversedWord_binary w hw))) 2 1 := by
  classical
  intro hratio
  have hn : 0 < N := by omega
  let X := staircaseDiagram w hw
  let Y := staircaseDiagram (reversedWord w) (reversedWord_binary w hw)
  let G := gridDefect X Y
  have hX : X.Connected := staircase_connected w hw hn
  have hY : Y.Connected := staircase_connected _ (reversedWord_binary w hw) hn
  have hinner : X.inner = Y.inner := staircase_common_inner _ _ hw (reversedWord_binary w hw)
  have hG0 : G 0 ≠ 0 := staircase_boundary_three_defect_zero_ne w hw hn hfirst hlast hne
  have hG : gridDefect X Y ≠ 0 := by
    intro hz
    have h := congrArg (fun f : ℤ →₀ CompleteRing => f 0) hz
    exact hG0 h
  have hrevfirst : reversedWord w ⟨0, hn⟩ = 3 := by
    change w ⟨N - (0 + 1), by omega⟩ = 3
    exact hlast
  have htop : X.top = Y.top := by
    change (staircaseDiagram w hw).top =
      (staircaseDiagram (reversedWord w) (reversedWord_binary w hw)).top
    rw [staircase_top_three w hw hn hfirst,
      staircase_top_three _ (reversedWord_binary w hw) hn hrevfirst]
  have hgrid : ∀ j, X.capShift j = Y.capShift j := by
    intro j
    change (staircaseDiagram w hw).capShift j =
      (staircaseDiagram (reversedWord w) (reversedWord_binary w hw)).capShift j
    rw [staircase_capShift_three w hw hn hfirst,
      staircase_capShift_three _ (reversedWord_binary w hw) hn hrevfirst]
  have hneXY : X ≠ Y := staircase_ne_of_word_ne _ _ hw (reversedWord_binary w hw) hne
  obtain ⟨v, hv, hprefix, hchanged⟩ :=
    Diagram.exists_first_changed_row X Y hn htop hinner hneXY
  have hstrict := Diagram.ratio_strict_floor_normalized squareWeight X Y hX hY hgrid
    2 1 (by norm_num) hratio v hprefix hchanged
  have hfloorRaw := (Diagram.cap_fixed_floor squareWeight X Y hX hY hgrid v hv hprefix
    hchanged hstrict).2.1
  let j1 : Fin (N + 1) := ⟨1, by omega⟩
  have hOne : (1 : Fin (N + 1)) = j1 := by
    apply Fin.ext
    change 1 % (N + 1) = 1
    exact Nat.mod_eq_of_lt (by omega)
  have hshift1 : X.capShift j1 = 3 := by
    rw [staircase_capShift_three w hw hn hfirst]
    simp only [j1, Nat.cast_one]
    norm_num
  have hsupp := Diagram.ratio_virtual_gap_normalized squareWeight X Y hX hY hgrid 2 1
    (by norm_num) hratio v hprefix hchanged
  rw [hOne] at hsupp
  have hC0 := hsupp.1
  have hC1 := hsupp.2.1
  let u : ℝ := leastWeight squareWeight.generatorWeight (Diagram.cofactorDefect X Y j1) + 9
  have hfloor : Diagram.positiveFloor squareWeight X Y = (u : WithTop ℝ) := by
    rw [hfloorRaw]
    change Diagram.defectAction squareWeight X Y j1 = (u : WithTop ℝ)
    unfold Diagram.defectAction
    rw [monomialValuation_eq_coe hC1, hshift1]
    rw [int_toNat_three, square_weight_nat]
    norm_num only [Nat.cast_ofNat]
    change (leastWeight squareWeight.generatorWeight (Diagram.cofactorDefect X Y j1) :
      WithTop ℝ) + ((9 : ℝ) : WithTop ℝ) = (u : WithTop ℝ)
    rw [← WithTop.coe_add]
  have ha1 : Diagram.defectAction squareWeight X Y j1 = (u : WithTop ℝ) := by
    change Diagram.positiveFloor squareWeight X Y =
      Diagram.defectAction squareWeight X Y j1 at hfloorRaw
    exact hfloorRaw.symm.trans hfloor
  have hgap := Diagram.ratio_square_gap_normalized X Y hX hY hgrid 2 1 (by norm_num)
    hratio v hprefix hchanged
  rw [hOne, hshift1] at hgap
  have hgamma : Diagram.ratioVirtualShift 2 1 = 2 := by
    rw [Diagram.ratioVirtualShift, ite_eq_right (by norm_num : (2 : ℕ) ≠ 0)]
  rw [hgamma, int_toNat_three, square_weight_nat] at hgap
  norm_num only [Nat.cast_ofNat] at hgap
  have hraw0 : leastWeight squareWeight.generatorWeight (Diagram.cofactorDefect X Y 0) =
      u + 12 := by
    dsimp [u]
    linarith only [hgap]
  have ha0 : Diagram.defectAction squareWeight X Y 0 = ((u + 12 : ℝ) : WithTop ℝ) := by
    unfold Diagram.defectAction
    rw [monomialValuation_eq_coe hC0, hraw0]
    simp only [Diagram.capShift_zero, Int.toNat_zero, squareWeight.zero,
      WithTop.coe_zero, add_zero]
  have hpositive : ∀ j : Fin (N + 1), 0 < j.val →
      (u : WithTop ℝ) ≤ Diagram.defectAction squareWeight X Y j := by
    intro j hj
    rw [← hfloor]
    exact Finset.inf_le
      (show j ∈ Finset.univ.filter (fun k : Fin (N + 1) => 0 < k.val) by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact hj)
  let F1 : Fin (N + 1) → CompleteRing := fun j =>
    Diagram.cofactorDefect X Y j * complete (((1 : ℕ) : ℤ) + X.capShift j)
  let F2 : Fin (N + 1) → CompleteRing := fun j =>
    Diagram.cofactorDefect X Y j * complete (((2 : ℕ) : ℤ) + X.capShift j)
  have hF1 : monomialValuation squareWeight.generatorWeight (F1 j1) =
      ((u + 7 : ℝ) : WithTop ℝ) := by
    dsimp only [F1]
    rw [cap_summand_square_value X Y 1 j1, ha1, hshift1]
    norm_num only [Nat.cast_one, one_mul, one_pow, Int.cast_ofNat]
    norm_cast
  have hF1nz : F1 j1 ≠ 0 := by
    dsimp [F1]
    exact mul_ne_zero hC1 (complete_ne_zero_of_nonneg _ (by have h := X.capShift_nonneg j1; omega))
  have hF1min : ∀ j ∈ (Finset.univ : Finset (Fin (N + 1))), j ≠ j1 →
      monomialValuation squareWeight.generatorWeight (F1 j1) <
        monomialValuation squareWeight.generatorWeight (F1 j) := by
    intro j _ hj
    rw [hF1]
    by_cases hj0 : j.val = 0
    · have he : j = 0 := Fin.ext hj0
      subst j
      dsimp only [F1]
      rw [cap_summand_square_value X Y 1 0, ha0]
      simp only [Diagram.capShift_zero, Int.cast_zero, mul_zero, Nat.cast_one, one_pow, zero_add]
      norm_cast
      linarith only []
    · have hj1 : j.val ≠ 1 := by
        intro h
        apply hj
        apply Fin.ext
        change j.val = 1
        exact h
      have hd : (5 : ℤ) ≤ X.capShift j := by
        rw [staircase_capShift_three w hw hn hfirst, ite_eq_right hj0]
        omega
      have hdr : (5 : ℝ) ≤ (X.capShift j : ℝ) := by exact_mod_cast hd
      have hf := hpositive j (by omega)
      have hb : ((u + 11 : ℝ) : WithTop ℝ) ≤
          monomialValuation squareWeight.generatorWeight (F1 j) := by
        dsimp only [F1]
        rw [cap_summand_square_value X Y 1 j]
        norm_num only [Nat.cast_one]
        have hl : ((u + 11 : ℝ) : WithTop ℝ) ≤
            (u : WithTop ℝ) + ((2 * (1 : ℝ) * (X.capShift j : ℝ) + (1 : ℝ) ^ 2 : ℝ) :
              WithTop ℝ) := by
          rw [← WithTop.coe_add]
          apply WithTop.coe_le_coe.mpr
          linarith only [hdr]
        exact hl.trans (add_le_add hf (by norm_num))
      exact lt_of_lt_of_le (WithTop.coe_lt_coe.mpr
        (by linarith only [] : u + 7 < u + 11)) hb
  have hsum1nz := sum_ne_zero_of_unique_min Finset.univ F1 (Finset.mem_univ j1) hF1nz hF1min
  have hsum1least := (initialForm_sum_unique Finset.univ F1 (Finset.mem_univ j1) hF1nz hF1min).2
  have hsum1val : monomialValuation squareWeight.generatorWeight (∑ j, F1 j) =
      ((u + 7 : ℝ) : WithTop ℝ) := by
    rw [monomialValuation_eq_coe hsum1nz, hsum1least,
      ← monomialValuation_eq_coe hF1nz, hF1]
  have hresponse1 : gridResponse G 1 = ∑ j, F1 j :=
    Diagram.gridDefect_response_eq_sum X Y hgrid 1
  have hP1 : monomialValuation squareWeight.generatorWeight (gridResponse G 1) =
      ((u + 7 : ℝ) : WithTop ℝ) := by rw [hresponse1]; exact hsum1val
  have hF2bound : ∀ j ∈ (Finset.univ : Finset (Fin (N + 1))),
      ((u + 16 : ℝ) : WithTop ℝ) ≤ monomialValuation squareWeight.generatorWeight (F2 j) := by
    intro j _
    by_cases hj0 : j.val = 0
    · have he : j = 0 := Fin.ext hj0
      subst j
      dsimp only [F2]
      rw [cap_summand_square_value X Y 2 0, ha0]
      simp only [Diagram.capShift_zero, Int.cast_zero, mul_zero, zero_add, Nat.cast_ofNat]
      rw [← WithTop.coe_add]
      apply WithTop.coe_le_coe.mpr
      linarith only []
    · have hd : (3 : ℤ) ≤ X.capShift j := by
        rw [staircase_capShift_three w hw hn hfirst, ite_eq_right hj0]
        omega
      have hdr : (3 : ℝ) ≤ (X.capShift j : ℝ) := by exact_mod_cast hd
      have hf := hpositive j (by omega)
      dsimp only [F2]
      rw [cap_summand_square_value X Y 2 j]
      norm_num only [Nat.cast_ofNat]
      have hl : ((u + 16 : ℝ) : WithTop ℝ) ≤
          (u : WithTop ℝ) + ((2 * (2 : ℝ) * (X.capShift j : ℝ) + (2 : ℝ) ^ 2 : ℝ) :
            WithTop ℝ) := by
        rw [← WithTop.coe_add]
        apply WithTop.coe_le_coe.mpr
        linarith only [hdr]
      exact hl.trans (add_le_add hf (by norm_num))
  have hresponse2 : gridResponse G 2 = ∑ j, F2 j :=
    Diagram.gridDefect_response_eq_sum X Y hgrid 2
  have hP2 : ((u + 16 : ℝ) : WithTop ℝ) ≤
      monomialValuation squareWeight.generatorWeight (gridResponse G 2) := by
    rw [hresponse2]
    exact valuation_sum_lower_bound Finset.univ F2 _ hF2bound
  have hG0value : monomialValuation squareWeight.generatorWeight (G 0) =
      ((u + 12 : ℝ) : WithTop ℝ) := by
    have he : G 0 = Diagram.cofactorDefect X Y 0 := by
      rw [gridDefect_zero_schur]
      rfl
    rw [he, monomialValuation_eq_coe hC0, hraw0]
  have hh1 : MvPolynomial.IsWeightedHomogeneous squareWeight.generatorWeight
      (complete 1) 1 := by
    have h := complete_convex_homogeneous squareWeight 1 (by omega)
    simpa only [square_weight_nat, Int.toNat_one, Nat.cast_one, one_pow] using h
  have hh1sq : MvPolynomial.IsWeightedHomogeneous squareWeight.generatorWeight
      (complete 1 ^ 2) 2 := by simpa using hh1.pow 2
  have hh1nz : complete 1 ≠ 0 := complete_ne_zero_of_nonneg 1 (by omega)
  have hh1val : monomialValuation squareWeight.generatorWeight (complete 1) =
      ((1 : ℝ) : WithTop ℝ) := monomialValuation_eq_of_homogeneous hh1nz hh1
  have hh1sqval : monomialValuation squareWeight.generatorWeight (complete 1 ^ 2) =
      ((2 : ℝ) : WithTop ℝ) :=
    monomialValuation_eq_of_homogeneous (pow_ne_zero 2 hh1nz) hh1sq
  let H : Fin 3 → CompleteRing := Fin.cases (complete 1 * gridResponse G 2)
    (Fin.cases (-(complete 1 ^ 2 * gridResponse G 1)) (fun _ => elementaryThree * G 0))
  have hH0 : H 0 = complete 1 * gridResponse G 2 := rfl
  have hH1 : H (⟨1, by norm_num⟩ : Fin 3) = -(complete 1 ^ 2 * gridResponse G 1) := rfl
  have hH2 : H (⟨2, by norm_num⟩ : Fin 3) = elementaryThree * G 0 := rfl
  have hmiddle : monomialValuation squareWeight.generatorWeight (H ⟨1, by omega⟩) =
      ((u + 9 : ℝ) : WithTop ℝ) := by
    rw [hH1]
    rw [monomialValuation_neg, monomialValuation_mul, hh1sqval, hP1]
    rw [← WithTop.coe_add]
    apply congrArg (fun c : ℝ => (c : WithTop ℝ))
    ring
  have hmiddleNZ : H ⟨1, by omega⟩ ≠ 0 := by
    intro hz
    rw [hz, monomialValuation_zero] at hmiddle
    exact WithTop.top_ne_coe hmiddle
  have hHmin : ∀ j ∈ (Finset.univ : Finset (Fin 3)), j ≠ ⟨1, by omega⟩ →
      monomialValuation squareWeight.generatorWeight (H ⟨1, by omega⟩) <
        monomialValuation squareWeight.generatorWeight (H j) := by
    intro j _ hj
    have hb := j.isLt
    have hjval : j.val ≠ 1 := by intro he; exact hj (Fin.ext he)
    have hcases : j = 0 ∨ j = ⟨2, by norm_num⟩ := by
      by_cases h0 : j.val = 0
      · exact Or.inl (Fin.ext h0)
      · exact Or.inr (Fin.ext (show j.val = 2 by omega))
    rw [hmiddle]
    rcases hcases with rfl | rfl
    · rw [hH0]
      rw [monomialValuation_mul, hh1val]
      have hl := add_le_add (le_rfl : ((1 : ℝ) : WithTop ℝ) ≤ ((1 : ℝ) : WithTop ℝ)) hP2
      have hlt : ((u + 9 : ℝ) : WithTop ℝ) <
          ((1 : ℝ) : WithTop ℝ) + ((u + 16 : ℝ) : WithTop ℝ) := by
        rw [← WithTop.coe_add]
        exact WithTop.coe_lt_coe.mpr (by linarith only [])
      exact hlt.trans_le hl
    · rw [hH2]
      rw [monomialValuation_mul, elementaryThree_initial_valuation.2.2, hG0value]
      rw [← WithTop.coe_add]
      exact WithTop.coe_lt_coe.mpr (by linarith only [])
  have hrelation := staircase_boundary_three_relation w hw hn hfirst hlast
  change complete 1 * gridResponse G 2 - complete 1 ^ 2 * gridResponse G 1 +
    elementaryThree * G 0 = 0 at hrelation
  have hHzero : (∑ j, H j) = 0 := by
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_one]
    change H (0 : Fin 3) + (H ⟨1, by omega⟩ + H ⟨2, by omega⟩) = 0
    rw [hH0, hH1, hH2]
    linear_combination hrelation
  exact sum_ne_zero_of_unique_min Finset.univ H (Finset.mem_univ ⟨1, by omega⟩)
    hmiddleNZ hHmin hHzero

end SkewSchurReconstruction
