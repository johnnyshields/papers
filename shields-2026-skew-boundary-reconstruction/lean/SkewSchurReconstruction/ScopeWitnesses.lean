/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewSchurReconstruction.BoundaryWitnesses
import SkewSchurReconstruction.PolynomialValuation
import SkewSchurReconstruction.LaplaceFloor

/-!
# Actual scope witnesses

Formalizes "The strict floor condition is essential" (`subsec:floor-margin`) and
"The fingerprint does not identify an equality" (`subsec:fingerprint-not-classification`).
The floor-margin family is proved for every positive scale. Both examples are actual
connected diagrams, with determinant-defined cofactors and valuations. Sorry-free.
-/

namespace SkewSchurReconstruction
namespace Diagram

open scoped BigOperators

private theorem square_weight_value (i : ℕ) : squareWeight.weight i = (i : ℝ) ^ 2 := rfl

/-- The first actual parent in the arbitrarily scaled floor-margin example. -/
def floorMarginA (k : ℕ) (hk : 0 < k) : Diagram 3 where
  outer := (oneObservationU k hk).outer
  inner := ![3 * k - 2, 2 * k - 1, 0]
  outer_antitone := (oneObservationU k hk).outer_antitone
  inner_antitone := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp only [Matrix.cons_val_zero', Matrix.cons_val_succ', Fin.le_def] at * <;> omega
  row_nonempty := by
    intro i
    fin_cases i
    · change 3 * k - 2 < 6 * k - 2
      omega
    · change 2 * k - 1 < 5 * k - 1
      omega
    · change 0 < 2 * k
      omega

/-- The second actual parent in the floor-margin example. -/
def floorMarginB (k : ℕ) (hk : 0 < k) : Diagram 3 where
  outer := (oneObservationV k hk).outer
  inner := ![3 * k - 2, 2 * k - 1, 0]
  outer_antitone := (oneObservationV k hk).outer_antitone
  inner_antitone := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp only [Matrix.cons_val_zero', Matrix.cons_val_succ', Fin.le_def] at * <;> omega
  row_nonempty := by
    intro i
    fin_cases i
    · change 3 * k - 2 < 6 * k - 2
      omega
    · change 2 * k - 1 < 4 * k - 1
      omega
    · change 0 < 3 * k
      omega

theorem floorMargin_connected (k : ℕ) (hk : 0 < k) :
    (floorMarginA k hk).Connected ∧ (floorMarginB k hk).Connected := by
  constructor <;> refine ⟨by omega, ?_⟩ <;> intro i hi <;> fin_cases i
  · change 3 * k - 2 < 5 * k - 1
    omega
  · change 2 * k - 1 < 2 * k
    omega
  · change 2 + 1 < 3 at hi
    omega
  · change 3 * k - 2 < 4 * k - 1
    omega
  · change 2 * k - 1 < 3 * k
    omega
  · change 2 + 1 < 3 at hi
    omega

theorem floorMargin_inner_eq (k : ℕ) (hk : 0 < k) :
    (floorMarginA k hk).inner = (floorMarginB k hk).inner := rfl

theorem floorMargin_rowLength_grids (k : ℕ) (hk : 0 < k) (i : Fin 3) :
    (floorMarginA k hk).rowLength i = ![3 * k, 3 * k, 2 * k] i ∧
      (floorMarginB k hk).rowLength i = ![3 * k, 2 * k, 3 * k] i := by
  constructor <;> fin_cases i
  · change (6 * k - 2) - (3 * k - 2) = 3 * k
    omega
  · change (5 * k - 1) - (2 * k - 1) = 3 * k
    omega
  · change 2 * k - 0 = 2 * k
    omega
  · change (6 * k - 2) - (3 * k - 2) = 3 * k
    omega
  · change (4 * k - 1) - (2 * k - 1) = 2 * k
    omega
  · change 3 * k - 0 = 3 * k
    omega

theorem floorMargin_rowLengths_eq (k : ℕ) (hk : 0 < k) :
    ((floorMarginA k hk).rowLengthList : Multiset ℕ) =
      ((floorMarginB k hk).rowLengthList : Multiset ℕ) := by
  have hA : (floorMarginA k hk).rowLength = ![3 * k, 3 * k, 2 * k] :=
    funext fun i => (floorMargin_rowLength_grids k hk i).1
  have hB : (floorMarginB k hk).rowLength = ![3 * k, 2 * k, 3 * k] :=
    funext fun i => (floorMargin_rowLength_grids k hk i).2
  simp only [rowLengthList, hA, hB, List.ofFn_succ, List.ofFn_zero,
    Matrix.cons_val_zero, Matrix.cons_val_succ]
  change (3 * k) ::ₘ ((3 * k) ::ₘ ((2 * k) ::ₘ (0 : Multiset ℕ))) =
    (3 * k) ::ₘ ((2 * k) ::ₘ ((3 * k) ::ₘ (0 : Multiset ℕ)))
  exact congrArg (fun s : Multiset ℕ => (3 * k) ::ₘ s) (Multiset.cons_swap (3 * k) (2 * k) 0)

theorem floorMargin_row_grids (k : ℕ) (hk : 0 < k) (i : Fin 3) :
    (floorMarginA k hk).rowParam i = ![0, (k : ℤ), ((4 * k : ℕ) : ℤ)] i ∧
      (floorMarginB k hk).rowParam i = ![0, ((2 * k : ℕ) : ℤ), ((3 * k : ℕ) : ℤ)] i := by
  constructor <;> fin_cases i <;>
    simp [rowParam, top, floorMarginA, floorMarginB, oneObservationU, oneObservationV] <;> omega

theorem floorMargin_cap_grid (k : ℕ) (hk : 0 < k) (j : Fin 4) :
    (floorMarginA k hk).capShift j =
        ![0, ((3 * k : ℕ) : ℤ), ((4 * k : ℕ) : ℤ), ((6 * k : ℕ) : ℤ)] j ∧
      (floorMarginB k hk).capShift j =
        ![0, ((3 * k : ℕ) : ℤ), ((4 * k : ℕ) : ℤ), ((6 * k : ℕ) : ℤ)] j := by
  constructor <;> fin_cases j <;>
    simp [capShift, top, floorMarginA, floorMarginB, oneObservationU, oneObservationV] <;> omega

/-- The two actual three-row cap matrices at arbitrary scale. -/
theorem floorMargin_cap_matrices (k : ℕ) (hk : 0 < k) :
    (floorMarginA k hk).capMatrix = Matrix.of
      ![![1, complete ((3 * k : ℕ) : ℤ), complete ((4 * k : ℕ) : ℤ),
          complete ((6 * k : ℕ) : ℤ)],
        ![0, complete ((2 * k : ℕ) : ℤ), complete ((3 * k : ℕ) : ℤ),
          complete ((5 * k : ℕ) : ℤ)], ![0, 0, 1, complete ((2 * k : ℕ) : ℤ)]] ∧
      (floorMarginB k hk).capMatrix = Matrix.of
      ![![1, complete ((3 * k : ℕ) : ℤ), complete ((4 * k : ℕ) : ℤ),
          complete ((6 * k : ℕ) : ℤ)],
        ![0, complete (k : ℤ), complete ((2 * k : ℕ) : ℤ), complete ((4 * k : ℕ) : ℤ)],
        ![0, 1, complete (k : ℤ), complete ((3 * k : ℕ) : ℤ)]] := by
  constructor
  · apply Matrix.ext
    intro i j
    simp only [capMatrix, Matrix.of_apply, (floorMargin_row_grids k hk i).1,
      (floorMargin_cap_grid k hk j).1]
    fin_cases i <;> fin_cases j <;>
      simp only [Matrix.cons_val_zero', Matrix.cons_val_succ', sub_self, complete_zero] <;>
      first | rfl | exact complete_of_neg (by omega) | apply congrArg complete; omega
  · apply Matrix.ext
    intro i j
    simp only [capMatrix, Matrix.of_apply, (floorMargin_row_grids k hk i).2,
      (floorMargin_cap_grid k hk j).2]
    fin_cases i <;> fin_cases j <;>
      simp only [Matrix.cons_val_zero', Matrix.cons_val_succ', sub_self, complete_zero] <;>
      first | rfl | exact complete_of_neg (by omega) | apply congrArg complete; omega

theorem floorMargin_defect (k : ℕ) (hk : 0 < k) (j : Fin 4) :
    cofactorDefect (floorMarginA k hk) (floorMarginB k hk) j =
      ![-complete ((3 * k : ℕ) : ℤ) * complete ((5 * k : ℕ) : ℤ) -
          complete ((4 * k : ℕ) : ℤ) * complete ((2 * k : ℕ) : ℤ) ^ 2 -
          complete ((4 * k : ℕ) : ℤ) ^ 2 -
          complete ((6 * k : ℕ) : ℤ) * complete (k : ℤ) ^ 2 +
          2 * complete ((6 * k : ℕ) : ℤ) * complete ((2 * k : ℕ) : ℤ) +
          2 * complete (k : ℤ) * complete ((3 * k : ℕ) : ℤ) * complete ((4 * k : ℕ) : ℤ),
        complete ((5 * k : ℕ) : ℤ) - complete (k : ℤ) * complete ((4 * k : ℕ) : ℤ),
        complete ((2 * k : ℕ) : ℤ) ^ 2 - complete (k : ℤ) * complete ((3 * k : ℕ) : ℤ) +
          complete ((4 * k : ℕ) : ℤ),
        complete (k : ℤ) ^ 2 - 2 * complete ((2 * k : ℕ) : ℤ)] j := by
  unfold cofactorDefect cofactor signedMaximalCofactor
  rw [(floorMargin_cap_matrices k hk).1, (floorMargin_cap_matrices k hk).2]
  fin_cases j <;>
    norm_num [Matrix.det_fin_three, Matrix.submatrix_apply, Matrix.of_apply, Fin.succAbove] <;> ring

/-- First actual parent whose fingerprint does not classify equality. -/
def fingerprintX : Diagram 3 where
  outer := ![7, 5, 4]
  inner := ![4, 2, 0]
  outer_antitone := by intro i j h; fin_cases i <;> fin_cases j <;> norm_num at *
  inner_antitone := by intro i j h; fin_cases i <;> fin_cases j <;> norm_num at *
  row_nonempty := by intro i; fin_cases i <;> norm_num

/-- Second actual parent with the same adjacent-floor fingerprint. -/
def fingerprintY : Diagram 3 where
  outer := ![7, 6, 3]
  inner := ![4, 2, 0]
  outer_antitone := by intro i j h; fin_cases i <;> fin_cases j <;> norm_num at *
  inner_antitone := by intro i j h; fin_cases i <;> fin_cases j <;> norm_num at *
  row_nonempty := by intro i; fin_cases i <;> norm_num

theorem fingerprint_connected : fingerprintX.Connected ∧ fingerprintY.Connected := by
  constructor <;> refine ⟨by omega, ?_⟩ <;> intro i hi <;> fin_cases i
  · change 4 < 5
    omega
  · change 2 < 4
    omega
  · change 2 + 1 < 3 at hi
    omega
  · change 4 < 6
    omega
  · change 2 < 3
    omega
  · change 2 + 1 < 3 at hi
    omega

theorem fingerprint_inner_eq : fingerprintX.inner = fingerprintY.inner := rfl

theorem fingerprint_cap_grid (j : Fin 4) :
    fingerprintX.capShift j = ![0, 3, 6, 9] j ∧ fingerprintY.capShift j = ![0, 3, 6, 9] j := by
  constructor <;> fin_cases j <;> norm_num [capShift, top, fingerprintX, fingerprintY]

theorem fingerprint_row_grids (i : Fin 3) :
    fingerprintX.rowParam i = ![0, 3, 5] i ∧ fingerprintY.rowParam i = ![0, 2, 6] i := by
  constructor <;> fin_cases i <;> norm_num [rowParam, top, fingerprintX, fingerprintY]

theorem fingerprint_defect (j : Fin 4) :
    cofactorDefect fingerprintX fingerprintY j =
      ![complete 3 * complete 7 - complete 4 * complete 6,
        complete 1 * complete 6 - complete 7,
        complete 4 - complete 1 * complete 3, 0] j := by
  unfold cofactorDefect cofactor signedMaximalCofactor
  fin_cases j <;>
    norm_num [Matrix.det_fin_three, capMatrix, Matrix.submatrix_apply, Matrix.of_apply,
      Fin.succAbove, fingerprint_row_grids, fingerprint_cap_grid] <;> ring

private noncomputable def indexMonomial (c : ℤ) (l : List ℕ) : CompleteRing :=
  MvPolynomial.C c * (l.map (fun i : ℕ => complete (i : ℤ))).prod

private theorem natural_product_ne_zero (l : List ℕ) :
    (l.map (fun i : ℕ => complete (i : ℤ))).prod ≠ 0 := by
  induction l with
  | nil => exact one_ne_zero
  | cons i l ih =>
      rw [List.map_cons, List.prod_cons]
      exact mul_ne_zero (complete_ne_zero_of_nonneg _ (by omega)) ih

private theorem natural_product_leastWeight (l : List ℕ) :
    leastWeight squareWeight.generatorWeight (l.map (fun i : ℕ => complete (i : ℤ))).prod =
      (l.map (fun i : ℕ => (i : ℝ) ^ 2)).sum := by
  induction l with
  | nil =>
      have hh := MvPolynomial.isWeightedHomogeneous_C squareWeight.generatorWeight (1 : ℤ)
      simpa using leastWeight_eq_of_homogeneous (p := (1 : CompleteRing)) one_ne_zero
        (by simpa using hh)
  | cons i l ih =>
      rw [List.map_cons, List.prod_cons,
        leastWeight_mul (complete_ne_zero_of_nonneg _ (by omega)) (natural_product_ne_zero l),
        complete_leastWeight squareWeight _ (by omega), ih]
      simp only [square_weight_value, Int.toNat_natCast, List.map_cons, List.sum_cons]

private theorem indexMonomial_valuation (c : ℤ) (hc : c ≠ 0) (l : List ℕ) :
    monomialValuation squareWeight.generatorWeight (indexMonomial c l) =
      (((l.map (fun i : ℕ => (i : ℝ) ^ 2)).sum : ℝ) : WithTop ℝ) := by
  have hC : (MvPolynomial.C c : CompleteRing) ≠ 0 := MvPolynomial.C_ne_zero.mpr hc
  have hvC : monomialValuation squareWeight.generatorWeight
      (MvPolynomial.C c : CompleteRing) = 0 := by
    simpa only [WithTop.coe_zero] using monomialValuation_eq_of_homogeneous hC
      (MvPolynomial.isWeightedHomogeneous_C squareWeight.generatorWeight c)
  rw [indexMonomial, monomialValuation_mul, hvC, zero_add,
    monomialValuation_eq_coe (natural_product_ne_zero l), natural_product_leastWeight]

private theorem scaled_indexMonomial_valuation (c : ℤ) (hc : c ≠ 0) (b : List ℕ) (k : ℕ) :
    monomialValuation squareWeight.generatorWeight
        (indexMonomial c (b.map (fun i => i * k))) =
      ((((b.map (fun i : ℕ => (i : ℝ) ^ 2)).sum * (k : ℝ) ^ 2) : ℝ) : WithTop ℝ) := by
  rw [indexMonomial_valuation c hc]
  congr 1
  induction b with
  | nil => simp
  | cons i b ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [ih]
      push_cast
      ring

private theorem finite_terms_minimum {N : ℕ} (f : Fin N → CompleteRing) (c : Fin N → ℝ)
    (hval : ∀ i, monomialValuation squareWeight.generatorWeight (f i) = (c i : WithTop ℝ))
    (q : Fin N) (hmin : ∀ i, i ≠ q → c q < c i) :
    (∑ i, f i) ≠ 0 ∧
      monomialValuation squareWeight.generatorWeight (∑ i, f i) = (c q : WithTop ℝ) := by
  classical
  let v : AddValuation CompleteRing (WithTop ℝ) :=
    polynomialAddValuation squareWeight.generatorWeight
  have hq : v (f q) ≠ ⊤ := by
    rw [polynomialAddValuation_apply, hval q]
    exact WithTop.coe_ne_top
  have he : v (∑ i, f i) = v (f q) := by
    rw [← Finset.add_sum_erase Finset.univ f (Finset.mem_univ q)]
    apply v.map_add_eq_of_lt_left
    apply v.map_lt_sum hq
    intro i hi
    rw [polynomialAddValuation_apply, polynomialAddValuation_apply, hval q, hval i]
    exact WithTop.coe_lt_coe.mpr (hmin i (Finset.ne_of_mem_erase hi))
  have hv : monomialValuation squareWeight.generatorWeight (∑ i, f i) = (c q : WithTop ℝ) := by
    dsimp only [v] at he
    rw [polynomialAddValuation_apply, polynomialAddValuation_apply, hval q] at he
    exact he
  refine ⟨?_, hv⟩
  intro hz
  rw [hz, monomialValuation_zero] at hv
  exact WithTop.coe_ne_top hv.symm

private noncomputable def floorZeroTerms (k : ℕ) : Fin 6 → CompleteRing :=
  ![indexMonomial (-1) [3 * k, 5 * k], indexMonomial (-1) [4 * k, 2 * k, 2 * k],
    indexMonomial (-1) [4 * k, 4 * k], indexMonomial (-1) [6 * k, k, k],
    indexMonomial 2 [6 * k, 2 * k], indexMonomial 2 [k, 3 * k, 4 * k]]

private def floorZeroCosts (k : ℕ) (j : Fin 6) : ℝ := ![34, 24, 32, 38, 40, 26] j * (k : ℝ) ^ 2

private theorem floorZeroTerms_valuation (k : ℕ) (j : Fin 6) :
    monomialValuation squareWeight.generatorWeight (floorZeroTerms k j) =
      (floorZeroCosts k j : WithTop ℝ) := by
  fin_cases j
  · have hv := scaled_indexMonomial_valuation (-1) (by norm_num) [3, 5] k
    norm_num at hv
    exact hv
  · have hv := scaled_indexMonomial_valuation (-1) (by norm_num) [4, 2, 2] k
    norm_num at hv
    exact hv
  · have hv := scaled_indexMonomial_valuation (-1) (by norm_num) [4, 4] k
    norm_num at hv
    exact hv
  · have hv := scaled_indexMonomial_valuation (-1) (by norm_num) [6, 1, 1] k
    norm_num at hv
    exact hv
  · have hv := scaled_indexMonomial_valuation 2 (by norm_num) [6, 2] k
    norm_num at hv
    exact hv
  · have hv := scaled_indexMonomial_valuation 2 (by norm_num) [1, 3, 4] k
    norm_num at hv
    exact hv

private theorem floorZeroTerms_sum (k : ℕ) (hk : 0 < k) :
    (∑ i, floorZeroTerms k i) = cofactorDefect (floorMarginA k hk) (floorMarginB k hk) 0 := by
  rw [floorMargin_defect]
  simp only [floorZeroTerms, Fin.sum_univ_succ,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_fin_one,
    indexMonomial, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    map_neg, map_one, map_ofNat]
  ring

theorem floorMargin_zero_valuation (k : ℕ) (hk : 0 < k) :
    monomialValuation squareWeight.generatorWeight
        (cofactorDefect (floorMarginA k hk) (floorMarginB k hk) 0) =
      ((24 * (k : ℝ) ^ 2 : ℝ) : WithTop ℝ) := by
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  have hs := finite_terms_minimum (floorZeroTerms k) (floorZeroCosts k)
    (floorZeroTerms_valuation k) (1 : Fin 6) (by
      intro i hi
      fin_cases i <;> norm_num at hi <;> norm_num [floorZeroCosts] <;>
        nlinarith [sq_pos_of_pos hkR])
  rw [floorZeroTerms_sum k hk] at hs
  exact hs.2

private noncomputable def floorSecondTerms (k : ℕ) : Fin 3 → CompleteRing :=
  ![indexMonomial 1 [2 * k, 2 * k], indexMonomial (-1) [k, 3 * k], indexMonomial 1 [4 * k]]

private def floorSecondCosts (k : ℕ) (j : Fin 3) : ℝ := ![8, 10, 16] j * (k : ℝ) ^ 2

private theorem floorSecondTerms_valuation (k : ℕ) (j : Fin 3) :
    monomialValuation squareWeight.generatorWeight (floorSecondTerms k j) =
      (floorSecondCosts k j : WithTop ℝ) := by
  fin_cases j
  · have hv := scaled_indexMonomial_valuation 1 (by norm_num) [2, 2] k
    norm_num at hv
    exact hv
  · have hv := scaled_indexMonomial_valuation (-1) (by norm_num) [1, 3] k
    norm_num at hv
    exact hv
  · have hv := scaled_indexMonomial_valuation 1 (by norm_num) [4] k
    norm_num at hv
    exact hv

theorem floorMargin_second_valuation (k : ℕ) (hk : 0 < k) :
    monomialValuation squareWeight.generatorWeight
        (cofactorDefect (floorMarginA k hk) (floorMarginB k hk) 2) =
      ((8 * (k : ℝ) ^ 2 : ℝ) : WithTop ℝ) := by
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  have hs := finite_terms_minimum (floorSecondTerms k) (floorSecondCosts k)
    (floorSecondTerms_valuation k) (0 : Fin 3) (by
      intro i hi
      fin_cases i <;> norm_num at hi <;> norm_num [floorSecondCosts] <;>
        nlinarith [sq_pos_of_pos hkR])
  have he : (∑ i, floorSecondTerms k i) =
      cofactorDefect (floorMarginA k hk) (floorMarginB k hk) 2 := by
    rw [floorMargin_defect]
    simp only [floorSecondTerms, Fin.sum_univ_succ,
      Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_fin_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
      indexMonomial, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      map_neg, map_one]
    ring
  rw [he] at hs
  exact hs.2

private noncomputable def floorThirdTerms (k : ℕ) : Fin 2 → CompleteRing :=
  ![indexMonomial 1 [k, k], indexMonomial (-2) [2 * k]]

private def floorThirdCosts (k : ℕ) (j : Fin 2) : ℝ := ![2, 4] j * (k : ℝ) ^ 2

private theorem floorThirdTerms_valuation (k : ℕ) (j : Fin 2) :
    monomialValuation squareWeight.generatorWeight (floorThirdTerms k j) =
      (floorThirdCosts k j : WithTop ℝ) := by
  fin_cases j
  · have hv := scaled_indexMonomial_valuation 1 (by norm_num) [1, 1] k
    norm_num at hv
    exact hv
  · have hv := scaled_indexMonomial_valuation (-2) (by norm_num) [2] k
    norm_num at hv
    exact hv

theorem floorMargin_third_valuation (k : ℕ) (hk : 0 < k) :
    monomialValuation squareWeight.generatorWeight
        (cofactorDefect (floorMarginA k hk) (floorMarginB k hk) 3) =
      ((2 * (k : ℝ) ^ 2 : ℝ) : WithTop ℝ) := by
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  have hs := finite_terms_minimum (floorThirdTerms k) (floorThirdCosts k)
    (floorThirdTerms_valuation k) (0 : Fin 2) (by
      intro i hi
      fin_cases i
      · norm_num at hi
      · norm_num [floorThirdCosts]
        nlinarith [sq_pos_of_pos hkR])
  have he : (∑ i, floorThirdTerms k i) =
      cofactorDefect (floorMarginA k hk) (floorMarginB k hk) 3 := by
    rw [floorMargin_defect]
    simp only [floorThirdTerms, Fin.sum_univ_succ,
      Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_fin_one,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
      indexMonomial, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      map_neg, map_one, map_ofNat]
    ring
  rw [he] at hs
  exact hs.2

private noncomputable def floorFirstTerms (k : ℕ) : Fin 2 → CompleteRing :=
  ![indexMonomial 1 [5 * k], indexMonomial (-1) [k, 4 * k]]

private def floorFirstCosts (k : ℕ) (j : Fin 2) : ℝ := ![25, 17] j * (k : ℝ) ^ 2

private theorem floorFirstTerms_valuation (k : ℕ) (j : Fin 2) :
    monomialValuation squareWeight.generatorWeight (floorFirstTerms k j) =
      (floorFirstCosts k j : WithTop ℝ) := by
  fin_cases j
  · have hv := scaled_indexMonomial_valuation 1 (by norm_num) [5] k
    norm_num at hv
    exact hv
  · have hv := scaled_indexMonomial_valuation (-1) (by norm_num) [1, 4] k
    norm_num at hv
    exact hv

theorem floorMargin_first_valuation (k : ℕ) (hk : 0 < k) :
    monomialValuation squareWeight.generatorWeight
        (cofactorDefect (floorMarginA k hk) (floorMarginB k hk) 1) =
      ((17 * (k : ℝ) ^ 2 : ℝ) : WithTop ℝ) := by
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  have hs := finite_terms_minimum (floorFirstTerms k) (floorFirstCosts k)
    (floorFirstTerms_valuation k) (1 : Fin 2) (by
      intro i hi
      fin_cases i
      · norm_num [floorFirstCosts]
        nlinarith [sq_pos_of_pos hkR]
      · norm_num at hi)
  have he : (∑ i, floorFirstTerms k i) =
      cofactorDefect (floorMarginA k hk) (floorMarginB k hk) 1 := by
    rw [floorMargin_defect]
    simp only [floorFirstTerms, Fin.sum_univ_succ,
      Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_fin_one, Matrix.cons_val_one,
      indexMonomial, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      map_neg, map_one]
    ring
  rw [he] at hs
  exact hs.2

theorem floorMargin_valuations (k : ℕ) (hk : 0 < k) (j : Fin 4) :
    monomialValuation squareWeight.generatorWeight
        (cofactorDefect (floorMarginA k hk) (floorMarginB k hk) j) =
      ((![24, 17, 8, 2] j * (k : ℝ) ^ 2 : ℝ) : WithTop ℝ) := by
  fin_cases j
  · exact floorMargin_zero_valuation k hk
  · exact floorMargin_first_valuation k hk
  · exact floorMargin_second_valuation k hk
  · exact floorMargin_third_valuation k hk

/-- The full square action tuple is exact at every positive scale, with only three rows. -/
theorem floorMargin_square_actions (k : ℕ) (hk : 0 < k) (j : Fin 4) :
    defectAction squareWeight (floorMarginA k hk) (floorMarginB k hk) j =
      ((![24, 26, 24, 38] j * (k : ℝ) ^ 2 : ℝ) : WithTop ℝ) := by
  unfold defectAction
  rw [floorMargin_valuations, (floorMargin_cap_grid k hk j).1]
  fin_cases j <;>
    simp only [Matrix.cons_val_zero', Matrix.cons_val_succ', square_weight_value,
      Int.toNat_natCast] <;>
    first
    | rfl
    | rw [← WithTop.coe_add]
      apply congrArg (fun x : ℝ => (x : WithTop ℝ))
      push_cast
      ring

theorem floorMargin_positiveFloor (k : ℕ) (hk : 0 < k) :
    positiveFloor squareWeight (floorMarginA k hk) (floorMarginB k hk) =
      ((24 * (k : ℝ) ^ 2 : ℝ) : WithTop ℝ) := by
  apply le_antisymm
  · apply (Finset.inf_le (s := Finset.univ.filter (fun j : Fin 4 => 0 < j.val))
      (f := defectAction squareWeight (floorMarginA k hk) (floorMarginB k hk))
      (by norm_num : (2 : Fin 4) ∈ Finset.univ.filter (fun j : Fin 4 => 0 < j.val))).trans
    rw [floorMargin_square_actions]
    rfl
  · apply Finset.le_inf
    intro j hj
    have hp := (Finset.mem_filter.mp hj).2
    rw [floorMargin_square_actions]
    fin_cases j
    · change 0 < 0 at hp
      omega
    · apply WithTop.coe_le_coe.mpr
      change 24 * (k : ℝ) ^ 2 ≤ 26 * (k : ℝ) ^ 2
      nlinarith [sq_nonneg (k : ℝ)]
    · exact le_rfl
    · apply WithTop.coe_le_coe.mpr
      change 24 * (k : ℝ) ^ 2 ≤ 38 * (k : ℝ) ^ 2
      nlinarith [sq_nonneg (k : ℝ)]

/-- Replacing the strict floor by equality admits the actual floor-margin family. -/
theorem floorMargin_zero_equals_floor (k : ℕ) (hk : 0 < k) :
    defectAction squareWeight (floorMarginA k hk) (floorMarginB k hk) 0 =
      positiveFloor squareWeight (floorMarginA k hk) (floorMarginB k hk) := by
  rw [floorMargin_square_actions, floorMargin_positiveFloor]
  rfl

/-- The excess of the first positive action is exactly `2 k^2`, uniformly in the scale. -/
theorem floorMargin_first_action_gap (k : ℕ) (hk : 0 < k) :
    defectAction squareWeight (floorMarginA k hk) (floorMarginB k hk) 1 =
      positiveFloor squareWeight (floorMarginA k hk) (floorMarginB k hk) +
        ((2 * (k : ℝ) ^ 2 : ℝ) : WithTop ℝ) := by
  rw [floorMargin_square_actions, floorMargin_positiveFloor, ← WithTop.coe_add]
  apply congrArg (fun x : ℝ => (x : WithTop ℝ))
  change 26 * (k : ℝ) ^ 2 = 24 * (k : ℝ) ^ 2 + 2 * (k : ℝ) ^ 2
  ring

theorem floorMargin_floor_columns (k : ℕ) (hk : 0 < k) :
    positiveFloorFace squareWeight (floorMarginA k hk) (floorMarginB k hk) = {2} := by
  classical
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  apply Finset.ext
  intro j
  simp only [positiveFloorFace, Finset.mem_filter, Finset.mem_univ, true_and,
    floorMargin_square_actions, floorMargin_positiveFloor, WithTop.coe_inj,
    Finset.mem_singleton]
  fin_cases j <;>
    simp only [Matrix.cons_val_zero', Matrix.cons_val_succ'] <;>
    norm_num <;> nlinarith [sq_pos_of_pos hkR]

theorem floorMargin_floor_shifts (k : ℕ) (hk : 0 < k) :
    (positiveFloorFace squareWeight (floorMarginA k hk) (floorMarginB k hk)).image
      (floorMarginA k hk).capShift = {((4 * k : ℕ) : ℤ)} := by
  rw [floorMargin_floor_columns, Finset.image_singleton, (floorMargin_cap_grid k hk 2).1]
  rfl

/-- The leftmost positive column is supported but lies outside the positive floor. -/
theorem floorMargin_leftmost_not_floor (k : ℕ) (hk : 0 < k) :
    cofactorDefect (floorMarginA k hk) (floorMarginB k hk) 1 ≠ 0 ∧
      (1 : Fin 4) ∉ positiveFloorFace squareWeight (floorMarginA k hk) (floorMarginB k hk) := by
  constructor
  · intro hz
    have hv := floorMargin_first_valuation k hk
    rw [hz, monomialValuation_zero] at hv
    exact WithTop.coe_ne_top hv.symm
  · rw [floorMargin_floor_columns]
    norm_num

/-- Every coordinate stays supported while the scale grows. -/
theorem floorMargin_all_coordinates_nonzero (k : ℕ) (hk : 0 < k) (j : Fin 4) :
    cofactorDefect (floorMarginA k hk) (floorMarginB k hk) j ≠ 0 := by
  intro hz
  have hv := floorMargin_valuations k hk j
  rw [hz, monomialValuation_zero] at hv
  exact WithTop.coe_ne_top hv.symm

theorem floorMargin_gridDefect_ne_zero (k : ℕ) (hk : 0 < k) :
    gridDefect (floorMarginA k hk) (floorMarginB k hk) ≠ 0 := by
  have hgrid : ∀ j, (floorMarginA k hk).capShift j = (floorMarginB k hk).capShift j :=
    fun j => (floorMargin_cap_grid k hk j).1.trans (floorMargin_cap_grid k hk j).2.symm
  intro hz
  have he := congrArg (fun G : ℤ →₀ CompleteRing => G ((floorMarginA k hk).capShift 0)) hz
  rw [gridDefect_apply_of_common_grid _ _ hgrid 0, Finsupp.zero_apply] at he
  exact floorMargin_all_coordinates_nonzero k hk 0 he

/-- The number of supported union-grid coordinates stays exactly four. -/
theorem floorMargin_support_card (k : ℕ) (hk : 0 < k) :
    (gridDefect (floorMarginA k hk) (floorMarginB k hk)).support.card = 4 := by
  classical
  let A := floorMarginA k hk
  let B := floorMarginB k hk
  have hgrid : ∀ j, A.capShift j = B.capShift j :=
    fun j => (floorMargin_cap_grid k hk j).1.trans (floorMargin_cap_grid k hk j).2.symm
  have hs : (gridDefect A B).support = Finset.univ.image A.capShift := by
    ext d
    constructor
    · intro hd
      have hdn := Finsupp.mem_support_iff.mp hd
      by_cases hx : A.cofactorGridVector d = 0
      · have hy : B.cofactorGridVector d ≠ 0 := by
          intro hy
          exact hdn (by simp [gridDefect, hx, hy])
        obtain ⟨j, hj⟩ := B.exists_capShift_of_gridVector_ne_zero d hy
        exact Finset.mem_image.mpr ⟨j, Finset.mem_univ j, (hgrid j).trans hj⟩
      · obtain ⟨j, hj⟩ := A.exists_capShift_of_gridVector_ne_zero d hx
        exact Finset.mem_image.mpr ⟨j, Finset.mem_univ j, hj⟩
    · intro hd
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hd
      apply Finsupp.mem_support_iff.mpr
      rw [gridDefect_apply_of_common_grid A B hgrid j]
      exact floorMargin_all_coordinates_nonzero k hk j
  rw [hs, Finset.card_image_of_injective _ A.capShift_strictMono.injective]
  simp

theorem floorMargin_firstPositiveShift (k : ℕ) (hk : 0 < k) :
    firstPositiveDefectShift (floorMarginA k hk) (floorMarginB k hk)
        (floorMargin_connected k hk).1 (floorMargin_connected k hk).2
        (floorMargin_gridDefect_ne_zero k hk) = ((3 * k : ℕ) : ℤ) := by
  have hgrid : ∀ j, (floorMarginA k hk).capShift j = (floorMarginB k hk).capShift j :=
    fun j => (floorMargin_cap_grid k hk j).1.trans (floorMargin_cap_grid k hk j).2.symm
  rw [firstPositiveDefectShift_eq_one _ _ (floorMargin_connected k hk).1
    (floorMargin_connected k hk).2 hgrid (floorMargin_gridDefect_ne_zero k hk)
    (floorMargin_all_coordinates_nonzero k hk 1), (floorMargin_cap_grid k hk 1).1]
  rfl

theorem floorMargin_firstPositiveShift_not_floor (k : ℕ) (hk : 0 < k) :
    firstPositiveDefectShift (floorMarginA k hk) (floorMarginB k hk)
        (floorMargin_connected k hk).1 (floorMargin_connected k hk).2
        (floorMargin_gridDefect_ne_zero k hk) ∉
      (positiveFloorFace squareWeight (floorMarginA k hk) (floorMarginB k hk)).image
        (floorMarginA k hk).capShift := by
  rw [floorMargin_firstPositiveShift, floorMargin_floor_shifts, Finset.mem_singleton]
  intro he
  omega

/-- No fixed real slack bounds the first-positive action margin in this three-row family. -/
theorem floorMargin_gap_unbounded (slack : ℝ) :
    ∃ (k : ℕ) (hk : 0 < k), slack < 2 * (k : ℝ) ^ 2 ∧
      defectAction squareWeight (floorMarginA k hk) (floorMarginB k hk) 1 =
        positiveFloor squareWeight (floorMarginA k hk) (floorMarginB k hk) +
          ((2 * (k : ℝ) ^ 2 : ℝ) : WithTop ℝ) := by
  obtain ⟨k, hk⟩ := exists_nat_gt (max slack 0 + 1)
  have hkR : 0 < (k : ℝ) := by have := le_max_right slack 0; linarith
  have hkN : 0 < k := by exact_mod_cast hkR
  refine ⟨k, hkN, ?_, floorMargin_first_action_gap k hkN⟩
  have hslack := le_max_left slack 0
  have hnonneg := le_max_right slack 0
  nlinarith

private noncomputable def fingerprintZeroTerms : Fin 2 → CompleteRing :=
  ![indexMonomial 1 [3, 7], indexMonomial (-1) [4, 6]]

private def fingerprintZeroCosts : Fin 2 → ℝ := ![58, 52]

private theorem fingerprintZeroTerms_valuation (j : Fin 2) :
    monomialValuation squareWeight.generatorWeight (fingerprintZeroTerms j) =
      (fingerprintZeroCosts j : WithTop ℝ) := by
  fin_cases j
  · have hv := indexMonomial_valuation 1 (by norm_num) [3, 7]
    norm_num at hv
    exact hv
  · have hv := indexMonomial_valuation (-1) (by norm_num) [4, 6]
    norm_num at hv
    exact hv

theorem fingerprint_zero_valuation :
    monomialValuation squareWeight.generatorWeight (cofactorDefect fingerprintX fingerprintY 0) =
      (52 : WithTop ℝ) := by
  have hs := finite_terms_minimum fingerprintZeroTerms fingerprintZeroCosts
    fingerprintZeroTerms_valuation (1 : Fin 2) (by
      intro i hi
      fin_cases i
      · norm_num [fingerprintZeroCosts]
      · norm_num at hi)
  have he : (∑ i, fingerprintZeroTerms i) = cofactorDefect fingerprintX fingerprintY 0 := by
    rw [fingerprint_defect]
    simp only [fingerprintZeroTerms, Fin.sum_univ_succ,
      Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_fin_one,
      indexMonomial, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, map_neg, map_one]
    ring
  rw [he] at hs
  dsimp only [fingerprintZeroCosts] at hs
  exact hs.2

private noncomputable def fingerprintFirstTerms : Fin 2 → CompleteRing :=
  ![indexMonomial 1 [1, 6], indexMonomial (-1) [7]]

private def fingerprintFirstCosts : Fin 2 → ℝ := ![37, 49]

private theorem fingerprintFirstTerms_valuation (j : Fin 2) :
    monomialValuation squareWeight.generatorWeight (fingerprintFirstTerms j) =
      (fingerprintFirstCosts j : WithTop ℝ) := by
  fin_cases j
  · have hv := indexMonomial_valuation 1 (by norm_num) [1, 6]
    norm_num at hv
    exact hv
  · have hv := indexMonomial_valuation (-1) (by norm_num) [7]
    norm_num at hv
    exact hv

theorem fingerprint_first_valuation :
    monomialValuation squareWeight.generatorWeight (cofactorDefect fingerprintX fingerprintY 1) =
      (37 : WithTop ℝ) := by
  have hs := finite_terms_minimum fingerprintFirstTerms fingerprintFirstCosts
    fingerprintFirstTerms_valuation (0 : Fin 2) (by
      intro i hi
      fin_cases i
      · norm_num at hi
      · norm_num [fingerprintFirstCosts])
  have he : (∑ i, fingerprintFirstTerms i) = cofactorDefect fingerprintX fingerprintY 1 := by
    rw [fingerprint_defect]
    simp only [fingerprintFirstTerms, Fin.sum_univ_succ,
      Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_fin_one, Matrix.cons_val_one,
      indexMonomial, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, map_neg, map_one]
    ring
  rw [he] at hs
  dsimp only [fingerprintFirstCosts] at hs
  exact hs.2

private noncomputable def fingerprintSecondTerms : Fin 2 → CompleteRing :=
  ![indexMonomial 1 [4], indexMonomial (-1) [1, 3]]

private def fingerprintSecondCosts : Fin 2 → ℝ := ![16, 10]

private theorem fingerprintSecondTerms_valuation (j : Fin 2) :
    monomialValuation squareWeight.generatorWeight (fingerprintSecondTerms j) =
      (fingerprintSecondCosts j : WithTop ℝ) := by
  fin_cases j
  · have hv := indexMonomial_valuation 1 (by norm_num) [4]
    norm_num at hv
    exact hv
  · have hv := indexMonomial_valuation (-1) (by norm_num) [1, 3]
    norm_num at hv
    exact hv

theorem fingerprint_second_valuation :
    monomialValuation squareWeight.generatorWeight (cofactorDefect fingerprintX fingerprintY 2) =
      (10 : WithTop ℝ) := by
  have hs := finite_terms_minimum fingerprintSecondTerms fingerprintSecondCosts
    fingerprintSecondTerms_valuation (1 : Fin 2) (by
      intro i hi
      fin_cases i
      · norm_num [fingerprintSecondCosts]
      · norm_num at hi)
  have he : (∑ i, fingerprintSecondTerms i) = cofactorDefect fingerprintX fingerprintY 2 := by
    rw [fingerprint_defect]
    simp only [fingerprintSecondTerms, Fin.sum_univ_succ,
      Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_fin_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
      indexMonomial, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, map_neg, map_one]
    ring
  rw [he] at hs
  dsimp only [fingerprintSecondCosts] at hs
  exact hs.2

theorem fingerprint_defect_valuations (j : Fin 4) :
    monomialValuation squareWeight.generatorWeight (cofactorDefect fingerprintX fingerprintY j) =
      ![(52 : WithTop ℝ), 37, 10, ⊤] j := by
  fin_cases j
  · exact fingerprint_zero_valuation
  · exact fingerprint_first_valuation
  · exact fingerprint_second_valuation
  · rw [fingerprint_defect]
    exact monomialValuation_zero _

/-- The fingerprint has the stated strict floor even though the actual Schur functions differ. -/
theorem fingerprint_square_actions (j : Fin 4) :
    defectAction squareWeight fingerprintX fingerprintY j = ![(52 : WithTop ℝ), 46, 46, ⊤] j := by
  unfold defectAction
  rw [fingerprint_defect_valuations, (fingerprint_cap_grid j).1]
  fin_cases j <;> norm_num [square_weight_value]

theorem fingerprint_schur_difference :
    fingerprintX.schurFunction - fingerprintY.schurFunction =
      complete 3 * complete 7 - complete 4 * complete 6 :=
  fingerprint_defect 0

theorem fingerprint_schur_ne : fingerprintX.schurFunction ≠ fingerprintY.schurFunction := by
  intro h
  have hz : cofactorDefect fingerprintX fingerprintY 0 = 0 := sub_eq_zero.mpr h
  have hv := fingerprint_zero_valuation
  rw [hz, monomialValuation_zero] at hv
  exact WithTop.coe_ne_top hv.symm

theorem fingerprint_positiveFloor : positiveFloor squareWeight fingerprintX fingerprintY = 46 := by
  apply le_antisymm
  · apply (Finset.inf_le (s := Finset.univ.filter (fun j : Fin 4 => 0 < j.val))
      (f := defectAction squareWeight fingerprintX fingerprintY)
      (by norm_num : (1 : Fin 4) ∈ Finset.univ.filter (fun j : Fin 4 => 0 < j.val))).trans
    rw [fingerprint_square_actions]
    exact le_rfl
  · apply Finset.le_inf
    intro j hj
    have hp := (Finset.mem_filter.mp hj).2
    rw [fingerprint_square_actions]
    fin_cases j <;> norm_num at *

theorem fingerprint_strict_floor :
    positiveFloor squareWeight fingerprintX fingerprintY <
      defectAction squareWeight fingerprintX fingerprintY 0 := by
  rw [fingerprint_positiveFloor, fingerprint_square_actions]
  change (46 : WithTop ℝ) < (52 : WithTop ℝ)
  norm_cast

/-- A genuine strict adjacent-floor fingerprint is not an equality certificate. -/
theorem fingerprint_not_equality_certificate :
    fingerprintX.Connected ∧ fingerprintY.Connected ∧
      fingerprintX.inner = fingerprintY.inner ∧
      positiveFloor squareWeight fingerprintX fingerprintY <
        defectAction squareWeight fingerprintX fingerprintY 0 ∧
      fingerprintX.schurFunction ≠ fingerprintY.schurFunction :=
  ⟨fingerprint_connected.1, fingerprint_connected.2, fingerprint_inner_eq,
    fingerprint_strict_floor, fingerprint_schur_ne⟩

end Diagram
end SkewSchurReconstruction
