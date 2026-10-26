/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewSchurReconstruction.RatioRigidity
import SkewSchurReconstruction.BoundaryReconstruction

/-!
# Exact witnesses for boundary observations

Formalizes "Reconstruction from two positive extensions" (`subsec:two-positive-extensions`,
`rem:one-extension-insufficient`), "Application to actual skew Schur equality"
(`subsec:actual-equality`, `ex:actual-equal-chain`), and the scope warning
`rem:realizability-terminal`.  The witness family is parametric in every positive extension
length, not a finite search. Sorry-free.
-/

namespace SkewSchurReconstruction
namespace Diagram

open scoped BigOperators

private theorem square_weight_value (k : ℕ) : squareWeight.weight k = (k : ℝ) ^ 2 := rfl

/-- The first parent in the parametric one-observation counterexample. -/
def oneObservationU (a : ℕ) (ha : 0 < a) : Diagram 3 where
  outer := ![6 * a - 2, 5 * a - 1, 2 * a]
  inner := ![4 * a - 2, 2 * a - 1, 0]
  outer_antitone := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all <;> omega
  inner_antitone := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp only [Matrix.cons_val_zero', Matrix.cons_val_succ', Fin.le_def] at * <;> omega
  row_nonempty := by
    intro i
    fin_cases i <;> simp <;> omega

/-- The second parent in the parametric one-observation counterexample. -/
def oneObservationV (a : ℕ) (ha : 0 < a) : Diagram 3 where
  outer := ![6 * a - 2, 4 * a - 1, 3 * a]
  inner := ![4 * a - 2, 2 * a - 1, 0]
  outer_antitone := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all <;> omega
  inner_antitone := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp only [Matrix.cons_val_zero', Matrix.cons_val_succ', Fin.le_def] at * <;> omega
  row_nonempty := by
    intro i
    fin_cases i <;> simp <;> omega

theorem oneObservationU_connected (a : ℕ) (ha : 0 < a) : (oneObservationU a ha).Connected := by
  refine ⟨by omega, ?_⟩
  intro i hi
  fin_cases i
  · change 4 * a - 2 < 5 * a - 1
    omega
  · change 2 * a - 1 < 2 * a
    omega
  · change 2 + 1 < 3 at hi
    omega

theorem oneObservationV_connected (a : ℕ) (ha : 0 < a) : (oneObservationV a ha).Connected := by
  refine ⟨by omega, ?_⟩
  intro i hi
  fin_cases i
  · change 4 * a - 2 < 4 * a - 1
    omega
  · change 2 * a - 1 < 3 * a
    omega
  · change 2 + 1 < 3 at hi
    omega

theorem oneObservation_inner_eq (a : ℕ) (ha : 0 < a) :
    (oneObservationU a ha).inner = (oneObservationV a ha).inner := rfl

theorem oneObservationU_rowParam (a : ℕ) (ha : 0 < a) (i : Fin 3) :
    (oneObservationU a ha).rowParam i = ![0, (a : ℤ), ((4 * a : ℕ) : ℤ)] i := by
  fin_cases i <;> simp [rowParam, top, oneObservationU] <;> omega

theorem oneObservationV_rowParam (a : ℕ) (ha : 0 < a) (i : Fin 3) :
    (oneObservationV a ha).rowParam i = ![0, ((2 * a : ℕ) : ℤ), ((3 * a : ℕ) : ℤ)] i := by
  fin_cases i <;> simp [rowParam, top, oneObservationV] <;> omega

theorem oneObservationU_capShift (a : ℕ) (ha : 0 < a) (j : Fin 4) :
    (oneObservationU a ha).capShift j =
      ![0, ((2 * a : ℕ) : ℤ), ((4 * a : ℕ) : ℤ), ((6 * a : ℕ) : ℤ)] j := by
  fin_cases j <;> simp [capShift, top, oneObservationU] <;> omega

theorem oneObservationV_capShift (a : ℕ) (ha : 0 < a) (j : Fin 4) :
    (oneObservationV a ha).capShift j =
      ![0, ((2 * a : ℕ) : ℤ), ((4 * a : ℕ) : ℤ), ((6 * a : ℕ) : ℤ)] j := by
  fin_cases j <;> simp [capShift, top, oneObservationV] <;> omega

theorem oneObservationU_capMatrix (a : ℕ) (ha : 0 < a) :
    (oneObservationU a ha).capMatrix = Matrix.of
      ![![1, complete ((2 * a : ℕ) : ℤ), complete ((4 * a : ℕ) : ℤ),
          complete ((6 * a : ℕ) : ℤ)],
        ![0, complete (a : ℤ), complete ((3 * a : ℕ) : ℤ), complete ((5 * a : ℕ) : ℤ)],
        ![0, 0, 1, complete ((2 * a : ℕ) : ℤ)]] := by
  apply Matrix.ext
  intro i j
  rw [capMatrix]
  simp only [Matrix.of_apply, oneObservationU_rowParam, oneObservationU_capShift]
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.cons_val_zero', Matrix.cons_val_succ', sub_self, complete_zero] <;>
    first | rfl | exact complete_of_neg (by omega) | apply congrArg complete; omega

theorem oneObservationV_capMatrix (a : ℕ) (ha : 0 < a) :
    (oneObservationV a ha).capMatrix = Matrix.of
      ![![1, complete ((2 * a : ℕ) : ℤ), complete ((4 * a : ℕ) : ℤ),
          complete ((6 * a : ℕ) : ℤ)],
        ![0, 1, complete ((2 * a : ℕ) : ℤ), complete ((4 * a : ℕ) : ℤ)],
        ![0, 0, complete (a : ℤ), complete ((3 * a : ℕ) : ℤ)]] := by
  apply Matrix.ext
  intro i j
  rw [capMatrix]
  simp only [Matrix.of_apply, oneObservationV_rowParam, oneObservationV_capShift]
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.cons_val_zero', Matrix.cons_val_succ', sub_self, complete_zero] <;>
    first | rfl | exact complete_of_neg (by omega) | apply congrArg complete; omega

/-- Every maximal-cofactor difference in the parametric parent pair. -/
theorem oneObservation_defect (a : ℕ) (ha : 0 < a) (j : Fin 4) :
    cofactorDefect (oneObservationU a ha) (oneObservationV a ha) j =
      ![complete ((3 * a : ℕ) : ℤ) * complete ((4 * a : ℕ) : ℤ) -
          complete ((2 * a : ℕ) : ℤ) * complete ((5 * a : ℕ) : ℤ),
        complete ((5 * a : ℕ) : ℤ) - complete (a : ℤ) * complete ((4 * a : ℕ) : ℤ),
        complete (a : ℤ) * complete ((2 * a : ℕ) : ℤ) - complete ((3 * a : ℕ) : ℤ), 0] j := by
  unfold cofactorDefect cofactor signedMaximalCofactor
  rw [oneObservationU_capMatrix, oneObservationV_capMatrix]
  fin_cases j <;>
    norm_num [Matrix.det_fin_three, Matrix.submatrix_apply, Matrix.of_apply, Fin.succAbove] <;> ring

/-- The parent Schur functions differ by the stated two monomials. -/
theorem oneObservation_schur_difference (a : ℕ) (ha : 0 < a) :
    (oneObservationU a ha).schurFunction - (oneObservationV a ha).schurFunction =
      complete ((3 * a : ℕ) : ℤ) * complete ((4 * a : ℕ) : ℤ) -
        complete ((2 * a : ℕ) : ℤ) * complete ((5 * a : ℕ) : ℤ) := by
  exact oneObservation_defect a ha 0

/-- A single extension of the prescribed length has equal actual Schur functions. -/
theorem oneObservation_extension_eq (a : ℕ) (ha : 0 < a) :
    ((oneObservationU a ha).extendNortheast a ha).schurFunction =
      ((oneObservationV a ha).extendNortheast a ha).schurFunction := by
  rw [schurFunction_extendNortheast, schurFunction_extendNortheast]
  apply sub_eq_zero.mp
  unfold capPolynomial
  rw [← Finset.sum_sub_distrib]
  have hterm : ∀ j : Fin 4,
      (oneObservationU a ha).cofactor j * complete ((a : ℤ) + (oneObservationU a ha).capShift j) -
        (oneObservationV a ha).cofactor j * complete ((a : ℤ) + (oneObservationV a ha).capShift j) =
      cofactorDefect (oneObservationU a ha) (oneObservationV a ha) j *
        complete ((a : ℤ) + (oneObservationU a ha).capShift j) := by
    intro j
    rw [oneObservationV_capShift, oneObservationU_capShift]
    unfold cofactorDefect
    ring
  simp_rw [hterm, oneObservation_defect, oneObservationU_capShift]
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_one]
  have e3 : (a : ℤ) + ((2 * a : ℕ) : ℤ) = ((3 * a : ℕ) : ℤ) := by omega
  have e5 : (a : ℤ) + ((4 * a : ℕ) : ℤ) = ((5 * a : ℕ) : ℤ) := by omega
  simp only [Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_fin_one,
    add_zero, e3, e5, zero_mul, add_zero]
  ring

/-- The square valuation distinguishes the two parent monomials for every positive scale. -/
theorem oneObservation_difference_valuation (a : ℕ) (ha : 0 < a) :
    monomialValuation squareWeight.generatorWeight
      (complete ((3 * a : ℕ) : ℤ) * complete ((4 * a : ℕ) : ℤ) -
        complete ((2 * a : ℕ) : ℤ) * complete ((5 * a : ℕ) : ℤ)) =
      ((25 * (a : ℝ) ^ 2 : ℝ) : WithTop ℝ) := by
  have h2 := complete_ne_zero_of_nonneg (((2 * a : ℕ) : ℤ)) (by omega)
  have h3 := complete_ne_zero_of_nonneg (((3 * a : ℕ) : ℤ)) (by omega)
  have h4 := complete_ne_zero_of_nonneg (((4 * a : ℕ) : ℤ)) (by omega)
  have h5 := complete_ne_zero_of_nonneg (((5 * a : ℕ) : ℤ)) (by omega)
  have hp := mul_ne_zero h3 h4
  have hq := mul_ne_zero h2 h5
  have hlp : leastWeight squareWeight.generatorWeight
      (complete ((3 * a : ℕ) : ℤ) * complete ((4 * a : ℕ) : ℤ)) =
      25 * (a : ℝ) ^ 2 := by
    rw [leastWeight_mul h3 h4, complete_leastWeight squareWeight _ (by omega),
      complete_leastWeight squareWeight _ (by omega)]
    simp only [square_weight_value, Int.toNat_natCast]
    push_cast
    ring
  have hlq : leastWeight squareWeight.generatorWeight
      (complete ((2 * a : ℕ) : ℤ) * complete ((5 * a : ℕ) : ℤ)) =
      29 * (a : ℝ) ^ 2 := by
    rw [leastWeight_mul h2 h5, complete_leastWeight squareWeight _ (by omega),
      complete_leastWeight squareWeight _ (by omega)]
    simp only [square_weight_value, Int.toNat_natCast]
    push_cast
    ring
  have hlt : monomialValuation squareWeight.generatorWeight
      (complete ((3 * a : ℕ) : ℤ) * complete ((4 * a : ℕ) : ℤ)) <
      monomialValuation squareWeight.generatorWeight
        (complete ((2 * a : ℕ) : ℤ) * complete ((5 * a : ℕ) : ℤ)) := by
    rw [monomialValuation_eq_coe hp, monomialValuation_eq_coe hq, hlp, hlq]
    apply WithTop.coe_lt_coe.mpr
    have haR : 0 < (a : ℝ) := by exact_mod_cast ha
    nlinarith [sq_pos_of_pos haR]
  rw [monomialValuation_sub_eq_min hlt.ne, min_eq_left hlt.le,
    monomialValuation_eq_coe hp, hlp]

theorem oneObservation_schur_ne (a : ℕ) (ha : 0 < a) :
    (oneObservationU a ha).schurFunction ≠ (oneObservationV a ha).schurFunction := by
  intro he
  have hz := sub_eq_zero.mpr he
  rw [oneObservation_schur_difference] at hz
  have hv := oneObservation_difference_valuation a ha
  rw [hz, monomialValuation_zero] at hv
  exact WithTop.coe_ne_top hv.symm

theorem oneObservation_not_translationEquivalent (a : ℕ) (ha : 0 < a) :
    ¬TranslationEquivalent (oneObservationU a ha) (oneObservationV a ha) := by
  intro h
  obtain ⟨_, t, ht⟩ := h
  have hi := (ht (2 : Fin 3) (2 : Fin 3) rfl).2
  have ho := (ht (1 : Fin 3) (1 : Fin 3) rfl).1
  simp [oneObservationU, oneObservationV] at hi ho
  omega

/-- `rem:one-extension-insufficient`, quantified over every prescribed positive length. -/
theorem one_extension_insufficient (a : ℕ) (ha : 0 < a) :
    ∃ U V : Diagram 3, U.Connected ∧ V.Connected ∧ U.inner = V.inner ∧
      (U.extendNortheast a ha).schurFunction = (V.extendNortheast a ha).schurFunction ∧
      U.schurFunction ≠ V.schurFunction :=
  ⟨oneObservationU a ha, oneObservationV a ha, oneObservationU_connected a ha,
    oneObservationV_connected a ha, oneObservation_inner_eq a ha,
    oneObservation_extension_eq a ha, oneObservation_schur_ne a ha⟩

/-- The first actual equal parent in `ex:actual-equal-chain`. -/
def equalChainX : Diagram 4 := (oneObservationU 1 (by omega)).extendNortheast 1 (by omega)

/-- The second actual equal parent in `ex:actual-equal-chain`. -/
def equalChainY : Diagram 4 := (oneObservationV 1 (by omega)).extendNortheast 1 (by omega)

theorem equalChainX_boundaries :
    equalChainX.outer = ![4, 4, 4, 2] ∧ equalChainX.inner = ![3, 2, 1, 0] := by
  constructor
  · funext i
    cases i using Fin.cases with
    | zero =>
        norm_num [equalChainX, extendNortheast_outer_zero, extensionTop, top, oneObservationU]
    | succ i =>
        simp only [equalChainX, extendNortheast_outer_succ, Matrix.cons_val_succ]
        rfl
  · funext i
    cases i using Fin.cases with
    | zero => norm_num [equalChainX, extendNortheast_inner_zero, top, oneObservationU]
    | succ i =>
        simp only [equalChainX, extendNortheast_inner_succ, Matrix.cons_val_succ]
        rfl

theorem equalChainY_boundaries :
    equalChainY.outer = ![4, 4, 3, 3] ∧ equalChainY.inner = ![3, 2, 1, 0] := by
  constructor
  · funext i
    cases i using Fin.cases with
    | zero =>
        norm_num [equalChainY, extendNortheast_outer_zero, extensionTop, top, oneObservationV]
    | succ i =>
        simp only [equalChainY, extendNortheast_outer_succ, Matrix.cons_val_succ]
        rfl
  · funext i
    cases i using Fin.cases with
    | zero => norm_num [equalChainY, extendNortheast_inner_zero, top, oneObservationV]
    | succ i =>
        simp only [equalChainY, extendNortheast_inner_succ, Matrix.cons_val_succ]
        rfl

theorem equalChain_connected : equalChainX.Connected ∧ equalChainY.Connected :=
  ⟨(oneObservationU 1 (by omega)).extendNortheast_connected 1 (by omega)
      (oneObservationU_connected 1 (by omega)),
    (oneObservationV 1 (by omega)).extendNortheast_connected 1 (by omega)
      (oneObservationV_connected 1 (by omega))⟩

theorem equalChain_schur_eq : equalChainX.schurFunction = equalChainY.schurFunction :=
  oneObservation_extension_eq 1 (by omega)

theorem equalChain_cap_grid (j : Fin 5) :
    equalChainX.capShift j = ![0, 1, 3, 5, 7] j ∧
      equalChainY.capShift j = ![0, 1, 3, 5, 7] j := by
  cases j using Fin.cases with
  | zero => simp [equalChainX, equalChainY]
  | succ j =>
      simp only [equalChainX, equalChainY, extendNortheast_capShift_succ,
        oneObservationU_capShift, oneObservationV_capShift]
      fin_cases j <;> norm_num

theorem equalChain_row_grids (i : Fin 4) :
    equalChainX.rowParam i = ![0, 1, 2, 5] i ∧
      equalChainY.rowParam i = ![0, 1, 3, 4] i := by
  cases i using Fin.cases with
  | zero =>
      constructor
      · exact extendNortheast_rowParam_zero _ 1 (by omega)
      · exact extendNortheast_rowParam_zero _ 1 (by omega)
  | succ i =>
      simp only [equalChainX, equalChainY, extendNortheast_rowParam_succ,
        oneObservationU_rowParam, oneObservationV_rowParam]
      fin_cases i <;> norm_num

theorem equalChain_defect (j : Fin 5) :
    cofactorDefect equalChainX equalChainY j =
      ![0, complete 2 * complete 5 - complete 3 * complete 4,
        complete 1 * complete 4 - complete 5, complete 3 - complete 1 * complete 2, 0] j := by
  cases j using Fin.cases with
  | zero => exact cofactorDefect_zero_of_schur_eq _ _ equalChain_schur_eq
  | succ j =>
      rw [equalChainX, equalChainY, cofactorDefect_extend_succ, oneObservation_defect]
      fin_cases j <;> norm_num

private theorem equalChain_second_valuation :
    monomialValuation squareWeight.generatorWeight (complete 1 * complete 4 - complete 5) =
      (17 : WithTop ℝ) := by
  have hp : complete 1 * complete 4 ≠ 0 := mul_ne_zero
    (complete_ne_zero_of_nonneg _ (by omega)) (complete_ne_zero_of_nonneg _ (by omega))
  have hlp : leastWeight squareWeight.generatorWeight (complete 1 * complete 4) = 17 := by
    rw [leastWeight_mul (complete_ne_zero_of_nonneg _ (by omega))
        (complete_ne_zero_of_nonneg _ (by omega)),
      complete_leastWeight squareWeight _ (by omega),
      complete_leastWeight squareWeight _ (by omega)]
    norm_num [square_weight_value]
  have hvq := complete_monomialValuation squareWeight (5 : ℤ) (by omega)
  have hw5 : squareWeight.weight (5 : ℤ).toNat = (25 : ℝ) := by
    rw [square_weight_value]
    norm_num
  rw [hw5] at hvq
  have hlt : monomialValuation squareWeight.generatorWeight (complete 1 * complete 4) <
      monomialValuation squareWeight.generatorWeight (complete 5) := by
    rw [monomialValuation_eq_coe hp, hlp, hvq]
    exact WithTop.coe_lt_coe.mpr (by norm_num)
  rw [monomialValuation_sub_eq_min hlt.ne, min_eq_left hlt.le,
    monomialValuation_eq_coe hp, hlp]
  norm_cast

private theorem equalChain_third_valuation :
    monomialValuation squareWeight.generatorWeight (complete 3 - complete 1 * complete 2) =
      (5 : WithTop ℝ) := by
  have hp : complete 1 * complete 2 ≠ 0 := mul_ne_zero
    (complete_ne_zero_of_nonneg _ (by omega)) (complete_ne_zero_of_nonneg _ (by omega))
  have hlp : leastWeight squareWeight.generatorWeight (complete 1 * complete 2) = 5 := by
    rw [leastWeight_mul (complete_ne_zero_of_nonneg _ (by omega))
        (complete_ne_zero_of_nonneg _ (by omega)),
      complete_leastWeight squareWeight _ (by omega),
      complete_leastWeight squareWeight _ (by omega)]
    norm_num [square_weight_value]
  have hvq := complete_monomialValuation squareWeight (3 : ℤ) (by omega)
  have hw3 : squareWeight.weight (3 : ℤ).toNat = (9 : ℝ) := by
    rw [square_weight_value]
    norm_num
  rw [hw3] at hvq
  have hlt : monomialValuation squareWeight.generatorWeight (complete 1 * complete 2) <
      monomialValuation squareWeight.generatorWeight (complete 3) := by
    rw [monomialValuation_eq_coe hp, hlp, hvq]
    exact WithTop.coe_lt_coe.mpr (by norm_num)
  rw [monomialValuation_sub_eq_min hlt.ne', min_eq_right hlt.le,
    monomialValuation_eq_coe hp, hlp]
  norm_cast

theorem equalChain_first_valuation :
    monomialValuation squareWeight.generatorWeight
      (complete 2 * complete 5 - complete 3 * complete 4) =
      (25 : WithTop ℝ) := by
  have he : complete 2 * complete 5 - complete 3 * complete 4 =
      -(complete 3 * complete 4 - complete 2 * complete 5) := by ring
  rw [he, monomialValuation_neg]
  have hh := oneObservation_difference_valuation 1 (by omega)
  simp only [Nat.cast_one, one_pow, mul_one] at hh
  convert hh using 1

private theorem equalChain_defect_valuations (j : Fin 5) :
    monomialValuation squareWeight.generatorWeight (cofactorDefect equalChainX equalChainY j) =
      ![⊤, (25 : WithTop ℝ), 17, 5, ⊤] j := by
  rw [equalChain_defect]
  fin_cases j
  · change monomialValuation squareWeight.generatorWeight 0 = ⊤
    exact monomialValuation_zero _
  · change monomialValuation squareWeight.generatorWeight
      (complete 2 * complete 5 - complete 3 * complete 4) = (25 : WithTop ℝ)
    exact equalChain_first_valuation
  · change monomialValuation squareWeight.generatorWeight
      (complete 1 * complete 4 - complete 5) = (17 : WithTop ℝ)
    exact equalChain_second_valuation
  · change monomialValuation squareWeight.generatorWeight
      (complete 3 - complete 1 * complete 2) = (5 : WithTop ℝ)
    exact equalChain_third_valuation
  · change monomialValuation squareWeight.generatorWeight 0 = ⊤
    exact monomialValuation_zero _

/-- The normalized square actions of the actual equal pair are `(infinity,26,26,30,infinity)`. -/
theorem equalChain_square_actions (j : Fin 5) :
    defectAction squareWeight equalChainX equalChainY j =
      ![⊤, (26 : WithTop ℝ), 26, 30, ⊤] j := by
  unfold defectAction
  rw [equalChain_defect_valuations, (equalChain_cap_grid j).1]
  fin_cases j <;> norm_num [square_weight_value]

/-- The example's two exact common-row relations. -/
theorem equalChain_kernel_relations :
    complete 1 * cofactorDefect equalChainX equalChainY 1 +
        complete 3 * cofactorDefect equalChainX equalChainY 2 +
        complete 5 * cofactorDefect equalChainX equalChainY 3 = 0 ∧
      cofactorDefect equalChainX equalChainY 1 +
        complete 2 * cofactorDefect equalChainX equalChainY 2 +
        complete 4 * cofactorDefect equalChainX equalChainY 3 = 0 := by
  constructor <;> rw [equalChain_defect, equalChain_defect, equalChain_defect] <;>
    norm_num <;> ring

theorem equalChain_first_row_deletions_ne :
    equalChainX.deleteFirstRow.schurFunction ≠ equalChainY.deleteFirstRow.schurFunction := by
  simpa only [equalChainX, equalChainY, deleteFirstRow_extendNortheast] using
    oneObservation_schur_ne 1 (by omega)

private theorem equalChain_tilted_zero (j : Fin 5) :
    defectTiltedCost squareWeight equalChainX equalChainY 0 j =
      defectAction squareWeight equalChainX equalChainY j := by
  simp only [defectTiltedCost, ite_eq_left (equalChainX.capShift_nonneg j), sub_zero,
    defectAction]

private theorem equalChain_tilted_one (j : Fin 5) :
    defectTiltedCost squareWeight equalChainX equalChainY 1 j =
      ![⊤, (25 : WithTop ℝ), 21, 21, ⊤] j := by
  unfold defectTiltedCost
  rw [equalChain_defect_valuations, (equalChain_cap_grid j).1]
  fin_cases j <;> norm_num [square_weight_value]

theorem equalChain_zero_minimizers :
    defectMinimizers squareWeight equalChainX equalChainY 0 = {1, 2} := by
  classical
  apply Finset.ext
  intro j
  fin_cases j <;>
    norm_num [mem_defectMinimizers, Fin.forall_fin_succ,
      equalChain_tilted_zero, equalChain_square_actions] <;> norm_cast

theorem equalChain_one_minimizers :
    defectMinimizers squareWeight equalChainX equalChainY 1 = {2, 3} := by
  classical
  apply Finset.ext
  intro j
  fin_cases j <;>
    norm_num [mem_defectMinimizers, Fin.forall_fin_succ, equalChain_tilted_one] <;> norm_cast

end Diagram

/-- The formal one-coordinate vector excluded by own `P0=0` in `rem:realizability-terminal`. -/
noncomputable def formalTerminalVector : ℤ →₀ CompleteRing := Finsupp.single 0 1

theorem formalTerminalVector_ratio_all (a : ℕ) : RatioIdentity formalTerminalVector 0 a := by
  simp only [RatioIdentity, formalTerminalVector, gridResponse_single, Nat.cast_zero,
    zero_add, add_zero, complete_zero, one_mul, mul_one]

theorem formalTerminalVector_response_zero : gridResponse formalTerminalVector 0 = 1 := by
  simp [formalTerminalVector]

theorem formalTerminalVector_not_actual {n m : ℕ} (X : Diagram n) (Y : Diagram m)
    (hX : X.Connected) (hY : Y.Connected) : gridDefect X Y ≠ formalTerminalVector := by
  intro h
  have hz := gridDefect_response_zero X Y hX.1 hY.1
  rw [h, formalTerminalVector_response_zero] at hz
  exact one_ne_zero hz

theorem formalTerminalVector_terminal_failure (D : ℤ) (a : ℕ) (ha : D < (a : ℤ)) :
    RatioIdentity formalTerminalVector 0 a ∧
      formalTerminalVector.support = {0} ∧ 0 + (0 : ℤ) + a > D := by
  refine ⟨formalTerminalVector_ratio_all a, ?_, ?_⟩
  · simp [formalTerminalVector]
  · omega

end SkewSchurReconstruction
