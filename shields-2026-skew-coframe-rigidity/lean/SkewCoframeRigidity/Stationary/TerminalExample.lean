/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCoframeRigidity.SpliceExample
import SkewCoframeRigidity.Coframe.Defs

/-!
# Terminal coframes of the equal hooks

Formalizes `shields-2026-skew-coframe-rigidity.tex`, `ex:terminal-coframes`.  For the hooks
`A = (2,1)` and `B = (2,2)/(1)` the complete coherent native matrices have the common
determinant `H₁H₂ - ϑH₃`, both spans equal `3`, and the complete coframes and the defect are
explicit.  Sorry-free.
-/

namespace SkewCoframeRigidity.Coframe

open SkewCofactorIndependence SkewCoframeRigidity Polynomial
open scoped Polynomial Matrix

section Letters

variable {L : Type*} [CommRing L] (h : ℕ → L)

theorem hookA_matrix : fullMatrixOf h hookA = !![h 2, h 3; h 0, h 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [fullMatrixOf, hookA, letterOf]

theorem hookB_matrix : fullMatrixOf h hookB = !![h 1, h 3; h 0, h 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [fullMatrixOf, hookB, letterOf]

theorem hookA_schurOf : schurOf h hookA = h 2 * h 1 - h 3 * h 0 := by
  rw [schurOf, hookA_matrix, Matrix.det_fin_two_of]

theorem hookB_schurOf : schurOf h hookB = h 1 * h 2 - h 3 * h 0 := by
  rw [schurOf, hookB_matrix, Matrix.det_fin_two_of]

theorem hookA_span : span hookA = 3 := by
  simp [span, BetaDiagram.largestLabel, hookA]

theorem hookB_span : span hookB = 3 := by
  simp [span, BetaDiagram.largestLabel, hookB]

end Letters

section FieldCase

variable {L : Type*} [Field L] (h : ℕ → L)

theorem hookA_coframeOf :
    coframeOf h hookA = 1 - C (h 1 / h 0) * X := by
  have hm : properMatrixOf h hookA = !![h 0] := by
    ext i j
    fin_cases i; fin_cases j
    simp [properMatrixOf, hookA, letterOf]
  have hv : topVecOf h hookA = ![h 1] := by
    ext i
    fin_cases i
    simp [topVecOf, hookA, letterOf]
  have hc : colPos hookA 0 = 1 := by simp [colPos, hookA]
  simp only [coframeOf, coframeVecOf, hm, hv, Fin.sum_univ_one, hc]
  rw [Matrix.inv_subsingleton]
  simp [div_eq_inv_mul]
  ring

theorem hookB_coframeOf :
    coframeOf h hookB = 1 - C (h 2 / h 0) * X ^ 2 := by
  have hm : properMatrixOf h hookB = !![h 0] := by
    ext i j
    fin_cases i; fin_cases j
    simp [properMatrixOf, hookB, letterOf]
  have hv : topVecOf h hookB = ![h 2] := by
    ext i
    fin_cases i
    simp [topVecOf, hookB, letterOf]
  have hc : colPos hookB 0 = 2 := by simp [colPos, hookB]
  simp only [coframeOf, coframeVecOf, hm, hv, Fin.sum_univ_one, hc]
  rw [Matrix.inv_subsingleton]
  simp [div_eq_inv_mul]
  ring

/-- The coefficient of `H (1 - a z^k)`. -/
theorem coeff_mk_mul_one_sub (a : L) (k n : ℕ) :
    PowerSeries.coeff n (PowerSeries.mk h * ((1 - C a * X ^ k : L[X]) : PowerSeries L)) =
      h n - if k ≤ n then a * h (n - k) else 0 := by
  have : ((1 - C a * X ^ k : L[X]) : PowerSeries L) =
      1 - PowerSeries.C a * PowerSeries.X ^ k := by simp
  rw [this, mul_sub, mul_one, map_sub, PowerSeries.coeff_mk, mul_left_comm,
    PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_X_pow']
  simp only [PowerSeries.coeff_mk]
  split_ifs <;> simp

/-- Clipping `H (1 - a z^k)` at `3`, coefficientwise. -/
theorem coeff_trunc_mk_mul_one_sub (a : L) (k n : ℕ) :
    (PowerSeries.trunc 3 (PowerSeries.mk h * ((1 - C a * X ^ k : L[X]) : PowerSeries L))).coeff n
      = if n < 3 then h n - (if k ≤ n then a * h (n - k) else 0) else 0 := by
  rw [PowerSeries.coeff_trunc, coeff_mk_mul_one_sub]

theorem trunc3_hookA (a : L) :
    PowerSeries.trunc 3 (PowerSeries.mk h * ((1 - C a * X : L[X]) : PowerSeries L)) =
      C (h 0) + C (h 1 - a * h 0) * X + C (h 2 - a * h 1) * X ^ 2 := by
  have := coeff_trunc_mk_mul_one_sub h a 1
  simp only [pow_one] at this
  ext n
  rw [this]
  rcases n with _ | _ | _ | n
  all_goals simp [Polynomial.coeff_X, Polynomial.coeff_C, Polynomial.coeff_X_pow, -map_sub,
    Polynomial.coeff_C_mul]

theorem trunc3_hookB (b : L) :
    PowerSeries.trunc 3 (PowerSeries.mk h * ((1 - C b * X ^ 2 : L[X]) : PowerSeries L)) =
      C (h 0) + C (h 1) * X + C (h 2 - b * h 0) * X ^ 2 := by
  ext n
  rw [coeff_trunc_mk_mul_one_sub]
  rcases n with _ | _ | _ | n
  all_goals simp [Polynomial.coeff_X, Polynomial.coeff_C, Polynomial.coeff_X_pow, -map_sub,
    Polynomial.coeff_C_mul]

/-- The defect of the equal hooks, for any letter sequence with `h 0 ≠ 0`. -/
theorem hooks_defectOf (h0 : h 0 ≠ 0) :
    clippedOp 3 (coframeOf h hookA) (coframeOf h hookB) (seriesOf h) =
      C (h 2 * (h 0 * h 2 - h 1 ^ 2) / h 0 ^ 2) * X ^ 4 := by
  unfold clippedOp seriesOf
  rw [hookA_coframeOf, hookB_coframeOf, trunc3_hookA, trunc3_hookB]
  have e1 : h 1 = h 1 / h 0 * h 0 := by field_simp
  have e2 : h 2 = h 2 / h 0 * h 0 := by field_simp
  have e3 : h 2 * (h 0 * h 2 - h 1 ^ 2) / h 0 ^ 2 =
      h 2 / h 0 * (h 2 - h 1 / h 0 * h 1) := by field_simp
  rw [e3]
  generalize h 1 / h 0 = a at e1 ⊢
  generalize h 2 / h 0 = b at e2 ⊢
  generalize h 0 = x at *
  generalize h 1 = y at *
  generalize h 2 = w at *
  generalize h 3 = v at *
  subst e1 e2
  simp only [map_sub, map_mul]
  ring

end FieldCase

theorem cohLetters_zero_ne_zero : cohLetters 0 ≠ 0 := by
  unfold cohLetters
  rw [map_ne_zero_iff _ (IsFractionRing.injective CohRing CohField)]
  exact MvPolynomial.X_ne_zero 0

/-- The two hooks have the same coherent Jacobi–Trudi determinant `H₁H₂ - ϑH₃`. -/
theorem hooks_schurOf_eq {L : Type*} [CommRing L] (h : ℕ → L) :
    schurOf h hookA = schurOf h hookB := by
  rw [hookA_schurOf, hookB_schurOf]; ring

/-- The coherent determinant of both hooks over the raw field. -/
theorem hooks_cohSchur_eq :
    algebraMap CohRing CohField (cohSchur hookA) = algebraMap CohRing CohField (cohSchur hookB) :=
  congrArg _ (hooks_schurOf_eq _)

/-- The complete coframe of the hook `(2,1)`: `1 - (H₁/ϑ) z`. -/
theorem coframe_hookA : coframe hookA = 1 - C (cohLetters 1 / cohLetters 0) * X :=
  hookA_coframeOf cohLetters

/-- The complete coframe of the hook `(2,2)/(1)`: `1 - (H₂/ϑ) z²`. -/
theorem coframe_hookB : coframe hookB = 1 - C (cohLetters 2 / cohLetters 0) * X ^ 2 :=
  hookB_coframeOf cohLetters

/-- The proper native equation of the first hook: `ϑ G₁ = -H₁`. -/
theorem hookA_native : cohLetters 0 * (coframe hookA).coeff 1 = -cohLetters 1 := by
  rw [coframe_hookA, Polynomial.coeff_sub, Polynomial.coeff_one, Polynomial.coeff_C_mul,
    Polynomial.coeff_X_one]
  field_simp [cohLetters_zero_ne_zero]
  simp

/-- The proper native equation of the second hook: `ϑ C₂ = -H₂`. -/
theorem hookB_native : cohLetters 0 * (coframe hookB).coeff 2 = -cohLetters 2 := by
  rw [coframe_hookB, Polynomial.coeff_sub, Polynomial.coeff_one, Polynomial.coeff_C_mul,
    Polynomial.coeff_X_pow]
  field_simp [cohLetters_zero_ne_zero]
  simp

/-- The defect of the equal hooks is `H₂(ϑH₂ - H₁²)/ϑ² · z⁴`, of order `4 = 2M - 2`. -/
theorem hooks_defect :
    defect hookA hookB =
      C (cohLetters 2 * (cohLetters 0 * cohLetters 2 - cohLetters 1 ^ 2) / cohLetters 0 ^ 2) *
        X ^ 4 := by
  unfold defect coframe letterSeries
  rw [hookA_span]
  exact hooks_defectOf cohLetters cohLetters_zero_ne_zero

end SkewCoframeRigidity.Coframe
