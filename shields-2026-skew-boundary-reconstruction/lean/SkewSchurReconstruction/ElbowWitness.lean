/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewSchurReconstruction.ElbowVectors
import SkewSchurReconstruction.BoundarySeparation
import Mathlib.Algebra.Order.Ring.WithTop

/-!
# A formal ratio vector outside the leftmost floor

The three-point example in `subsec:elbow` has square actions 20, 18, 18.
Its two exact cap relations do not force the leftmost positive supported shift
onto the positive floor.  No cofactor realization is asserted.
-/

namespace SkewSchurReconstruction

open scoped Matrix

/-- The shifts of the smallest positive-grid elbow witness. -/
def elbowWitnessShifts : Fin 3 → ℤ := ![1, 2, 3]

/-- The actual square actions of the elbow witness. -/
theorem elbowWitness_actions (i : Fin 3) :
    monomialValuation squareWeight.generatorWeight
        (elbowCoefficients elbowWitnessShifts 1 1 i) +
      (squareWeight.weight (elbowWitnessShifts i).toNat : WithTop ℝ) =
        (![20, 18, 18] : Fin 3 → WithTop ℝ) i := by
  have hc1 := complete_monomialValuation squareWeight 1 (by omega)
  have hc2 := complete_monomialValuation squareWeight 2 (by omega)
  have hc3 := complete_monomialValuation squareWeight 3 (by omega)
  have hy1 := (boundary_ratio_kernel squareWeight 1 1 1 (by omega) (by omega)
    (by omega)).2.2
  have hy2 := (boundary_ratio_kernel squareWeight 1 1 2 (by omega) (by omega)
    (by omega)).2.2
  have hy3 := (boundary_ratio_kernel squareWeight 1 1 3 (by omega) (by omega)
    (by omega)).2.2
  change monomialValuation squareWeight.generatorWeight (elbowRemainder 1 1 1) = _ at hy1
  change monomialValuation squareWeight.generatorWeight (elbowRemainder 1 1 2) = _ at hy2
  change monomialValuation squareWeight.generatorWeight (elbowRemainder 1 1 3) = _ at hy3
  have hw (k : ℕ) : squareWeight.weight k = (k : ℝ) ^ 2 := rfl
  simp only [hw] at hc1 hc2 hc3 hy1 hy2 hy3
  norm_num at hc1 hc2 hc3 hy1 hy2 hy3
  have hc1 : monomialValuation squareWeight.generatorWeight (complete 1) = 1 := by
    simpa using hc1
  have hc2 : monomialValuation squareWeight.generatorWeight (complete 2) = 4 := by
    simpa using hc2
  have hc3 : monomialValuation squareWeight.generatorWeight (complete 3) = 9 := by
    simpa using hc3
  fin_cases i <;>
    norm_num [elbowCoefficients, cross_apply, elbowWitnessShifts, hw]
  · change monomialValuation squareWeight.generatorWeight
      (complete 2 * elbowRemainder 1 1 3 - complete 3 * elbowRemainder 1 1 2) + 1 = 20
    have hp : monomialValuation squareWeight.generatorWeight
        (complete 2 * elbowRemainder 1 1 3) = 21 := by
      rw [monomialValuation_mul, hc2, hy3]
      norm_cast
    have hq : monomialValuation squareWeight.generatorWeight
        (complete 3 * elbowRemainder 1 1 2) = 19 := by
      rw [monomialValuation_mul, hc3, hy2]
      norm_cast
    rw [monomialValuation_sub_eq_min (by rw [hp, hq]; norm_cast), hp, hq,
      min_eq_right (by norm_cast)]
    norm_cast
  · change monomialValuation squareWeight.generatorWeight
      (complete 3 * elbowRemainder 1 1 1 - complete 1 * elbowRemainder 1 1 3) + 4 = 18
    have hp : monomialValuation squareWeight.generatorWeight
        (complete 3 * elbowRemainder 1 1 1) = 14 := by
      rw [monomialValuation_mul, hc3, hy1]
      norm_cast
    have hq : monomialValuation squareWeight.generatorWeight
        (complete 1 * elbowRemainder 1 1 3) = 18 := by
      rw [monomialValuation_mul, hc1, hy3]
      norm_cast
    rw [monomialValuation_sub_eq_min (by rw [hp, hq]; norm_cast), hp, hq,
      min_eq_left (by norm_cast)]
    norm_cast
  · change monomialValuation squareWeight.generatorWeight
      (complete 1 * elbowRemainder 1 1 2 - complete 2 * elbowRemainder 1 1 1) + 9 = 18
    have hp : monomialValuation squareWeight.generatorWeight
        (complete 1 * elbowRemainder 1 1 2) = 11 := by
      rw [monomialValuation_mul, hc1, hy2]
      norm_cast
    have hq : monomialValuation squareWeight.generatorWeight
        (complete 2 * elbowRemainder 1 1 1) = 9 := by
      rw [monomialValuation_mul, hc2, hy1]
      norm_cast
    rw [monomialValuation_sub_eq_min (by rw [hp, hq]; norm_cast), hp, hq,
      min_eq_right (by norm_cast)]
    norm_cast

end SkewSchurReconstruction
