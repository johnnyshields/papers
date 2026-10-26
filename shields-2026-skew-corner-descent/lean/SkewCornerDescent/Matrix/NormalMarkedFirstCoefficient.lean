/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.HessenbergMarkedActivityDerivative

/-!
# First coefficient of a complete marked cost expansion

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
Vanishing below the first marked cost removes whole activities; the retained
cost keeps its complete normal activity before the residue projection.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix

/-- The first possible marked cost contributes exactly its full activity residue. -/
theorem normal_marked_first_coeff {ι F : Type*} [Fintype ι] [CommRing F]
    (admissible : ι → Prop) [DecidablePred admissible]
    (cost : ι → ℕ) (marked : ι → PowerSeries F) (a : F) (q : ℕ)
    (hprev : ∀ i, admissible i → cost i < q → marked i = 0) :
    PowerSeries.coeff q (∑ i, if admissible i then
      (-1 : PowerSeries F) ^ cost i * (PowerSeries.X * PowerSeries.C a) ^ cost i * marked i
      else 0) =
    (-1 : F) ^ q * a ^ q * PowerSeries.constantCoeff
      (∑ i, if admissible i ∧ cost i = q then marked i else 0) := by
  rw [map_sum, map_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : admissible i
  · rw [ite_eq_left hi, normal_cost_prefactor_coeff]
    by_cases hc : cost i = q
    · have hterm : admissible i ∧ cost i = q := ⟨hi, hc⟩
      rw [ite_eq_left hterm, hc, ite_eq_left le_rfl, Nat.sub_self,
        PowerSeries.coeff_zero_eq_constantCoeff_apply]
    · have hnot : ¬ (admissible i ∧ cost i = q) := fun h => hc h.2
      rw [ite_eq_right hnot, map_zero, mul_zero]
      by_cases hle : cost i ≤ q
      · rw [ite_eq_left hle, hprev i hi (by omega), map_zero, mul_zero]
      · rw [ite_eq_right hle]
  · have hnot : ¬ (admissible i ∧ cost i = q) := fun h => hi h.1
    rw [ite_eq_right hi, ite_eq_right hnot, map_zero, map_zero, mul_zero]

end SkewCornerDescent.Matrix
