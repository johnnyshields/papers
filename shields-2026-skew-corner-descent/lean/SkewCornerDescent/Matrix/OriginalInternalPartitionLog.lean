/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalInternalMarkedCoefficient
import SkewCornerDescent.Matrix.OriginalInternalNextLogFrontier
import SkewCornerDescent.Matrix.LogIndependentMultiplier

/-!
# Complete original partition logarithm at the next marked cost

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
Every inverse diagonal remains a whole normal series. Its actual protected
independence removes its logarithmic derivative, not its normal coefficients.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing CyclicWindows

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The original determinant's normalized logarithm equals the full partition
coefficient derivative minus its entire first-coefficient correction. -/
theorem originalInternal_partition_log_next {n : ℕ} (P : Profile n)
    [NeZero (originalSelectedCount (hD := hD) P)]
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ))
    (r d : ℕ) (hn : 2 ≤ d * r)
    (hp : Function.Periodic
      (fun x => c.originalCompletedGap P ((ZMod.finEquiv _).symm x))
      (r : ZMod (originalSelectedCount (hD := hD) P)))
    (J H : ℕ+)
    (hH : (H : ℤ) = d • windowSum
      (fun x => c.originalCompletedGap P ((ZMod.finEquiv _).symm x)) 1 r 0 + (J : ℤ)) :
    let K := c.originalInternalPeriodHigherIndex P r d hn hp J H hH
    let δ := residueGeneratorDeriv c.top ⟨K.val, ne_of_gt K.property⟩
    let A := (c.originalInternalResponseMatrix P).map c.normalSeries
    let p := A.det
    let F := p * ∏ j, (A j j)⁻¹
    δ (PowerSeries.coeff (d * r)
      (PowerSeries.logOf (PowerSeries.C (PowerSeries.constantCoeff p)⁻¹ * p))) =
      δ (PowerSeries.coeff (d * r) F) -
        PowerSeries.coeff 1 F * δ (PowerSeries.coeff (d * r - 1) F) := by
  let K := c.originalInternalPeriodHigherIndex P r d hn hp J H hH
  let δ := residueGeneratorDeriv c.top ⟨K.val, ne_of_gt K.property⟩
  let A := (c.originalInternalResponseMatrix P).map c.normalSeries
  let p := A.det
  let w := fun j => (A j j)⁻¹
  let U := ∏ j, w j
  let F := p * U
  have hheight : d • windowSum
      (fun x => c.originalCompletedGap P ((ZMod.finEquiv _).symm x)) 1 r 0 < (K.val : ℤ) := by
    change d • windowSum
      (fun x => c.originalCompletedGap P ((ZMod.finEquiv _).symm x)) 1 r 0 < (H : ℤ)
    have hJ := J.pos
    omega
  have hmap : c.normalSeries (c.originalInternalResponseMatrix P).det = p := by
    rw [RingHom.map_det]
    rfl
  have hunit (j) : PowerSeries.constantCoeff (A j j) ≠ 0 :=
    c.originalInternal_normal_diagonal_ne_zero P (NeZero.pos _) hmax j
  have hT : (A.map PowerSeries.constantCoeff).IsUpperTriangular := by
    intro i j hji
    change j.val < i.val at hji
    change PowerSeries.constantCoeff (A i j) = 0
    by_cases hfar : j.val + 1 < i.val
    · exact (congrArg PowerSeries.constantCoeff
        (c.originalInternal_normal_shape P i j hfar)).trans (map_zero _)
    · have hnear : i.val = j.val + 1 := by omega
      calc
        PowerSeries.constantCoeff (A i j) =
            PowerSeries.constantCoeff (PowerSeries.X * PowerSeries.C c.normalCoefficient⁻¹) :=
          congrArg PowerSeries.constantCoeff (c.originalInternal_normal_subdiagonal P i j hnear)
        _ = 0 := by rw [map_mul, PowerSeries.constantCoeff_X, zero_mul]
  have hdet : PowerSeries.constantCoeff p = ∏ j, PowerSeries.constantCoeff (A j j) := by
    change PowerSeries.constantCoeff A.det = _
    rw [RingHom.map_det]
    exact Matrix.det_of_isUpperTriangular hT
  have hF0 : PowerSeries.constantCoeff F = 1 := by
    change PowerSeries.constantCoeff (p * U) = 1
    rw [map_mul, hdet, map_prod, ← Finset.prod_mul_distrib]
    apply Finset.prod_eq_one
    intro j _
    change PowerSeries.constantCoeff (A j j) * PowerSeries.constantCoeff (A j j)⁻¹ = 1
    rw [PowerSeries.constantCoeff_inv, mul_inv_cancel₀ (hunit j)]
  have hp0 : PowerSeries.constantCoeff p ≠ 0 := by
    rw [← hmap]
    exact c.originalInternal_normal_constant_ne_zero P (NeZero.pos _) hmax
  have hU0 : PowerSeries.constantCoeff U ≠ 0 := by
    intro hz
    have h := hF0
    change PowerSeries.constantCoeff (p * U) = 1 at h
    rw [map_mul, hz, mul_zero] at h
    exact zero_ne_one h
  obtain ⟨_, hw⟩ := c.originalInternal_marked_derivative_inputs P hmax r d hn hp J H hH
  have hwc (i : Fin (originalSelectedCount (hD := hD) P - 1)) (k : ℕ) :
      δ (PowerSeries.coeff k (w i)) = 0 := by
    rw [← residueSeriesGeneratorDeriv_coeff]
    change PowerSeries.coeff k
      (residueSeriesGeneratorDeriv c.top ⟨K.val, ne_of_gt K.property⟩
        ((c.normalSeries (c.originalInternalResponseMatrix P i i))⁻¹)) = 0
    rw [hw i, map_zero]
  have hUc (k : ℕ) : δ (PowerSeries.coeff k U) = 0 :=
    coeff_deriv_prod_zero δ Finset.univ w k (fun i _ l _ => hwc i l)
  have hprevp (k : ℕ) (hk : k < d * r - 1) : δ (PowerSeries.coeff k p) = 0 := by
    rw [← hmap]
    exact c.originalInternal_normal_before_first P hmax r d hp K.val K.property hheight k hk
  have hprevF (k : ℕ) (hk : k < d * r - 1) : δ (PowerSeries.coeff k F) = 0 :=
    coeff_deriv_mul_zero δ p U k
      (fun l hl => hprevp l (by omega)) (fun l _ => hUc l)
  have hlog := normalized_log_deriv_mul_independent δ p U hp0 hU0 hUc (d * r) (by omega)
  change δ (PowerSeries.coeff (d * r)
    (PowerSeries.logOf (PowerSeries.C (PowerSeries.constantCoeff F)⁻¹ * F))) = _ at hlog
  rw [hF0, inv_one, map_one, one_mul] at hlog
  dsimp only
  exact hlog.symm.trans (coeff_deriv_log_next δ F (d * r) hn hF0 hprevF)

end SkewCornerDescent.Matrix.SelectedCoordinate
