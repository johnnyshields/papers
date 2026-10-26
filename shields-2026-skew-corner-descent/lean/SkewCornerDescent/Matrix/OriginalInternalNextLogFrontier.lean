/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalInternalNormalStructure
import SkewCornerDescent.Matrix.NormalNextLogCoefficient

/-!
# Exact complete logarithmic correction at the actual internal next-fresh frontier

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
The actual gap geometry supplies all earlier independence and the original
internal determinant supplies its own normal unit. The entire first coefficient
appears in the correction, including pair terms and full inverse jets.
The cyclic count and original defect assembly are separate obligations. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing CyclicWindows

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Before the first possible high internal interval, the complete actual determinant
has no fresh-generator derivative. Every entry and normal jet remains in the determinant. -/
theorem originalInternal_normal_before_first {n : ℕ} (P : Profile n)
    [NeZero (originalSelectedCount (hD := hD) P)]
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ))
    (r k : ℕ)
    (hp : Function.Periodic
      (fun x => c.originalCompletedGap P ((ZMod.finEquiv _).symm x))
      (r : ZMod (originalSelectedCount (hD := hD) P)))
    (K : ℕ+) (hK : c.top < K)
    (hheight : k • windowSum
      (fun x => c.originalCompletedGap P ((ZMod.finEquiv _).symm x)) 1 r 0 < (K : ℤ))
    (m : ℕ) (hm : m < k * r - 1) :
    residueGeneratorDeriv c.top ⟨K, ne_of_gt hK⟩
      (PowerSeries.coeff m (c.normalSeries (c.originalInternalResponseMatrix P).det)) = 0 := by
  let A := (c.originalInternalResponseMatrix P).map c.normalSeries
  let δ := residueGeneratorDeriv c.top ⟨K, ne_of_gt hK⟩
  rw [RingHom.map_det]
  change δ (PowerSeries.coeff m A.det) = 0
  apply hessenberg_coeff_deriv_zero δ A (c.originalInternal_normal_shape P)
    c.normalCoefficient⁻¹
  · apply residueGeneratorDeriv_lower
    exact Subfield.inv_mem _ (residueLowerField_mono hK.le c.normalCoordinate_mem_lower.1)
  · intro i j hij
    exact c.originalInternal_normal_subdiagonal P i j hij
  · intro i j hij hcost l hl
    change δ (PowerSeries.coeff l (c.normalSeries (c.originalHessenbergResponse P
      (originalInternalStateIndex (hD := hD) P i)
      (originalInternalStateIndex (hD := hD) P j)))) = 0
    exact c.originalHessenberg_normalSeries_derivative_below P (NeZero.pos _) hmax K hK _ _
      (by change i.val + 1 ≤ j.val + 1; omega)
      ((c.originalInternalDistance_short_period P r k hp i j hij (by omega)).trans hheight) l

/-- The actual complete normalized internal logarithm at the next fresh order retains
both original determinant frontiers and its entire first-coefficient correction.
Neither earlier independence nor a normal determinant unit is assumed. -/
theorem originalInternal_normalized_log_next {n : ℕ} (P : Profile n)
    [NeZero (originalSelectedCount (hD := hD) P)]
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ))
    (r k : ℕ) (hn : 2 ≤ k * r)
    (hp : Function.Periodic
      (fun x => c.originalCompletedGap P ((ZMod.finEquiv _).symm x))
      (r : ZMod (originalSelectedCount (hD := hD) P)))
    (K : ℕ+) (hK : c.top < K)
    (hheight : k • windowSum
      (fun x => c.originalCompletedGap P ((ZMod.finEquiv _).symm x)) 1 r 0 < (K : ℤ)) :
    let p := c.normalSeries (c.originalInternalResponseMatrix P).det
    let δ := residueGeneratorDeriv c.top ⟨K, ne_of_gt hK⟩
    δ (PowerSeries.coeff (k * r)
      (PowerSeries.logOf (PowerSeries.C (PowerSeries.constantCoeff p)⁻¹ * p))) =
      (PowerSeries.constantCoeff p)⁻¹ * δ (PowerSeries.coeff (k * r) p) -
        ((PowerSeries.constantCoeff p)⁻¹ ^ 2 * PowerSeries.coeff 1 p) *
          δ (PowerSeries.coeff (k * r - 1) p) := by
  exact coeff_deriv_normalized_log_next _ _ _ hn
    (c.originalInternal_normal_constant_ne_zero P (NeZero.pos _) hmax)
    (fun m hm => c.originalInternal_normal_before_first P hmax r k hp K hK hheight m hm)

end SkewCornerDescent.Matrix.SelectedCoordinate
