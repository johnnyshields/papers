/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.NormalDeterminantFirstJet
import SkewCornerDescent.Matrix.OriginalInternalNormalStructure
import SkewCornerDescent.Matrix.HessenbergFirstSlope

/-!
# Actual full internal first-normal determinant slope

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
The original source supplies the complete constant inverse through its produced
diagonal units. Its first logarithmic slope retains every actual first entry jet
and all residue inverse couplings, without a regularity or trace premise.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The original internal determinant's first slope is the complete actual inverse
trace, including the empty internal matrix. Source units discharge invertibility. -/
theorem originalInternal_normal_first_slope {n : ℕ} (P : Profile n)
    (hB : 0 < originalSelectedCount (hD := hD) P)
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ)) :
    let A := (c.originalInternalResponseMatrix P).map c.normalSeries
    let p := c.normalSeries (c.originalInternalResponseMatrix P).det
    PowerSeries.coeff 1 p * (PowerSeries.constantCoeff p)⁻¹ =
      Matrix.trace ((A.map PowerSeries.constantCoeff)⁻¹ * A.map (PowerSeries.coeff 1)) := by
  let A := (c.originalInternalResponseMatrix P).map c.normalSeries
  have hmap : c.normalSeries (c.originalInternalResponseMatrix P).det = A.det := by
    rw [RingHom.map_det]
    congr 1
  have hc : PowerSeries.constantCoeff A.det = (A.map PowerSeries.constantCoeff).det := by
    rw [RingHom.map_det]
    congr 1
  have h0 := c.originalInternal_normal_constant_ne_zero P hB hmax
  rw [hmap, hc] at h0
  let := Matrix.invertibleOfIsUnitDet (A.map PowerSeries.constantCoeff)
    (isUnit_iff_ne_zero.mpr h0)
  dsimp only
  rw [hmap]
  exact normal_det_first_slope A

/-- Every actual internal first-normal slope is its onsite sum minus its full
adjacent-pair activity sum. The index equivalence retains every original internal
state and derives its dimension from the actual selected count. -/
theorem originalInternal_first_normal_balance {n : ℕ} (P : Profile n)
    (hB : 2 ≤ originalSelectedCount (hD := hD) P)
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ)) :
    let e : Fin (originalSelectedCount (hD := hD) P - 2 + 1) ≃
        Fin (originalSelectedCount (hD := hD) P - 1) := finCongr (by omega)
    let A := ((c.originalInternalResponseMatrix P).map c.normalSeries).submatrix e e
    let p := c.normalSeries (c.originalInternalResponseMatrix P).det
    PowerSeries.coeff 1 p * (PowerSeries.constantCoeff p)⁻¹ =
      (∑ i, PowerSeries.coeff 1 (A i i) * (PowerSeries.constantCoeff (A i i))⁻¹) -
      ∑ i : Fin (originalSelectedCount (hD := hD) P - 2),
        c.normalCoefficient⁻¹ * PowerSeries.constantCoeff (A i.castSucc i.succ) *
          (PowerSeries.constantCoeff (A i.castSucc i.castSucc))⁻¹ *
          (PowerSeries.constantCoeff (A i.succ i.succ))⁻¹ := by
  let e : Fin (originalSelectedCount (hD := hD) P - 2 + 1) ≃
      Fin (originalSelectedCount (hD := hD) P - 1) := finCongr (by omega)
  let M := (c.originalInternalResponseMatrix P).map c.normalSeries
  let A := M.submatrix e e
  have hmap : c.normalSeries (c.originalInternalResponseMatrix P).det = A.det := by
    calc
      _ = M.det := by rw [RingHom.map_det]; congr 1
      _ = A.det := (Matrix.det_submatrix_equiv_self e M).symm
  have hc : PowerSeries.constantCoeff A.det = (A.map PowerSeries.constantCoeff).det := by
    rw [RingHom.map_det]
    congr 1
  have h0 := c.originalInternal_normal_constant_ne_zero P (by omega) hmax
  rw [hmap, hc] at h0
  let := Matrix.invertibleOfIsUnitDet (A.map PowerSeries.constantCoeff)
    (isUnit_iff_ne_zero.mpr h0)
  have hval (i) : (e i).val = i.val := rfl
  have hshape : IsUpperHessenberg A := by
    intro i j hij
    exact c.originalInternal_normal_shape P (e i) (e j) (by rw [hval, hval]; exact hij)
  have hsub (i j : Fin (originalSelectedCount (hD := hD) P - 2 + 1))
      (hij : i.val = j.val + 1) : A i j =
      PowerSeries.X * PowerSeries.C c.normalCoefficient⁻¹ := by
    exact c.originalInternal_normal_subdiagonal P (e i) (e j) (by rw [hval, hval]; exact hij)
  dsimp only
  rw [hmap]
  exact hessenberg_normal_first_slope A hshape c.normalCoefficient⁻¹ hsub

end SkewCornerDescent.Matrix.SelectedCoordinate
