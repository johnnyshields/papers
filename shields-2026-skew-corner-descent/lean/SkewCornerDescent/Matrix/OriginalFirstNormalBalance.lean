/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.HessenbergFirstSlope
import SkewCornerDescent.Matrix.OriginalNormalLog

/-!
# Complete original first-normal onsite and adjacent-pair balance

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
The unchanged original source supplies every diagonal unit, Hessenberg zero and
exact selected subdiagonal. The full first-normal determinant slope includes
both true caps, all internal states and every adjacent pair activity.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing
open scoped BigOperators

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The actual original determinant's first-normal slope is its full onsite sum
minus its complete adjacent-pair sum. Neither cap nor any inverse jet is frozen. -/
theorem originalHessenberg_first_normal_balance {n : ℕ} (P : Profile n)
    (hB : 0 < originalSelectedCount (hD := hD) P)
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ)) :
    let A := (c.originalHessenbergResponse P).map c.normalSeries
    let p := c.normalSeries (c.originalHessenbergResponse P).det
    PowerSeries.coeff 1 p * (PowerSeries.constantCoeff p)⁻¹ =
      (∑ i, PowerSeries.coeff 1 (A i i) * (PowerSeries.constantCoeff (A i i))⁻¹) -
      ∑ i : Fin (originalSelectedCount (hD := hD) P),
        c.normalCoefficient⁻¹ * PowerSeries.constantCoeff (A i.castSucc i.succ) *
          (PowerSeries.constantCoeff (A i.castSucc i.castSucc))⁻¹ *
          (PowerSeries.constantCoeff (A i.succ i.succ))⁻¹ := by
  let A := (c.originalHessenbergResponse P).map c.normalSeries
  have hmap : c.normalSeries (c.originalHessenbergResponse P).det = A.det := by
    rw [RingHom.map_det]
    congr 1
  have hc : PowerSeries.constantCoeff A.det = (A.map PowerSeries.constantCoeff).det := by
    rw [RingHom.map_det]
    congr 1
  have h0 := c.originalHessenberg_normalSeries_constant_ne_zero P hB hmax
  rw [hmap, hc] at h0
  let := Matrix.invertibleOfIsUnitDet (A.map PowerSeries.constantCoeff)
    (isUnit_iff_ne_zero.mpr h0)
  have hshape : IsUpperHessenberg A := by
    intro i j hij
    change c.normalSeries (c.originalHessenbergResponse P i j) = 0
    rw [c.originalHessenbergResponse_isUpperHessenberg P i j hij, map_zero]
  have hsub (i j : Fin (originalSelectedCount (hD := hD) P + 1))
      (hij : i.val = j.val + 1) : A i j =
      PowerSeries.X * PowerSeries.C c.normalCoefficient⁻¹ := by
    have hi : i ≠ 0 := by
      intro he
      have he' := congrArg Fin.val he
      simp only [Fin.val_zero] at he'
      omega
    obtain ⟨k, rfl⟩ := Fin.exists_succ_eq_of_ne_zero hi
    have hj : j = k.castSucc := by
      apply Fin.ext
      simp only [Fin.val_succ] at hij
      change j.val = k.val
      omega
    subst j
    exact c.originalHessenberg_normalSeries_subdiagonal P k
  dsimp only
  rw [hmap]
  exact hessenberg_normal_first_slope A hshape c.normalCoefficient⁻¹ hsub

end SkewCornerDescent.Matrix.SelectedCoordinate
