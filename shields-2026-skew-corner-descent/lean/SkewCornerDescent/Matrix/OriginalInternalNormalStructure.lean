/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalInternalNormalFrontiers
import SkewCornerDescent.Matrix.OriginalEndLogLocality

/-!
# Produced structure and regularity of the complete internal normal matrix

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
The original source supplies Hessenberg support, every exact selected subdiagonal,
and its complete internal normal unit. No entry or inverse jet is frozen.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Every full internal normal entry has the original source's Hessenberg support. -/
theorem originalInternal_normal_shape {n : ℕ} (P : Profile n) :
    IsUpperHessenberg ((c.originalInternalResponseMatrix P).map c.normalSeries) := by
  intro i j hij
  change c.normalSeries (c.originalHessenbergResponse P
    (originalInternalStateIndex (hD := hD) P i)
    (originalInternalStateIndex (hD := hD) P j)) = 0
  rw [c.originalHessenbergResponse_isUpperHessenberg P _ _ (by
    dsimp only [originalInternalStateIndex]
    omega), map_zero]

/-- Every selected internal subdiagonal is the exact normal scalar, with no extra jets. -/
theorem originalInternal_normal_subdiagonal {n : ℕ} (P : Profile n)
    (i j : Fin (originalSelectedCount (hD := hD) P - 1))
    (hij : i.val = j.val + 1) :
    ((c.originalInternalResponseMatrix P).map c.normalSeries) i j =
      PowerSeries.X * PowerSeries.C c.normalCoefficient⁻¹ := by
  let b : Fin (originalSelectedCount (hD := hD) P) := ⟨j.val + 1, by have := j.isLt; omega⟩
  have hi : originalInternalStateIndex (hD := hD) P i = b.succ := by
    apply Fin.ext
    simp only [Fin.val_succ]
    dsimp only [originalInternalStateIndex, b]
    omega
  have hj : originalInternalStateIndex (hD := hD) P j = b.castSucc := rfl
  change c.normalSeries (c.originalHessenbergResponse P
    (originalInternalStateIndex (hD := hD) P i)
    (originalInternalStateIndex (hD := hD) P j)) = _
  rw [hi, hj]
  exact c.originalHessenberg_normalSeries_subdiagonal P b

/-- The entire actual internal determinant is its literal interval in the full source.
Both exterior states are omitted, and no internal original state is dropped. -/
theorem originalInternal_normal_det_interval {n : ℕ} (P : Profile n) :
    c.normalSeries (c.originalInternalResponseMatrix P).det =
      intervalDet (c.originalNormalExtension P) 1 (originalSelectedCount (hD := hD) P - 1) := by
  rw [RingHom.map_det]
  unfold intervalDet
  congr 1
  ext i j : 1
  change c.normalSeries (c.originalHessenbergResponse P
    (originalInternalStateIndex (hD := hD) P i)
    (originalInternalStateIndex (hD := hD) P j)) =
      c.originalNormalExtension P (1 + i.val) (1 + j.val)
  have h := c.originalNormalExtension_inside P
    (originalInternalStateIndex (hD := hD) P i) (originalInternalStateIndex (hD := hD) P j)
  simpa only [originalInternalStateIndex, Nat.add_comm] using h.symm

/-- The complete actual internal normal determinant has nonzero constant coefficient,
including an empty internal interval. Source diagonal units supply its regularity. -/
theorem originalInternal_normal_constant_ne_zero {n : ℕ} (P : Profile n)
    (hB : 0 < originalSelectedCount (hD := hD) P)
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ)) :
    PowerSeries.constantCoeff (c.normalSeries (c.originalInternalResponseMatrix P).det) ≠ 0 := by
  rw [c.originalInternal_normal_det_interval P]
  exact intervalDet_regular _ c.normalCoefficient⁻¹
    (c.originalNormalExtension_shape P) (c.originalNormalExtension_subdiag P)
    (c.originalNormalExtension_regular P hB hmax) 1 _

end SkewCornerDescent.Matrix.SelectedCoordinate
