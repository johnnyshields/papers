/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.FiniteHessenbergEndLocality
import SkewCornerDescent.Matrix.OriginalNormalLog

/-!
# Complete endpoint logarithmic locality of the original response matrix

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
The actual original matrix supplies its Hessenberg support, exact normal subdiagonal,
and every nonzero diagonal residue. All source entries and their normal jets remain.
Sorry-free.
-/

noncomputable section

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The complete original normal response matrix, extended only outside its finite source. -/
def originalNormalExtension {n : ℕ} (P : Profile n) :
    ℕ → ℕ → PowerSeries (OtherField c.top) :=
  hessenbergExtension ((c.originalHessenbergResponse P).map c.normalSeries)
    c.normalCoefficient⁻¹

/-- The original normal matrix produces upper-Hessenberg support of its extension. -/
theorem originalNormalExtension_shape {n : ℕ} (P : Profile n) :
    ∀ i j : ℕ, j + 1 < i → c.originalNormalExtension P i j = 0 := by
  apply hessenbergExtension_shape
  intro i j hij
  change c.normalSeries (c.originalHessenbergResponse P i j) = 0
  rw [c.originalHessenbergResponse_isUpperHessenberg P i j hij, map_zero]

/-- Every selected subdiagonal is the actual normal variable divided by its coefficient. -/
theorem originalNormalExtension_subdiag {n : ℕ} (P : Profile n) (i : ℕ) :
    c.originalNormalExtension P (i + 1) i =
      PowerSeries.C c.normalCoefficient⁻¹ * PowerSeries.X :=
  hessenbergExtension_subdiag _ _ i

/-- Original residue factors, not additional unit assumptions, supply all interval units. -/
theorem originalNormalExtension_regular {n : ℕ} (P : Profile n)
    (hB : 0 < originalSelectedCount (hD := hD) P)
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ)) :
    ∀ i : ℕ, PowerSeries.constantCoeff (c.originalNormalExtension P i i) ≠ 0 := by
  apply hessenbergExtension_regular
  intro i
  change PowerSeries.constantCoeff (c.normalSeries (c.originalHessenbergResponse P i i)) ≠ 0
  rw [c.normalSeries_constant_apply]
  exact c.originalHessenberg_residue_ne_zero P hB hmax i

/-- The auxiliary family retains every original finite entry, including both full caps. -/
theorem originalNormalExtension_inside {n : ℕ} (P : Profile n)
    (i j : Fin (originalSelectedCount (hD := hD) P + 1)) :
    c.originalNormalExtension P i.val j.val =
      c.normalSeries (c.originalHessenbergResponse P i j) := by
  apply hessenbergExtension_inside
  intro x y hxy
  let t : Fin (originalSelectedCount (hD := hD) P) := ⟨y.val, by omega⟩
  have hx : x = t.succ := by apply Fin.ext; exact hxy.symm
  have hy : y = t.castSucc := by apply Fin.ext; rfl
  rw [hx, hy]
  change c.normalSeries (c.originalHessenbergResponse P t.succ t.castSucc) = _
  rw [c.originalHessenberg_normalSeries_subdiagonal, mul_comm]

/-- The full actual normal determinant is exactly the source interval determinant. -/
theorem originalNormalExtension_det {n : ℕ} (P : Profile n) :
    intervalDet (c.originalNormalExtension P) 0 (originalSelectedCount (hD := hD) P + 1) =
      c.normalSeries (c.originalHessenbergResponse P).det := by
  rw [RingHom.map_det]
  unfold intervalDet
  congr 1
  ext i j : 1
  simp only [Matrix.of_apply, zero_add]
  exact c.originalNormalExtension_inside P i j

/-- The full original left cap through order `k` depends only on its first `k+1` states.
All regularity and selected-subdiagonal inputs are produced from the source. -/
theorem original_left_log_prefix_locality {n : ℕ} (P : Profile n)
    (hB : 0 < originalSelectedCount (hD := hD) P)
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ))
    (k : ℕ) (hk : k ≤ originalSelectedCount (hD := hD) P) :
    PowerSeries.coeff k (leftCap (c.originalNormalExtension P)
      (originalSelectedCount (hD := hD) P)) =
    PowerSeries.coeff k (leftCap (c.originalNormalExtension P) k) := by
  exact leftCap_coeff_eq_of_le _ c.normalCoefficient⁻¹
    (c.originalNormalExtension_shape P) (c.originalNormalExtension_subdiag P)
    (c.originalNormalExtension_regular P hB hmax) k k _ le_rfl hk

/-- The full original right cap through order `k` depends only on its last `k+1` states.
No original boundary entry is frozen or required to omit a chosen higher generator. -/
theorem original_right_log_suffix_locality {n : ℕ} (P : Profile n)
    (hB : 0 < originalSelectedCount (hD := hD) P)
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ))
    (k d : ℕ) (hkd : originalSelectedCount (hD := hD) P = k + d) :
    PowerSeries.coeff k (rightCap (c.originalNormalExtension P) 0
      (originalSelectedCount (hD := hD) P)) =
    PowerSeries.coeff k (rightCap (c.originalNormalExtension P) d k) := by
  rw [hkd]
  simpa only [zero_add] using rightCap_shift _ c.normalCoefficient⁻¹
    (c.originalNormalExtension_shape P) (c.originalNormalExtension_subdiag P)
    (c.originalNormalExtension_regular P hB hmax) k d 0

end SkewCornerDescent.Matrix.SelectedCoordinate
