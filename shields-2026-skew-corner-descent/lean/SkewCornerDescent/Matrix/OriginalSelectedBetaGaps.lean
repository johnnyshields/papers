/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/


import SkewCornerDescent.Matrix.OriginalClosureRowDisplacement

/-!
# Actual selected beta increments and their finite displacement

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
A selected core’s exact endpoint span identifies each signed beta increment
with the actual retained interval height. Finite increment periodicity then
produces a common beta displacement without inventing wrapped endpoints.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate
open SkewGluing
variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The actual original retained selected-row beta coordinate. -/
noncomputable def originalSelectedSourceBeta {n : ℕ} (P : Profile n)
    (i : Fin (originalSelectedCount (hD := hD) P)) : ℤ :=
  P.xi (originalSelectedEnumeration (hD := hD) P i).val.val.succ

/-- Signed beta increment between consecutive actual selected starting rows. -/
noncomputable def originalInternalSourceBetaGap {n : ℕ} (P : Profile n)
    (i : Fin (originalSelectedCount (hD := hD) P - 1)) : ℤ :=
  originalSelectedSourceBeta P ⟨i.val+1, by have := i.isLt; omega⟩ -
    originalSelectedSourceBeta P ⟨i.val, by have := i.isLt; omega⟩

/-- The exact selected core span converts the retained height to its beta increment. -/
theorem originalInternal_source_beta_gap_height {n : ℕ} (P : Profile n)
    (i : Fin (originalSelectedCount (hD := hD) P - 1)) :
    originalInternalSourceBetaGap P i = (c.top : ℤ) - originalHessenbergDistance (hD := hD) P
      (originalInternalStateIndex P i) (originalInternalStateIndex P i) := by
  let a : Fin (originalSelectedCount (hD := hD) P) := ⟨i.val, by have := i.isLt; omega⟩
  let b : Fin (originalSelectedCount (hD := hD) P) := ⟨i.val+1, by have := i.isLt; omega⟩
  let E := originalSelectedEnumeration (hD := hD) P
  have hcore := c.originalSelected_endpoint_distance P (E b)
  change originalSelectedSourceBeta P b - originalSelectedSourceBeta P a =
    (c.top : ℤ) - (P.xi (originalRowSplitEquiv P (.inl (originalHessenbergRows P a.succ))) -
      P.zeta (originalColSplitEquiv P (.inl (originalHessenbergCols P b.castSucc))))
  rw [originalHessenbergRows_succ, originalHessenbergCols_castSucc,
    originalRowSplitEquiv_selected, originalColSplitEquiv_selected]
  change P.xi (E b).val.val.succ - P.xi (E a).val.val.succ =
    (c.top : ℤ) - (P.xi (E a).val.val.succ -
      P.zeta (interiorBlockLast P (E b).val.val).castSucc)
  omega

/-- Actual finite beta-increment periods give one common whole-period beta displacement. -/
theorem originalSelected_source_beta_displacement {n : ℕ} (P : Profile n) (r B : ℕ)
    (hB : B < originalSelectedCount (hD := hD) P) (hr : r ≤ B)
    (hperiod : ∀ i : Fin (originalSelectedCount (hD := hD) P - 1), (hi : i.val + r < B) →
      originalInternalSourceBetaGap P ⟨i.val + r, by omega⟩ = originalInternalSourceBetaGap P i)
    (i : ℕ) (hi : i + r ≤ B) :
    originalSelectedSourceBeta P ⟨i + r, by omega⟩ -
        originalSelectedSourceBeta P ⟨i, by omega⟩ =
      originalSelectedSourceBeta P ⟨r, by omega⟩ -
        originalSelectedSourceBeta P ⟨0, by omega⟩ := by
  let s : ℕ → ℤ := fun j => if h : j < originalSelectedCount (hD := hD) P then
    originalSelectedSourceBeta P ⟨j, h⟩ else 0
  have hs (j : ℕ) (hj : j < originalSelectedCount (hD := hD) P) :
      s j = originalSelectedSourceBeta P ⟨j, hj⟩ := dite_eq_left hj
  have hstep (j : ℕ) (hj : j + r < B) : s (j + r + 1) - s (j + r) = s (j + 1) - s j := by
    have hp := hperiod ⟨j, by omega⟩ hj
    rw [hs (j+r+1) (by omega), hs (j+r) (by omega), hs (j+1) (by omega), hs j (by omega)]
    exact hp
  have he := finite_row_displacement_of_periodic_differences s r B hstep i hi
  rw [hs (i+r) (by omega), hs i (by omega), hs r (by omega), hs 0 (by omega)] at he
  exact he

end SkewCornerDescent.Matrix.SelectedCoordinate
