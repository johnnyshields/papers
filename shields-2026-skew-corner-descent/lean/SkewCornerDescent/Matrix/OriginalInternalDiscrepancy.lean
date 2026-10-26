/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalIncomingDiscrepancy
import SkewCornerDescent.Matrix.OriginalInternalSelfJet
import SkewCornerDescent.Matrix.OriginalInternalHeights

/-!
# Visible discrepancy between actual internal states

Formalizes `shields-2026-skew-corner-descent.tex`, `prop:normal-interface`.
Equal original internal heights and residues, with distinct complete incoming
profiles, produce a genuine first difference strictly below half-height.
Both adjacent selected endpoint ranks and the positive height are produced.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate
open SkewGluing
variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Distinct incoming profiles of two actual equal-height, equal-response
internal states have a first nonzero difference strictly below half-height.
All selected endpoints and the required positive height are source-produced. -/
theorem originalInternal_incoming_difference_visible {n : ℕ} (P : Profile n)
    (i j : Fin (originalSelectedCount (hD := hD) P - 1))
    (hheight : originalHessenbergDistance (hD := hD) P
        (originalInternalStateIndex P i) (originalInternalStateIndex P i) =
      originalHessenbergDistance (hD := hD) P
        (originalInternalStateIndex P j) (originalInternalStateIndex P j))
    (hresponse : c.originalInternalResidue P i = c.originalInternalResidue P j)
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ))
    (hne : (c.originalInternalEndpointProfiles P i).1 ≠
      (c.originalInternalEndpointProfiles P j).1) :
    ∃ w : ℕ, 0 < w ∧
      2 * (w : ℤ) < originalHessenbergDistance (hD := hD) P
        (originalInternalStateIndex P i) (originalInternalStateIndex P i) ∧
      (∀ l < w, (c.originalInternalEndpointProfiles P i).1.coeff l =
        (c.originalInternalEndpointProfiles P j).1.coeff l) ∧
      (c.originalInternalEndpointProfiles P i).1.coeff w -
        (c.originalInternalEndpointProfiles P j).1.coeff w ≠ 0 := by
  let ai : Fin (originalSelectedCount (hD := hD) P) := ⟨i.val, by have := i.isLt; omega⟩
  let bi : Fin (originalSelectedCount (hD := hD) P) := ⟨i.val + 1, by have := i.isLt; omega⟩
  let aj : Fin (originalSelectedCount (hD := hD) P) := ⟨j.val, by have := j.isLt; omega⟩
  let bj : Fin (originalSelectedCount (hD := hD) P) := ⟨j.val + 1, by have := j.isLt; omega⟩
  let E := originalSelectedEnumeration (hD := hD) P
  let H := originalHessenbergDistance (hD := hD) P
    (originalInternalStateIndex P i) (originalInternalStateIndex P i)
  have hHN : 2 * (c.top : ℤ) < H := c.originalInternal_height_gt_twice_top P i
  have hHpos : 0 < H := by have := c.top.pos; omega
  let K : ℕ+ := ⟨H.toNat, by omega⟩
  have hK : (K : ℤ) = H := Int.toNat_of_nonneg hHpos.le
  have hKN : 2 * (c.top : ℕ) < (K : ℕ) := by
    have hh : 2 * (c.top : ℤ) < (K : ℤ) := by rw [hK]; exact hHN
    exact_mod_cast hh
  have hi : P.xi (originalRowSplitEquiv (hD := hD) P (.inl (some (E ai)))) -
      P.zeta (originalColSplitEquiv (hD := hD) P (.inl (some (E bi)))) = (K : ℤ) := by
    rw [hK]
    change _ = P.xi (originalRowSplitEquiv (hD := hD) P
        (.inl (originalHessenbergRows P ai.succ))) -
      P.zeta (originalColSplitEquiv (hD := hD) P
        (.inl (originalHessenbergCols P bi.castSucc)))
    rw [originalHessenbergRows_succ, originalHessenbergCols_castSucc]
  have hj : P.xi (originalRowSplitEquiv (hD := hD) P (.inl (some (E aj)))) -
      P.zeta (originalColSplitEquiv (hD := hD) P (.inl (some (E bj)))) = (K : ℤ) := by
    rw [hK]
    change _ = originalHessenbergDistance (hD := hD) P
      (originalInternalStateIndex P i) (originalInternalStateIndex P i)
    rw [hheight]
    change _ = P.xi (originalRowSplitEquiv (hD := hD) P
        (.inl (originalHessenbergRows P aj.succ))) -
      P.zeta (originalColSplitEquiv (hD := hD) P
        (.inl (originalHessenbergCols P bj.castSucc)))
    rw [originalHessenbergRows_succ, originalHessenbergCols_castSucc]
  have hr : c.regularResidue (c.originalLocalResponse P (some (E ai)) (some (E bi))) =
      c.regularResidue (c.originalLocalResponse P (some (E aj)) (some (E bj))) := by
    rw [← c.originalInternalResponseMatrix_selected_entry P i i,
      ← c.originalInternalResponseMatrix_selected_entry P j j]
    exact hresponse
  obtain ⟨w, hw, hbound, hbefore, hη⟩ := c.original_incoming_difference_visible P P
    ai bi (by rfl) aj bj (by rfl) K hKN hi hj hmax hmax hr hne
  refine ⟨w, hw, ?_, hbefore, hη⟩
  have hh : 2 * (w : ℤ) < (K : ℤ) := by exact_mod_cast hbound
  rwa [hK] at hh

end SkewCornerDescent.Matrix.SelectedCoordinate
