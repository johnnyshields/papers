/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.OriginalHessenbergTops

/-!
# Complete original response top inventory

Formalizes `shields-2026-skew-corner-descent.tex`, «Equal windows and the determinant defect»
(`sec:normal-chart`, `lem:actual-elimination`, `lem:component-elimination`). The diagonal
inventory contains both literal end caps and every intervening selected gap plus the selected
top. Its total retains every selected occurrence. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

attribute [local instance] Classical.propDecidable

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- An actual selected occurrence produces a positive response count. -/
theorem originalSelectedCount_pos {n : ℕ} (P : Profile n)
    (b : OriginalSelectedBlocks (hD := hD) P) :
    0 < originalSelectedCount (hD := hD) P := by
  exact Fintype.card_pos_iff.mpr ⟨b⟩

/-- The first diagonal response has the true exterior first-cap top. -/
theorem originalHessenbergDistance_first {n : ℕ} (P : Profile n)
    (hB : 0 < originalSelectedCount (hD := hD) P) :
    originalHessenbergDistance (hD := hD) P 0 0 =
      originalFirstCapDistance P (originalSelectedEnumeration (hD := hD) P ⟨0, hB⟩) := by
  unfold originalHessenbergDistance originalFirstCapDistance
  rw [originalHessenbergRows_zero]
  have hz : (0 : Fin (originalSelectedCount (hD := hD) P + 1)) =
      (⟨0, hB⟩ : Fin (originalSelectedCount (hD := hD) P)).castSucc := rfl
  rw [hz, originalHessenbergCols_castSucc, originalRowSplitEquiv_corner,
    originalColSplitEquiv_selected]

/-- The last diagonal response has the true exterior last-cap top. -/
theorem originalHessenbergDistance_last {n : ℕ} (P : Profile n)
    (hB : 0 < originalSelectedCount (hD := hD) P) :
    originalHessenbergDistance (hD := hD) P (Fin.last _) (Fin.last _) =
      originalLastCapDistance P (originalSelectedEnumeration (hD := hD) P
        ⟨originalSelectedCount (hD := hD) P - 1, by omega⟩) := by
  unfold originalHessenbergDistance originalLastCapDistance
  rw [originalHessenbergCols_last]
  have hz : (Fin.last (originalSelectedCount (hD := hD) P)) =
      (⟨originalSelectedCount (hD := hD) P - 1, by omega⟩ :
        Fin (originalSelectedCount (hD := hD) P)).succ := by
    apply Fin.ext
    simp only [Fin.val_last, Fin.val_succ]
    omega
  rw [hz, originalHessenbergRows_succ, originalRowSplitEquiv_selected,
    originalColSplitEquiv_corner]

/-- Every intervening diagonal top is the literal selected-component gap plus its span. -/
theorem originalHessenbergDistance_between {n : ℕ} (P : Profile n)
    (a k : Fin (originalSelectedCount (hD := hD) P)) (hnext : a.val + 1 = k.val) :
    originalHessenbergDistance (hD := hD) P a.succ a.succ =
      P.zeta (interiorBlockLast P
        (originalSelectedEnumeration (hD := hD) P a).val.val).castSucc -
      P.zeta (interiorBlockLast P
        (originalSelectedEnumeration (hD := hD) P k).val.val).castSucc + (c.top : ℤ) := by
  have he : a.succ = k.castSucc := Fin.ext hnext
  unfold originalHessenbergDistance
  rw [originalHessenbergRows_succ, he, originalHessenbergCols_castSucc,
    originalRowSplitEquiv_selected, originalColSplitEquiv_selected]
  have ht := c.originalSelected_endpoint_distance P
    (originalSelectedEnumeration (hD := hD) P a)
  omega

/-- The complete literal top sum records the parent top and every selected occurrence. -/
theorem originalHessenbergDistance_sum {n : ℕ} (P : Profile n) :
    ∑ i, originalHessenbergDistance (hD := hD) P i i =
      P.xi 0 - P.zeta (Fin.last n) +
        (originalSelectedCount (hD := hD) P : ℤ) * (c.top : ℤ) := by
  unfold originalHessenbergDistance
  rw [Finset.sum_sub_distrib]
  rw [Fin.sum_univ_succ (fun i => P.xi (originalRowSplitEquiv (hD := hD) P
      (.inl (originalHessenbergRows (hD := hD) P i))))]
  rw [Fin.sum_univ_castSucc (fun j => P.zeta (originalColSplitEquiv (hD := hD) P
      (.inl (originalHessenbergCols (hD := hD) P j))))]
  simp only [originalHessenbergRows_zero, originalHessenbergRows_succ,
    originalHessenbergCols_last, originalHessenbergCols_castSucc,
    originalRowSplitEquiv_corner, originalRowSplitEquiv_selected,
    originalColSplitEquiv_corner, originalColSplitEquiv_selected]
  have ht : ∑ i : Fin (originalSelectedCount (hD := hD) P),
      (P.xi (originalSelectedEnumeration (hD := hD) P i).val.val.succ -
        P.zeta (interiorBlockLast P
          (originalSelectedEnumeration (hD := hD) P i).val.val).castSucc) =
      (originalSelectedCount (hD := hD) P : ℤ) * (c.top : ℤ) := by
    simp only [c.originalSelected_endpoint_distance P, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [Finset.sum_sub_distrib] at ht
  omega

end SkewCornerDescent.Matrix.SelectedCoordinate
