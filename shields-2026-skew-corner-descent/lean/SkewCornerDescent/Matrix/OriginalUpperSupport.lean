/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.OriginalEndpointGeometry
import SkewCornerDescent.Matrix.OrderedResponses

/-!
# Original upper-response support

Supports `shields-2026-skew-corner-descent.tex`, «Equal windows and the determinant defect»
(`sec:normal-chart`, `lem:actual-elimination`). Actual removed source indices strictly
intervene between retained endpoints. Selected boundary blocks retain their entire proper
minor, rather than disappearing from the inverse contraction. Sorry-free.
-/

namespace SkewCornerDescent.Matrix

open SkewGluing

/-- Every produced block label is bounded by the full complementary source size. -/
theorem interiorBlock_le_size {n : ℕ} (P : Profile n) (i : Fin n) : interiorBlock P i ≤ n := by
  unfold interiorBlock
  have h := Finset.card_le_card
    (Finset.subset_univ (((interiorCuts P).filter fun k => k ≤ i)))
  simpa only [Finset.card_univ, Fintype.card_fin] using h

/-- Strictly ordered labels force the same strict order on their original indices. -/
theorem interiorBlock_index_lt {n : ℕ} (P : Profile n) {i j : Fin n}
    (h : interiorBlock P i < interiorBlock P j) : i < j := by
  by_contra hn
  have := interiorBlock_mono P (le_of_not_gt hn)
  omega

namespace SelectedCoordinate

attribute [local instance] Classical.propDecidable

variable {D : Diagram} {hD : IsConnectedSkew D}

/-- Actual removed row indices lie strictly after a selected first row at or below its block. -/
theorem originalRemovedRow_gt_selected {n : ℕ} (P : Profile n)
    (b : OriginalSelectedBlocks (hD := hD) P) (j : OriginalRemainingIndices (hD := hD) P)
    (h : interiorBlock P b.val.val ≤ interiorBlock P j.1.val) :
    b.val.val < originalRemovedRow (hD := hD) P j.1 j.2 := by
  by_cases he : interiorBlock P b.val.val = interiorBlock P j.1.val
  · have hb := originalBlocks_label_injective P he
    rcases j with ⟨d, k⟩
    change b.val = d at hb
    subst d
    change b.val.val.val <
      (interiorSliceIndex _ _ _ (originalRemovedRowPosition (hD := hD) P b.val k)).val
    simp only [originalRemovedRowPosition, dite_eq_left b.property,
      interiorSliceIndex, b.val.property]
    omega
  · have hl := interiorBlock_index_lt P (lt_of_le_of_ne h he)
    have hm := (mem_interiorBlockFiber_iff P j.1.val _).mp
      ((mem_interiorBlockFiber P j.1.val _).mpr
        (originalRemovedRow_block (hD := hD) P j.1 j.2))
    rw [j.1.property] at hm
    exact lt_of_lt_of_le hl hm.1

/-- Actual removed columns lie strictly before a selected last column at or above its block. -/
theorem originalRemovedCol_lt_selected {n : ℕ} (P : Profile n)
    (b : OriginalSelectedBlocks (hD := hD) P) (j : OriginalRemainingIndices (hD := hD) P)
    (h : interiorBlock P j.1.val ≤ interiorBlock P b.val.val) :
    originalRemovedCol (hD := hD) P j.1 j.2 < interiorBlockLast P b.val.val := by
  by_cases he : interiorBlock P j.1.val = interiorBlock P b.val.val
  · have hb := originalBlocks_label_injective P he
    rcases j with ⟨d, k⟩
    change d = b.val at hb
    subst d
    have hk := k.isLt
    simp only [originalRemovedSize, ite_eq_left b.property] at hk
    have hf := Fin.le_def.mp (interiorBlockFirst_le_last P b.val.val)
    change (interiorSliceIndex _ _ _
      (originalRemovedColPosition (hD := hD) P b.val k)).val < _
    simp only [originalRemovedColPosition, interiorSliceIndex]
    unfold interiorBlockLength at hk
    omega
  · have hl := interiorBlock_index_lt P
      (i := originalRemovedCol (hD := hD) P j.1 j.2)
      (j := interiorBlockLast P b.val.val) (by
        rw [originalRemovedCol_block, interiorBlockLast_label]
        exact lt_of_le_of_ne h he)
    exact hl

/-- Integer lower cutoff includes the proper minor of a selected boundary block. -/
def originalResponseLowerCut {n : ℕ} (P : Profile n) :
    Option (OriginalSelectedBlocks (hD := hD) P) → ℤ
  | none => -1
  | some b => (interiorBlock P b.val.val : ℤ) - 1

/-- Integer upper cutoff includes the proper minor of a selected boundary block. -/
def originalResponseUpperCut {n : ℕ} (P : Profile n) :
    Option (OriginalSelectedBlocks (hD := hD) P) → ℤ
  | none => n + 1
  | some b => (interiorBlock P b.val.val : ℤ) + 1

/-- Every intervening removed row is strictly below the literal retained source row. -/
theorem originalResponse_row_lt {n : ℕ} (P : Profile n)
    (b : Option (OriginalSelectedBlocks (hD := hD) P))
    (j : OriginalRemainingIndices (hD := hD) P)
    (h : originalResponseLowerCut P b < (interiorBlock P j.1.val : ℤ)) :
    P.xi (originalRemovedRow (hD := hD) P j.1 j.2).succ <
      P.xi (originalRowSplitEquiv (hD := hD) P (.inl b)) := by
  cases b with
  | none =>
    rw [originalRowSplitEquiv_corner]
    exact P.xi_strictAnti (by change 0 < _ + 1; omega)
  | some b =>
    rw [originalRowSplitEquiv_selected]
    apply P.xi_strictAnti
    have hr := originalRemovedRow_gt_selected P b j (by
      change (interiorBlock P b.val.val : ℤ) - 1 < (interiorBlock P j.1.val : ℤ) at h
      omega)
    change b.val.val.val + 1 < _ + 1
    exact Nat.add_lt_add_right hr 1

/-- Every intervening removed column is strictly above the literal retained source column. -/
theorem originalResponse_col_gt {n : ℕ} (P : Profile n)
    (b : Option (OriginalSelectedBlocks (hD := hD) P))
    (j : OriginalRemainingIndices (hD := hD) P)
    (h : (interiorBlock P j.1.val : ℤ) < originalResponseUpperCut P b) :
    P.zeta (originalColSplitEquiv (hD := hD) P (.inl b)) <
      P.zeta (originalRemovedCol (hD := hD) P j.1 j.2).castSucc := by
  cases b with
  | none =>
    rw [originalColSplitEquiv_corner]
    exact P.zeta_strictAnti (Fin.castSucc_lt_last _)
  | some b =>
    rw [originalColSplitEquiv_selected]
    apply P.zeta_strictAnti
    exact originalRemovedCol_lt_selected P b j (by
      change (interiorBlock P j.1.val : ℤ) < (interiorBlock P b.val.val : ℤ) + 1 at h
      omega)

/-- Removed columns outside the lower cutoff lie strictly above the retained source row. -/
theorem originalResponse_incoming_cutoff {n : ℕ} (P : Profile n)
    (b : Option (OriginalSelectedBlocks (hD := hD) P))
    (j : OriginalRemainingIndices (hD := hD) P)
    (h : ¬originalResponseLowerCut P b < (interiorBlock P j.1.val : ℤ)) :
    P.xi (originalRowSplitEquiv (hD := hD) P (.inl b)) <
      P.zeta (originalRemovedCol (hD := hD) P j.1 j.2).castSucc := by
  cases b with
  | none =>
    change ¬(-1 : ℤ) < (interiorBlock P j.1.val : ℤ) at h
    omega
  | some b =>
    rw [originalRowSplitEquiv_selected]
    apply interior_block_endpoint_separation P
    rw [originalRemovedCol_block]
    change ¬(interiorBlock P b.val.val : ℤ) - 1 <
      (interiorBlock P j.1.val : ℤ) at h
    omega

/-- Removed rows outside the upper cutoff lie strictly below the retained source column. -/
theorem originalResponse_outgoing_cutoff {n : ℕ} (P : Profile n)
    (b : Option (OriginalSelectedBlocks (hD := hD) P))
    (j : OriginalRemainingIndices (hD := hD) P)
    (h : ¬(interiorBlock P j.1.val : ℤ) < originalResponseUpperCut P b) :
    P.xi (originalRemovedRow (hD := hD) P j.1 j.2).succ <
      P.zeta (originalColSplitEquiv (hD := hD) P (.inl b)) := by
  cases b with
  | none =>
    change ¬(interiorBlock P j.1.val : ℤ) < (n : ℤ) + 1 at h
    have := interiorBlock_le_size P j.1.val
    omega
  | some b =>
    rw [originalColSplitEquiv_selected]
    apply interior_block_endpoint_separation P
    rw [originalRemovedRow_block, interiorBlockLast_label]
    change ¬(interiorBlock P j.1.val : ℤ) <
      (interiorBlock P b.val.val : ℤ) + 1 at h
    omega

end SelectedCoordinate
end SkewCornerDescent.Matrix
