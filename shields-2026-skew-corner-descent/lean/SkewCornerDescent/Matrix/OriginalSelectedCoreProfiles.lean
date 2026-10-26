/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalSelectedCoreCoordinates
import SkewCornerDescent.Matrix.ResidueProfileReindex

/-!
# Actual selected boundary strips are their literal proper-core profiles

Supports `shields-2026-skew-corner-descent.tex` (`lem:early-recovery`,
`prop:closure-pin`). The source supplies its own selected component profile,
complete index bijection, and exact beta translation. Reindexing and translation
identify the entire original strip polynomial with that same proper core.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

attribute [local instance] Classical.propDecidable

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- A valid actual first strip is exactly the proper left profile of its own
literal source component, not a freely chosen equivalent realization. -/
theorem original_left_strip_eq_selected_core {n : ℕ} (P : Profile n)
    (b : OriginalSelectedBlocks (hD := hD) P)
    (d : Option (OriginalSelectedBlocks (hD := hD) P))
    (hupper : (interiorBlock P b.val.val : ℤ) < originalResponseUpperCut P d) :
    let Q := interiorBlockProfile P b.val.val (originalBlockSelected_nonempty P b.val b.property)
    let hQ : cellSchur D hD.1 = Q.schur := (originalSelectedProfile_schur P b).symm
    c.originalLeftStripEndpointPolynomial P b d = c.selectedCoreLeftPolynomial Q hQ := by
  let Q := interiorBlockProfile P b.val.val (originalBlockSelected_nonempty P b.val b.property)
  have hQ : cellSchur D hD.1 = Q.schur := (originalSelectedProfile_schur P b).symm
  let := c.originalLeftStripResidueInverse P b d
  let : Invertible (vertexBetaMatrix c.residueMap
      (fun i : Fin (interiorBlockLength P b.val.val) => Q.xi i.succ)
      (fun i => Q.zeta i.castSucc)) := c.selectedMinorResidueInverse Q hQ
  let τ := P.zeta (interiorBlockLast P b.val.val).castSucc
  let row := fun i : OriginalLeftStripIndex (hD := hD) P b d => originalResponseRows P i.1.1.1
  let col := fun i : OriginalLeftStripIndex (hD := hD) P b d => originalResponseCols P i.1.1.1
  let x := P.xi (originalRowSplitEquiv (hD := hD) P (.inl (some b)))
  let e := (finCongr (originalRemovedSize_selected P b).symm).trans
    (originalLeftStripSourceEquiv P b d hupper)
  have hrow : row ∘ e = fun i : Fin (interiorBlockLength P b.val.val) => Q.xi i.succ + τ := by
    funext i
    exact original_selected_core_row_coordinate P b i
  have hcol : col ∘ e = fun i : Fin (interiorBlockLength P b.val.val) => Q.zeta i.castSucc + τ := by
    funext i
    exact original_selected_core_col_coordinate P b i
  have hx : x = Q.xi 0 + τ := original_selected_core_retained_row P b
  have hp := (c.residueIntervalLeftPolynomial_equiv row col x e).symm
  have ht := c.residueIntervalLeftPolynomial_translate
    (fun i : Fin (interiorBlockLength P b.val.val) => Q.xi i.succ)
    (fun i => Q.zeta i.castSucc) (Q.xi 0) τ
  have hb : c.residueIntervalLeftPolynomial
      (fun i : Fin (interiorBlockLength P b.val.val) => Q.xi i.succ)
      (fun i => Q.zeta i.castSucc) (Q.xi 0) = c.selectedCoreLeftPolynomial Q hQ := rfl
  simp only [residueIntervalLeftPolynomial, Matrix.invOf_eq_nonsing_inv] at hp
  conv_rhs at hp => rw [hrow, hcol, hx]
  simp only [residueIntervalLeftPolynomial, Matrix.invOf_eq_nonsing_inv] at ht hb
  simp only [originalLeftStripEndpointPolynomial, residueIntervalLeftPolynomial,
    Matrix.invOf_eq_nonsing_inv]
  exact hp.trans (ht.trans hb)

/-- A valid actual last strip is exactly the proper right profile of its own
literal selected source component, with the full normalized inverse. -/
theorem original_right_strip_eq_selected_core {n : ℕ} (P : Profile n)
    (b : Option (OriginalSelectedBlocks (hD := hD) P))
    (d : OriginalSelectedBlocks (hD := hD) P)
    (hlower : originalResponseLowerCut P b < (interiorBlock P d.val.val : ℤ)) :
    let Q := interiorBlockProfile P d.val.val (originalBlockSelected_nonempty P d.val d.property)
    let hQ : cellSchur D hD.1 = Q.schur := (originalSelectedProfile_schur P d).symm
    c.originalRightStripEndpointPolynomial P b d = c.selectedCoreRightPolynomial Q hQ := by
  let Q := interiorBlockProfile P d.val.val (originalBlockSelected_nonempty P d.val d.property)
  have hQ : cellSchur D hD.1 = Q.schur := (originalSelectedProfile_schur P d).symm
  let := c.originalRightStripResidueInverse P b d
  let : Invertible (vertexBetaMatrix c.residueMap
      (fun i : Fin (interiorBlockLength P d.val.val) => Q.xi i.succ)
      (fun i => Q.zeta i.castSucc)) := c.selectedMinorResidueInverse Q hQ
  let τ := P.zeta (interiorBlockLast P d.val.val).castSucc
  let row := fun i : OriginalRightStripIndex (hD := hD) P b d => originalResponseRows P i.1.1.1
  let col := fun i : OriginalRightStripIndex (hD := hD) P b d => originalResponseCols P i.1.1.1
  let y := P.zeta (originalColSplitEquiv (hD := hD) P (.inl (some d)))
  let e := (finCongr (originalRemovedSize_selected P d).symm).trans
    (originalRightStripSourceEquiv P b d hlower)
  have hrow : row ∘ e = fun i : Fin (interiorBlockLength P d.val.val) => Q.xi i.succ + τ := by
    funext i
    exact original_selected_core_row_coordinate P d i
  have hcol : col ∘ e = fun i : Fin (interiorBlockLength P d.val.val) => Q.zeta i.castSucc + τ := by
    funext i
    exact original_selected_core_col_coordinate P d i
  have hy : y = Q.zeta (Fin.last (interiorBlockLength P d.val.val)) + τ := by
    rw [Q.zeta_last, zero_add]
    exact congrArg P.zeta (originalColSplitEquiv_selected P d)
  have hp := (c.residueIntervalRightPolynomial_equiv row col y e).symm
  have ht := c.residueIntervalRightPolynomial_translate
    (fun i : Fin (interiorBlockLength P d.val.val) => Q.xi i.succ)
    (fun i => Q.zeta i.castSucc) (Q.zeta (Fin.last (interiorBlockLength P d.val.val))) τ
  have hb : c.residueIntervalRightPolynomial
      (fun i : Fin (interiorBlockLength P d.val.val) => Q.xi i.succ)
      (fun i => Q.zeta i.castSucc) (Q.zeta (Fin.last (interiorBlockLength P d.val.val))) =
        c.selectedCoreRightPolynomial Q hQ := rfl
  simp only [residueIntervalRightPolynomial, Matrix.invOf_eq_nonsing_inv] at hp
  conv_rhs at hp => rw [hrow, hcol, hy]
  simp only [residueIntervalRightPolynomial, Matrix.invOf_eq_nonsing_inv] at ht hb
  simp only [originalRightStripEndpointPolynomial, residueIntervalRightPolynomial,
    Matrix.invOf_eq_nonsing_inv]
  exact hp.trans (ht.trans hb)

/-- Agreement of the two actual source-selected core profiles pushes every
complete interval-profile discrepancy strictly beyond the selected span. All
low-strip comparisons are supplied by the literal source-core bridges. -/
theorem original_profile_discrepancy_gt_top_of_cores {n m : ℕ} (P : Profile n) (Q : Profile m)
    (b d : OriginalSelectedBlocks (hD := hD) P)
    (b' d' : OriginalSelectedBlocks (hD := hD) Q)
    (horderP : interiorBlock P b.val.val ≤ interiorBlock P d.val.val)
    (horderQ : interiorBlock Q b'.val.val ≤ interiorBlock Q d'.val.val)
    (hleft :
      c.selectedCoreLeftPolynomial
        (interiorBlockProfile P b.val.val (originalBlockSelected_nonempty P b.val b.property))
        (originalSelectedProfile_schur P b).symm =
      c.selectedCoreLeftPolynomial
        (interiorBlockProfile Q b'.val.val (originalBlockSelected_nonempty Q b'.val b'.property))
        (originalSelectedProfile_schur Q b').symm)
    (hright :
      c.selectedCoreRightPolynomial
        (interiorBlockProfile P d.val.val (originalBlockSelected_nonempty P d.val d.property))
        (originalSelectedProfile_schur P d).symm =
      c.selectedCoreRightPolynomial
        (interiorBlockProfile Q d'.val.val (originalBlockSelected_nonempty Q d'.val d'.property))
        (originalSelectedProfile_schur Q d').symm)
    (w : ℕ)
    (hdiff :
      (c.originalResidueLeftEndpointPolynomial P (some b) (some d)).coeff w ≠
        (c.originalResidueLeftEndpointPolynomial Q (some b') (some d')).coeff w ∨
      (c.originalResidueRightEndpointPolynomial P (some b) (some d)).coeff w ≠
        (c.originalResidueRightEndpointPolynomial Q (some b') (some d')).coeff w) :
    (c.top : ℕ) < w := by
  have hupperP : (interiorBlock P b.val.val : ℤ) < originalResponseUpperCut P (some d) := by
    change (interiorBlock P b.val.val : ℤ) < (interiorBlock P d.val.val : ℤ) + 1
    omega
  have hlowerP : originalResponseLowerCut P (some b) < (interiorBlock P d.val.val : ℤ) := by
    change (interiorBlock P b.val.val : ℤ) - 1 < (interiorBlock P d.val.val : ℤ)
    omega
  have hupperQ : (interiorBlock Q b'.val.val : ℤ) < originalResponseUpperCut Q (some d') := by
    change (interiorBlock Q b'.val.val : ℤ) < (interiorBlock Q d'.val.val : ℤ) + 1
    omega
  have hlowerQ : originalResponseLowerCut Q (some b') < (interiorBlock Q d'.val.val : ℤ) := by
    change (interiorBlock Q b'.val.val : ℤ) - 1 < (interiorBlock Q d'.val.val : ℤ)
    omega
  apply c.original_profile_discrepancy_gt_top P Q b d b' d' ?_ ?_ w hdiff
  · rw [c.original_left_strip_eq_selected_core P b (some d) hupperP,
      c.original_left_strip_eq_selected_core Q b' (some d') hupperQ]
    exact hleft
  · rw [c.original_right_strip_eq_selected_core P (some b) d hlowerP,
      c.original_right_strip_eq_selected_core Q (some b') d' hlowerQ]
    exact hright

end SkewCornerDescent.Matrix.SelectedCoordinate
