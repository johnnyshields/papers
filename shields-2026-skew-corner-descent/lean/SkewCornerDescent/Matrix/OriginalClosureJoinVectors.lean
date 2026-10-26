/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalClosureCapComparison
import SkewCornerDescent.Matrix.OriginalPrivateIntervalCapVectors
import SkewCornerDescent.Matrix.OriginalClosureResponses

/-!
# The complete nonunit vertical join matches the literal horizontal join

Supports `shields-2026-skew-corner-descent.tex` (`prop:closure-pin`).
Actual private geometry splits both complete join intervals into their two
caps. Corresponding literal half windows match every beta endpoint. Removing
the one vertical unit therefore leaves the full horizontal interval, including
all cross-side couplings. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing
attribute [local instance] Classical.propDecidable

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

include c in
/-- Deleting the actual vertical join unit gives the complete horizontal
join's original beta lists. No full matrix, inverse, or scalar response match
is supplied as a hypothesis. -/
theorem originalClosures_join_nonunit_vectors {n m s : ℕ}
    (P : Profile n) (V : Profile m) (H : Profile s) (v w : ℤ × ℤ)
    (hV : originalVerticalClosure P = translate v V.cells)
    (hH : originalHorizontalClosure P = translate w H.cells)
    (b d : OriginalSelectedBlocks (hD := hD) P) :
    let bV := originalVerticalClosureSelectedCopy P V v hV true b
    let dV := originalVerticalClosureSelectedCopy P V v hV false d
    let bH := originalHorizontalClosureSelectedCopy P H w hH true b
    let dH := originalHorizontalClosureSelectedCopy P H w hH false d
    ∃ e : {i : OriginalResponseInterval (hD := hD) V (some bV) (some dV) //
        ¬ (originalResponseRows V i.1.1 = P.xi 0 ∧ originalResponseCols V i.1.1 = P.xi 0)} ≃
      OriginalResponseInterval (hD := hD) H (some bH) (some dH),
      ∀ j, originalResponseRows V (e.symm j).val.1.1 = originalResponseRows H j.1.1 ∧
        originalResponseCols V (e.symm j).val.1.1 = originalResponseCols H j.1.1 := by
  intro bV dV bH dH
  have hprivV := originalVerticalClosure_profile_join_private P V v hV
  have hprivH := originalHorizontalClosure_profile_join_private P H w hH
  have hsourceX := P.xi_pos b.val.val.succ
  have hsourceY : P.zeta (interiorBlockLast P d.val.val).castSucc < P.xi 0 := by
    have h := c.originalFirstCapDistance_gt_top P d
    unfold originalFirstCapDistance at h
    have hn := c.top.property
    omega
  have hxV : P.xi 0 < V.xi (originalRowSplitEquiv (hD := hD) V (.inl (some bV))) := by
    have h := (c.originalVerticalClosure_retained_endpoints P V v hV true b).1
    simp only [↓reduceIte, originalRowSplitEquiv_selected] at h
    rw [originalRowSplitEquiv_selected]
    dsimp only [bV]
    omega
  have hyV : V.zeta (originalColSplitEquiv (hD := hD) V (.inl (some dV))) < P.xi 0 := by
    have h := (c.originalVerticalClosure_retained_endpoints P V v hV false d).2
    simp only [Bool.false_eq_true, ↓reduceIte, add_zero, originalColSplitEquiv_selected] at h
    rw [originalColSplitEquiv_selected]
    dsimp only [dV]
    omega
  have hxH : P.xi 0 < H.xi (originalRowSplitEquiv (hD := hD) H (.inl (some bH))) := by
    have h := (originalHorizontalClosure_retained_endpoints P H w hH true b).1
    simp only [originalClosureBlockDisplacement, ↓reduceIte, sub_zero,
      originalRowSplitEquiv_selected] at h
    rw [originalRowSplitEquiv_selected]
    dsimp only [bH]
    omega
  have hyH : H.zeta (originalColSplitEquiv (hD := hD) H (.inl (some dH))) < P.xi 0 := by
    have h := (originalHorizontalClosure_retained_endpoints P H w hH false d).2
    simp only [originalClosureBlockDisplacement, Bool.false_eq_true, ↓reduceIte,
      add_sub_cancel_right, originalColSplitEquiv_selected] at h
    rw [originalColSplitEquiv_selected]
    dsimp only [dH]
    omega
  obtain ⟨sV, hsV⟩ := originalPrivateInterval_cap_vectors V bV dV (P.xi 0)
    hprivV.1 hprivV.2 hxV hyV
  obtain ⟨sH, hsH⟩ := originalPrivateInterval_cap_vectors H bH dH (P.xi 0)
    hprivH.1 hprivH.2 hxH hyH
  obtain ⟨lower, hlower⟩ := originalClosures_private_cap_vectors P V H v w hV hH false true d
  obtain ⟨upper, hupper⟩ := originalClosures_private_cap_vectors P V H v w hV hH true false b
  have hno (i : OriginalResponseInterval (hD := hD) H (some bH) (some dH)) :
      ¬ (originalResponseRows H i.1.1 = P.xi 0 ∧ originalResponseCols H i.1.1 = P.xi 0) :=
    fun h => originalHorizontalClosure_join_no_unit P H w hH i.1.1 h.2
  let forget : {i : OriginalResponseInterval (hD := hD) H (some bH) (some dH) //
      ¬ (originalResponseRows H i.1.1 = P.xi 0 ∧ originalResponseCols H i.1.1 = P.xi 0)} ≃
      OriginalResponseInterval (hD := hD) H (some bH) (some dH) :=
    { toFun := fun i => i.val
      invFun := fun i => ⟨i, hno i⟩
      left_inv := fun i => by apply Subtype.ext; rfl
      right_inv := fun _ => rfl }
  let t := Equiv.sumCongr lower upper
  refine ⟨((sV.trans t).trans sH.symm).trans forget, ?_⟩
  intro j
  let jH := forget.symm j
  have hv := hsV (t.symm (sH jH))
  have hh := hsH (sH jH)
  rw [sH.symm_apply_apply] at hh
  have hside :
      Sum.elim (fun i => originalResponseRows V ⟨i.val.1.val, i.val.2⟩)
          (fun i => originalResponseRows V ⟨i.val.1.val, i.val.2⟩) (t.symm (sH jH)) =
        Sum.elim (fun i => originalResponseRows H ⟨i.val.1.val, i.val.2⟩)
          (fun i => originalResponseRows H ⟨i.val.1.val, i.val.2⟩) (sH jH) ∧
      Sum.elim (fun i => originalResponseCols V ⟨i.val.1.val, i.val.2⟩)
          (fun i => originalResponseCols V ⟨i.val.1.val, i.val.2⟩) (t.symm (sH jH)) =
        Sum.elim (fun i => originalResponseCols H ⟨i.val.1.val, i.val.2⟩)
          (fun i => originalResponseCols H ⟨i.val.1.val, i.val.2⟩) (sH jH) := by
    rcases h : sH jH with i | i
    · have he := hlower (lower.symm i)
      rw [lower.apply_symm_apply] at he
      exact ⟨he.1.symm, he.2.symm⟩
    · have he := hupper (upper.symm i)
      rw [upper.apply_symm_apply] at he
      exact ⟨he.1.symm, he.2.symm⟩
  exact ⟨hv.1.trans (hside.1.trans hh.1.symm), hv.2.trans (hside.2.trans hh.2.symm)⟩

end SkewCornerDescent.Matrix.SelectedCoordinate
