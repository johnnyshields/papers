/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalCompleteWindowCapVectors
import SkewCornerDescent.Matrix.OriginalClosureHalfCapProjection

/-!
# Complete source-cap beta lists in either literal horizontal half

Supports `shields-2026-skew-corner-descent.tex` (`prop:closure-pin`).
Every cap side has the complete source index equivalence in either actual
horizontal half. The resulting row and column lists can be compared directly
with the corresponding vertical lists. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing
attribute [local instance] Classical.propDecidable

variable {D : Diagram} {hD : IsConnectedSkew D}

/-- Both actual horizontal halves preserve every complete source cap index
and both original beta endpoints by their produced common content shift. -/
theorem originalHorizontalClosure_half_cap_vectors {n m : ℕ}
    (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalHorizontalClosure P = translate v Q.cells) (copy upper : Bool)
    (b : OriginalSelectedBlocks (hD := hD) P) :
    let shift : ℤ := if copy then P.xi 0 else 0
    let d := originalHorizontalClosureSelectedCopy P Q v hQ copy b
    ∃ e : OriginalResponseInterval (hD := hD) P
        (originalClosureCapLeft upper b) (originalClosureCapRight upper b) ≃
      {i : OriginalWholeWindowRemaining (hD := hD) Q shift (P.xi 0 + shift) //
        originalCapBlockSide upper d i.1.val},
      ∀ i, originalResponseRows Q ⟨(e i).val.1.val, (e i).val.2⟩ =
          originalResponseRows P i.1.1 + shift ∧
        originalResponseCols Q ⟨(e i).val.1.val, (e i).val.2⟩ =
          originalResponseCols P i.1.1 + shift := by
  intro shift d
  let w := originalClosureBlockDisplacement P copy
  have hw : content w = shift := by
    cases copy <;> simp [w, shift, originalClosureBlockDisplacement, content]
  have hwindow : Q.cells.filter (fun x => shift ≤ content x ∧ content x < P.xi 0 + shift) =
      translate w P.cells := by
    cases copy
    · simpa only [shift, w, originalClosureBlockDisplacement, Bool.false_eq_true,
        ↓reduceIte, add_zero] using originalHorizontalClosure_lower_window P Q v hQ
    · simpa only [shift, w, originalClosureBlockDisplacement, ↓reduceIte, two_mul]
        using originalHorizontalClosure_upper_window P Q v hQ
  have he := originalHorizontalClosure_selected_normalized_cells P Q v hQ copy b
  have hd : originalBlockInWindow Q shift (P.xi 0 + shift) d.val := by
    left
    refine ⟨originalBlockSelected_nonempty Q d.val d.property, ?_⟩
    intro x hx
    rw [← he, mem_translate] at hx
    have hb := P.content_bounds_cells
      (Finset.mem_filter.mp (interiorSliceCells_subset P _ _ _ hx)).1
    have hc : content (x - w) = content x - shift := by
      simp only [content, Prod.fst_sub, Prod.snd_sub] at *
      omega
    change 0 ≤ content (x - w) ∧ content (x - w) < P.xi 0 at hb
    omega
  have hbound0 := profile_normalized_lower_private_boundaries Q
  have hbound1 := profile_normalized_upper_private_boundaries Q
  have hjoin := originalHorizontalClosure_profile_join_private P Q v hQ
  have htop : Q.xi 0 = 2 * P.xi 0 := by
    have h := originalHorizontalClosure_xi_upper P Q v hQ 0
    change Q.xi 0 = P.xi 0 + P.xi 0 at h
    omega
  have hlo : ∀ x ∈ diagramInterior Q.cells, content x ≠ shift := by
    cases copy
    · simpa only [shift, Bool.false_eq_true, ↓reduceIte] using
        private_diagonal_no_interior hbound0.1
    · simpa only [shift, ↓reduceIte] using private_diagonal_no_interior hjoin.1
  have hhi : ∀ x ∈ diagramInterior Q.cells, content x ≠ P.xi 0 + shift := by
    cases copy
    · simpa only [shift, Bool.false_eq_true, ↓reduceIte, add_zero] using
        private_diagonal_no_interior hjoin.1
    · simpa only [shift, ↓reduceIte, htop, two_mul] using private_diagonal_no_interior hbound1.1
  exact originalCompleteWindow_cap_vectors P Q shift w hw hwindow hlo hhi upper b d hd he

end SkewCornerDescent.Matrix.SelectedCoordinate
