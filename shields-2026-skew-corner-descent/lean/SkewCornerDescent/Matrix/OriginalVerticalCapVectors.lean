/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalCompleteWindowCapVectors
import SkewCornerDescent.Matrix.OriginalVerticalUnitJoin

/-!
# Complete source-cap beta lists in either literal vertical half

Supports `shields-2026-skew-corner-descent.tex` (`prop:closure-pin`).
Both cap sides in each actual vertical half have their complete source index
equivalence and endpoint lists. The join unit lies at the strict boundary and
is not silently retained in either half. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing
attribute [local instance] Classical.propDecidable

variable {D : Diagram} {hD : IsConnectedSkew D}

/-- Every complete cap list agrees with its clipped presentation in either
actual vertical half, with the copy and cap side chosen independently. -/
theorem originalVerticalClosure_half_cap_vectors {n m : ℕ}
    (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalVerticalClosure P = translate v Q.cells) (copy upper : Bool)
    (b : OriginalSelectedBlocks (hD := hD) P) :
    let shift : ℤ := if copy then P.xi 0 else 0
    let d := originalVerticalClosureSelectedCopy P Q v hQ copy b
    ∃ e : OriginalResponseInterval (hD := hD) P
        (originalClosureCapLeft upper b) (originalClosureCapRight upper b) ≃
      {i : OriginalWholeWindowRemaining (hD := hD) Q shift (P.xi 0 + shift) //
        originalCapBlockSide upper d i.1.val},
      ∀ i, originalResponseRows Q ⟨(e i).val.1.val, (e i).val.2⟩ =
          originalResponseRows P i.1.1 + shift ∧
        originalResponseCols Q ⟨(e i).val.1.val, (e i).val.2⟩ =
          originalResponseCols P i.1.1 + shift := by
  intro shift d
  let w := originalVerticalCopyDisplacement P v copy
  have hw : content w = shift := originalVerticalCopyDisplacement_content P Q v hQ copy
  have hwindow : Q.cells.filter (fun x => shift ≤ content x ∧ content x < P.xi 0 + shift) =
      translate w P.cells := by
    cases copy
    · simpa only [shift, w, originalVerticalCopyDisplacement, Bool.false_eq_true,
        ↓reduceIte, add_zero] using originalVerticalClosure_lower_window P Q v hQ
    · simpa only [shift, w, originalVerticalCopyDisplacement, ↓reduceIte, two_mul]
        using originalVerticalClosure_upper_window P Q v hQ
  have hbound0 := profile_normalized_lower_private_boundaries Q
  have hbound1 := profile_normalized_upper_private_boundaries Q
  have hjoin := originalVerticalClosure_profile_join_private P Q v hQ
  have htop := originalVerticalClosure_profile_top P Q v hQ
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
  exact originalCompleteWindow_cap_vectors P Q shift w hw hwindow hlo hhi upper b d
    (originalVerticalClosure_selected_copy_window P Q v hQ copy b)
    (originalVerticalClosure_selected_normalized_cells P Q v hQ copy b)

end SkewCornerDescent.Matrix.SelectedCoordinate
