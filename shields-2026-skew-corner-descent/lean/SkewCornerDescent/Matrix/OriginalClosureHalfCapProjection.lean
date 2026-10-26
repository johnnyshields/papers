/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalClosureHalfWindows
import SkewCornerDescent.Matrix.OriginalPrivateWindowMembership

/-!
# Full cap contractions inside either actual closure half

Supports `shields-2026-skew-corner-descent.tex` (`prop:closure-pin`).
The copy choice and the cap side are independent: the join-facing cap is
transported as well as the exterior-facing cap. Literal half-window equality
supplies all retained indices and the fresh complete inverse. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing
attribute [local instance] Classical.propDecidable

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Every selected closure copy is the full normalized affine source copy. -/
theorem originalHorizontalClosure_selected_normalized_cells {n m : ℕ}
    (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalHorizontalClosure P = translate v Q.cells) (copy : Bool)
    (b : OriginalSelectedBlocks (hD := hD) P) :
    translate (originalClosureBlockDisplacement P copy) (interiorBlockCells P b.val.val) =
      interiorBlockCells Q (originalHorizontalClosureSelectedCopy P Q v hQ copy b).val.val := by
  apply translate_injective v
  rw [translate_translate, originalHorizontalClosureSelectedCopy_cells]
  have hv := (originalHorizontalClosure_profile_rows P Q v hQ).2
  rw [hv]
  cases copy
  · simp only [originalClosureBlockDisplacement, Bool.false_eq_true, ↓reduceIte]
    rw [show (-(n : ℤ), -(n : ℤ)) + ((n : ℤ), (n : ℤ)) = 0 by ext <;> simp,
      translate_zero]
  · simp only [originalClosureBlockDisplacement, ↓reduceIte]
    rw [originalHorizontalDisplacement_pair]
    congr 1
    ext <;> simp only [Prod.fst_add, Prod.snd_add] <;> ring

/-- The complete source cap equals its clipped presentation in either actual
closure half, including all cross-index inverse entries in nonrow components. -/
theorem originalHorizontalClosure_half_cap_projection {n m : ℕ}
    (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalHorizontalClosure P = translate v Q.cells) (copy upper : Bool)
    (b : OriginalSelectedBlocks (hD := hD) P)
    (A T : LaurentPolynomial (OtherField c.top)) (z : ℤ) :
    let shift : ℤ := if copy then P.xi 0 else 0
    let d := originalHorizontalClosureSelectedCopy P Q v hQ copy b
    c.originalCapInverseProjection P upper b A T z =
      c.originalFilteredCapInverseProjection Q shift (P.xi 0 + shift) upper d A T (z + shift) := by
  let shift : ℤ := if copy then P.xi 0 else 0
  let w := originalClosureBlockDisplacement P copy
  let d := originalHorizontalClosureSelectedCopy P Q v hQ copy b
  have hw : content w = shift := by
    cases copy <;> simp [w, shift, originalClosureBlockDisplacement, content]
  have hP : P.cells.filter (fun x => 0 ≤ content x ∧ content x < P.xi 0) = P.cells := by
    ext x
    rw [Finset.mem_filter]
    exact ⟨And.left, fun hx => ⟨hx, P.content_bounds_cells hx⟩⟩
  have hwindow : Q.cells.filter (fun x => 0 + shift ≤ content x ∧
      content x < P.xi 0 + shift) = translate w
        (P.cells.filter fun x => 0 ≤ content x ∧ content x < P.xi 0) := by
    rw [hP]
    cases copy
    · simpa only [shift, w, originalClosureBlockDisplacement, Bool.false_eq_true,
        ↓reduceIte, add_zero] using originalHorizontalClosure_lower_window P Q v hQ
    · simpa only [shift, w, originalClosureBlockDisplacement, ↓reduceIte, zero_add,
        two_mul] using originalHorizontalClosure_upper_window P Q v hQ
  have he := originalHorizontalClosure_selected_normalized_cells P Q v hQ copy b
  have hb : originalBlockInWindow P 0 (P.xi 0) b.val := originalBlockInWindow_full P b.val
  have hd : originalBlockInWindow Q (0 + shift) (P.xi 0 + shift) d.val := by
    left
    refine ⟨originalBlockSelected_nonempty Q d.val d.property, ?_⟩
    intro x hx
    rw [← he, mem_translate] at hx
    have h := (originalBlockInWindow_full P b.val).resolve_right (by
      intro h
      have hp := originalBlockSelected_nonempty P b.val b.property
      omega)
    have hbounds := h.2 _ hx
    change 0 ≤ content (x - w) ∧ content (x - w) < P.xi 0 at hbounds
    have hc : content (x - w) = content x - shift := by
      simp only [content, Prod.fst_sub, Prod.snd_sub] at *
      omega
    omega
  have hnP := profile_normalized_lower_private_boundaries P
  have hhP := profile_normalized_upper_private_boundaries P
  have hnQ := profile_normalized_lower_private_boundaries Q
  have hhQ := profile_normalized_upper_private_boundaries Q
  have hjQ := originalHorizontalClosure_profile_join_private P Q v hQ
  have htopQ : Q.xi 0 = 2 * P.xi 0 := by
    have ht := originalHorizontalClosure_xi_upper P Q v hQ 0
    change Q.xi 0 = P.xi 0 + P.xi 0 at ht
    omega
  have hloQ : ∀ x ∈ diagramInterior Q.cells, content x ≠ 0 + shift := by
    cases copy
    · simpa only [shift, Bool.false_eq_true, ↓reduceIte, add_zero] using
        private_diagonal_no_interior hnQ.1
    · simpa only [shift, ↓reduceIte, zero_add] using private_diagonal_no_interior hjQ.1
  have hhiQ : ∀ x ∈ diagramInterior Q.cells, content x ≠ P.xi 0 + shift := by
    cases copy
    · simpa only [shift, Bool.false_eq_true, ↓reduceIte, add_zero] using
        private_diagonal_no_interior hjQ.1
    · simpa only [shift, ↓reduceIte, htopQ, two_mul] using private_diagonal_no_interior hhQ.1
  have htransport := c.originalLiteralWindow_filtered_cap_projection P Q 0 (P.xi 0)
    shift w hw hwindow (private_diagonal_no_interior hnP.1) hloQ
    (private_diagonal_no_interior hhP.1) hhiQ upper b d hb hd he A T z
  rw [c.originalFilteredCap_projection_of_contained P 0 (P.xi 0) upper b
    (fun a _ => originalBlockInWindow_full P a)] at htransport
  simpa only [zero_add] using htransport

end SkewCornerDescent.Matrix.SelectedCoordinate
