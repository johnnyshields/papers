/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalFilteredCapProjection
import SkewCornerDescent.Matrix.OriginalPrivateWindowMembership

/-!
# Equal whole windows identify the complete longer-cap contraction

Supports `shields-2026-skew-corner-descent.tex` (`prop:closure-pin`).
Literal selected-block translation and actual window equality transport the
clipped cap into the opposite complete exterior cap. Containment of that cap
is produced from its selected endpoint, including all empty and nonrow blocks.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing
attribute [local instance] Classical.propDecidable

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Translation of a selected whole lower-window block supplies its whole
upper-window containment, with no separately matched beta coordinates. -/
theorem originalEqualWindow_selected_contained {n : ℕ} (P : Profile n)
    (q : ℤ) (v : ℤ × ℤ) (hv : content v = q)
    (b d : OriginalSelectedBlocks (hD := hD) P)
    (hb : ∀ x ∈ interiorBlockCells P b.val.val,
      0 ≤ content x ∧ content x < P.xi 0 - q)
    (he : translate v (interiorBlockCells P b.val.val) = interiorBlockCells P d.val.val) :
    originalBlockInWindow P 0 (P.xi 0 - q) b.val ∧
      originalBlockInWindow P q (P.xi 0) d.val := by
  refine ⟨Or.inl ⟨originalBlockSelected_nonempty P b.val b.property, hb⟩,
    Or.inl ⟨originalBlockSelected_nonempty P d.val d.property, ?_⟩⟩
  intro x hx
  rw [← he, mem_translate] at hx
  have h := hb _ hx
  have hc : content (x - v) = content x - q := by
    simp only [content, Prod.fst_sub, Prod.snd_sub] at *
    omega
  omega

/-- The clipped lower-window upper cap is exactly the complete true upper
cap at the corresponding translated selected endpoint. -/
theorem originalEqualWindow_lower_cap_projection {n : ℕ} (P : Profile n)
    (q : ℤ) (v : ℤ × ℤ) (hv : content v = q)
    (hwindow : P.cells.filter (fun x => q ≤ content x ∧ content x < P.xi 0) =
      translate v (P.cells.filter fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hcutq : diagLo P.cells q = diagHi P.cells q)
    (hcutLq : diagLo P.cells (P.xi 0 - q) = diagHi P.cells (P.xi 0 - q))
    (b d : OriginalSelectedBlocks (hD := hD) P)
    (hb : ∀ x ∈ interiorBlockCells P b.val.val,
      0 ≤ content x ∧ content x < P.xi 0 - q)
    (he : translate v (interiorBlockCells P b.val.val) = interiorBlockCells P d.val.val)
    (A T : LaurentPolynomial (OtherField c.top)) (z : ℤ) :
    c.originalFilteredCapInverseProjection P 0 (P.xi 0 - q) true b A T z =
      c.originalCapInverseProjection P true d A T (z + q) := by
  have hband := originalEqualWindow_selected_contained P q v hv b d hb he
  have hlo := profile_normalized_lower_private_boundaries P
  have hhi := profile_normalized_upper_private_boundaries P
  have htransport := c.originalLiteralWindow_filtered_cap_projection P P 0 (P.xi 0 - q)
    q v hv (by simpa only [zero_add, sub_add_cancel] using hwindow)
    (private_diagonal_no_interior hlo.1)
    (by simpa only [zero_add] using private_diagonal_no_interior hcutq)
    (private_diagonal_no_interior hcutLq)
    (by simpa only [sub_add_cancel] using private_diagonal_no_interior hhi.1)
    true b d hband.1 (by simpa only [zero_add, sub_add_cancel] using hband.2) he A T z
  simp only [zero_add, sub_add_cancel] at htransport
  rw [htransport]
  exact c.originalFilteredCap_projection_of_contained P q (P.xi 0) true d
    (fun a ha => originalBlockInWindow_before_selected P q d a hband.2 ha) A T (z + q)

/-- The clipped upper-window lower cap is the complete true lower cap of
its literal lower-window preimage, at the same transported content position. -/
theorem originalEqualWindow_upper_cap_projection {n : ℕ} (P : Profile n)
    (q : ℤ) (v : ℤ × ℤ) (hv : content v = q)
    (hwindow : P.cells.filter (fun x => q ≤ content x ∧ content x < P.xi 0) =
      translate v (P.cells.filter fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hcutq : diagLo P.cells q = diagHi P.cells q)
    (hcutLq : diagLo P.cells (P.xi 0 - q) = diagHi P.cells (P.xi 0 - q))
    (b d : OriginalSelectedBlocks (hD := hD) P)
    (hb : ∀ x ∈ interiorBlockCells P b.val.val,
      0 ≤ content x ∧ content x < P.xi 0 - q)
    (he : translate v (interiorBlockCells P b.val.val) = interiorBlockCells P d.val.val)
    (A T : LaurentPolynomial (OtherField c.top)) (z : ℤ) :
    c.originalFilteredCapInverseProjection P q (P.xi 0) false d A T (z + q) =
      c.originalCapInverseProjection P false b A T z := by
  have hband := originalEqualWindow_selected_contained P q v hv b d hb he
  have hlo := profile_normalized_lower_private_boundaries P
  have hhi := profile_normalized_upper_private_boundaries P
  have htransport := c.originalLiteralWindow_filtered_cap_projection P P 0 (P.xi 0 - q)
    q v hv (by simpa only [zero_add, sub_add_cancel] using hwindow)
    (private_diagonal_no_interior hlo.1)
    (by simpa only [zero_add] using private_diagonal_no_interior hcutq)
    (private_diagonal_no_interior hcutLq)
    (by simpa only [sub_add_cancel] using private_diagonal_no_interior hhi.1)
    false b d hband.1 (by simpa only [zero_add, sub_add_cancel] using hband.2) he A T z
  simp only [zero_add, sub_add_cancel] at htransport
  rw [← htransport]
  exact c.originalFilteredCap_projection_of_contained P 0 (P.xi 0 - q) false b
    (fun a ha => originalBlockInWindow_after_selected P (P.xi 0 - q) b a hband.1 ha) A T z

end SkewCornerDescent.Matrix.SelectedCoordinate
