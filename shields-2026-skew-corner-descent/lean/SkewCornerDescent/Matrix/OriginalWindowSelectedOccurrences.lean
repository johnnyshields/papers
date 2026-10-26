/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.PrivateWindowComponents
import SkewCornerDescent.Matrix.OriginalSelectedOrder

/-!
# Actual selected occurrences matched by complete literal windows

Supports `shields-2026-skew-corner-descent.tex` (`lem:actual-words`).
A whole selected prefix occurrence has exactly one translated suffix occurrence in the
original source. The matching preserves actual source order. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D}

/-- Equal complete windows produce a unique original suffix block for a whole prefix block.
The boundary-gap hypotheses are geometric; they exclude cutting any interior component. -/
theorem originalWindow_selected_occurrence {n : ℕ} (P : Profile n)
    (lo hi q : ℤ) (v : ℤ × ℤ)
    (hprefix : IsSkew (P.cells.filter fun x => lo ≤ content x ∧ content x < hi - q))
    (hwindow : P.cells.filter (fun x => lo + q ≤ content x ∧ content x < hi) =
      translate v (P.cells.filter fun x => lo ≤ content x ∧ content x < hi - q))
    (hlo : ∀ x ∈ diagramInterior P.cells, content x ≠ lo)
    (hloq : ∀ x ∈ diagramInterior P.cells, content x ≠ lo + q)
    (hhiq : ∀ x ∈ diagramInterior P.cells, content x ≠ hi - q)
    (hhi : ∀ x ∈ diagramInterior P.cells, content x ≠ hi)
    (b : OriginalSelectedBlocks (hD := hD) P)
    (hb : ∀ x ∈ interiorBlockCells P b.val.val, lo ≤ content x ∧ content x < hi - q) :
    ∃! e : OriginalSelectedBlocks (hD := hD) P,
      interiorBlockCells P e.val.val = translate v (interiorBlockCells P b.val.val) := by
  classical
  have hiB : interiorBlockCells P b.val.val ∈ selectedComponentInventory (hD := hD) P.cells := by
    rw [selectedComponentInventory_eq_original_image]
    exact Finset.mem_image.mpr ⟨b, Finset.mem_univ _, rfl⟩
  have hsource : interiorBlockCells P b.val.val ∈
      (selectedComponentInventory (hD := hD) P.cells).filter
        (fun C => ∀ x ∈ C, lo ≤ content x ∧ content x < hi - q) :=
    Finset.mem_filter.mpr ⟨hiB, hb⟩
  have htarget : translate v (interiorBlockCells P b.val.val) ∈
      ((selectedComponentInventory (hD := hD) P.cells).filter
        (fun C => ∀ x ∈ C, lo ≤ content x ∧ content x < hi - q)).image
          (SkewGluing.translate v) :=
    Finset.mem_image.mpr ⟨interiorBlockCells P b.val.val, hsource, rfl⟩
  rw [← selectedComponentInventory_literal_windows P.cells lo hi q v
    hprefix hwindow hlo hloq hhiq hhi] at htarget
  obtain ⟨hC, hskew, he⟩ := (mem_selectedComponentInventory _ _).mp
    (Finset.mem_filter.mp htarget).1
  obtain ⟨e, he⟩ := exists_originalSelectedBlock_of_component (hD := hD) P _ hC he
  refine ⟨e, he, ?_⟩
  intro a ha
  exact originalSelectedBlock_cells_injective P (ha.trans he.symm)

end SkewCornerDescent.Matrix.SelectedCoordinate
