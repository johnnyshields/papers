/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.OriginalHorizontalSplice

/-!
# The complete actual component inventory of the horizontal closure

Formalizes `shields-2026-skew-corner-descent.tex`, «Equal windows and the determinant defect»
(`sec:normal-chart`, `lem:actual-elimination`, `lem:actual-words`). The two complete interior
copies have separated content bands. Their component inventories are retained independently;
no component is merged across the actual horizontal join. Sorry-free.
-/

namespace SkewCornerDescent.Matrix

open SkewGluing

/-- No actual interior cell of the first copy is adjacent to one of the translated copy. -/
theorem originalHorizontalClosure_not_adjacent {n : ℕ} (P : Profile n)
    {x y : ℤ × ℤ} (hx : x ∈ diagramInterior P.cells)
    (hy : y ∈ translate (vH P.cells) (diagramInterior P.cells)) : ¬ CellAdj x y := by
  have h := (emptyMarkH_isLegal P.isConnectedSkew_cells).empty_interiorCopy_separated
    rfl (by decide : (0 : ℕ) ≠ 1)
    (by simpa only [emptyMarkH, Nat.cast_zero, zero_smul, SkewGluing.translate_zero] using hx)
    (by simpa only [emptyMarkH, Nat.cast_one, one_smul] using hy)
  intro ha
  rw [cellAdj_iff] at ha
  simp only [content] at h
  omega

/-- The actual closure interior has precisely both complete component inventories. -/
theorem originalHorizontalClosure_components {n : ℕ} (P : Profile n) :
    edgeComponents (diagramInterior (originalHorizontalClosure P)) =
      edgeComponents (diagramInterior P.cells) ∪
        (edgeComponents (diagramInterior P.cells)).image (translate (vH P.cells)) := by
  rw [originalHorizontalClosure_interior,
    edgeComponents_union (fun x hx y hy => originalHorizontalClosure_not_adjacent P hx hy),
    edgeComponents_translate]

/-- Every original component occurs intact in the actual closure. -/
theorem originalHorizontalClosure_first_component {n : ℕ} (P : Profile n) {C : Diagram}
    (hC : C ∈ edgeComponents (diagramInterior P.cells)) :
    C ∈ edgeComponents (diagramInterior (originalHorizontalClosure P)) := by
  rw [originalHorizontalClosure_components]
  exact Finset.mem_union_left _ hC

/-- Every translated original component occurs intact in the actual closure. -/
theorem originalHorizontalClosure_second_component {n : ℕ} (P : Profile n) {C : Diagram}
    (hC : C ∈ edgeComponents (diagramInterior P.cells)) :
    translate (vH P.cells) C ∈ edgeComponents (diagramInterior (originalHorizontalClosure P)) := by
  rw [originalHorizontalClosure_components]
  exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨C, hC, rfl⟩)

/-- The two actual inventories are disjoint, so repeated functions do not erase occurrences. -/
theorem originalHorizontalClosure_component_disjoint {n : ℕ} (P : Profile n) :
    Disjoint (edgeComponents (diagramInterior P.cells))
      ((edgeComponents (diagramInterior P.cells)).image (translate (vH P.cells))) := by
  rw [Finset.disjoint_left]
  intro C hC hC'
  obtain ⟨E, hE, he⟩ := Finset.mem_image.mp hC'
  obtain ⟨x, hx⟩ := (isEdgeConnected_component hC).1
  have hx0 := component_subset hC hx
  have hx1 : x ∈ translate (vH P.cells) (diagramInterior P.cells) := by
    rw [← he] at hx
    exact mem_translate.mpr (component_subset hE (mem_translate.mp hx))
  have h := (emptyMarkH_isLegal P.isConnectedSkew_cells).empty_interiorCopy_separated
    rfl (by decide : (0 : ℕ) ≠ 1)
    (by simpa only [emptyMarkH, Nat.cast_zero, zero_smul, SkewGluing.translate_zero] using hx0)
    (by simpa only [emptyMarkH, Nat.cast_one, one_smul] using hx1)
  omega

end SkewCornerDescent.Matrix
