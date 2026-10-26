/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.EmptyVerticalClosure
import SkewCornerDescent.Matrix.OriginalPrivateUnitVertex

/-!
# Complete interior copies of the actual vertical closure

Supports `shields-2026-skew-corner-descent.tex` (`prop:closure-pin`).
The literal vertical union has disjoint content bands. Southeast erosion
therefore retains exactly the two complete source interiors. Their component
inventories and both private join flags are produced from the actual cells.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix

open SkewGluing

/-- The actual vertical empty displacement has the complete source span. -/
theorem originalVerticalDisplacement_content {n : ℕ} (P : Profile n) :
    content (vH P.cells - eCell) = P.xi 0 := by
  have h := originalHorizontalDisplacement_content P
  rw [P.zeta_last] at h
  simp only [content, eCell, Prod.fst_sub, Prod.snd_sub] at *
  omega

/-- The actual vertical closure retains both whole source interiors, without
creating an interior cell at its join or dropping a nonrow source component. -/
theorem originalVerticalClosure_interior {n : ℕ} (P : Profile n) :
    diagramInterior (originalVerticalClosure P) = diagramInterior P.cells ∪
      translate (vH P.cells - eCell) (diagramInterior P.cells) := by
  ext x
  let w := vH P.cells - eCell
  have hw : content w = P.xi 0 := originalVerticalDisplacement_content P
  simp only [diagramInterior, originalVerticalClosure_union, Finset.mem_filter,
    Finset.mem_union, mem_translate]
  change ((x ∈ P.cells ∨ x-w ∈ P.cells) ∧
    (x+eCell ∈ P.cells ∨ x+eCell-w ∈ P.cells)) ↔
      ((x ∈ P.cells ∧ x+eCell ∈ P.cells) ∨
        (x-w ∈ P.cells ∧ x-w+eCell ∈ P.cells))
  rw [show x + eCell - w = x - w + eCell by abel]
  constructor
  · rintro ⟨hx | hx, hn | hn⟩
    · exact Or.inl ⟨hx, hn⟩
    · have ha := P.content_bounds_cells hx
      have hb := P.content_bounds_cells hn
      simp only [content, eCell, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub] at *
      omega
    · have ha := P.content_bounds_cells hx
      have hb := P.content_bounds_cells hn
      simp only [content, eCell, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub] at *
      omega
    · exact Or.inr ⟨hx, hn⟩
  · rintro (⟨hx, hn⟩ | ⟨hx, hn⟩)
    · exact ⟨Or.inl hx, Or.inl hn⟩
    · exact ⟨Or.inr hx, Or.inr hn⟩

/-- Complete interior copies are separated by more than one content step. -/
theorem originalVerticalClosure_not_adjacent {n : ℕ} (P : Profile n)
    {x y : ℤ × ℤ} (hx : x ∈ diagramInterior P.cells)
    (hy : y ∈ translate (vH P.cells - eCell) (diagramInterior P.cells)) : ¬ CellAdj x y := by
  have ha := interior_content_strict P.isConnectedSkew_cells hx
  have hb := interior_content_strict P.isConnectedSkew_cells (mem_translate.mp hy)
  rw [P.minContent_cells, P.maxContent_cells] at ha hb
  have hw := originalVerticalDisplacement_content P
  intro hadj
  rw [cellAdj_iff] at hadj
  simp only [content, eCell, Prod.fst_sub, Prod.snd_sub] at ha hb hw
  omega

/-- Every actual source component occurs intact in the vertical closure. -/
theorem originalVerticalClosure_components {n : ℕ} (P : Profile n) :
    edgeComponents (diagramInterior (originalVerticalClosure P)) =
      edgeComponents (diagramInterior P.cells) ∪
        (edgeComponents (diagramInterior P.cells)).image (translate (vH P.cells - eCell)) := by
  rw [originalVerticalClosure_interior,
    edgeComponents_union (fun x hx y hy => originalVerticalClosure_not_adjacent P hx hy),
    edgeComponents_translate]

/-- Both actual join diagonals are private singletons (including the empty
convention); their flags are derived from the complete vertical interior. -/
theorem originalVerticalClosure_join_private {n : ℕ} (P : Profile n) :
    diagLo (originalVerticalClosure P) (P.xi 0) =
        diagHi (originalVerticalClosure P) (P.xi 0) ∧
      diagLo (originalVerticalClosure P) (P.xi 0 - 1) =
        diagHi (originalVerticalClosure P) (P.xi 0 - 1) := by
  have exclude (k : ℤ) (hk : k = P.xi 0 ∨ k = P.xi 0 - 1) :
      ∀ x ∈ diagramInterior (originalVerticalClosure P), content x ≠ k := by
    intro x hx he
    rw [originalVerticalClosure_interior] at hx
    rcases Finset.mem_union.mp hx with hx | hx
    · have h := interior_content_strict P.isConnectedSkew_cells hx
      rw [P.minContent_cells, P.maxContent_cells] at h
      rcases hk with hk | hk <;> omega
    · have h := interior_content_strict P.isConnectedSkew_cells (mem_translate.mp hx)
      rw [P.minContent_cells, P.maxContent_cells] at h
      have hw := originalVerticalDisplacement_content P
      simp only [content, eCell, Prod.fst_sub, Prod.snd_sub] at h hw he
      rcases hk with hk | hk <;> omega
  exact ⟨private_diagonal_of_no_interior (originalVerticalClosure_connected P).1
    (exclude _ (Or.inl rfl)),
    private_diagonal_of_no_interior (originalVerticalClosure_connected P).1
    (exclude _ (Or.inr rfl))⟩

end SkewCornerDescent.Matrix
