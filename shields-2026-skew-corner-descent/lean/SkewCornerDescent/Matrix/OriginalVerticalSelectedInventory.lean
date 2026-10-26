/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalSelectedInventory
import SkewCornerDescent.Matrix.OriginalVerticalInterior

/-!
# Complete actual selected inventory of the vertical closure

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
The two full interior copies remain disjoint in their original content bands.
Every selected occurrence is counted before taking response classes.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix

open SkewGluing

/-- The two complete vertical component inventories have no common literal occurrence. -/
theorem originalVerticalClosure_component_disjoint {n : ℕ} (P : Profile n) :
    Disjoint (edgeComponents (diagramInterior P.cells))
      ((edgeComponents (diagramInterior P.cells)).image (translate (vH P.cells - eCell))) := by
  rw [Finset.disjoint_left]
  intro C hC hC'
  obtain ⟨E, hE, he⟩ := Finset.mem_image.mp hC'
  obtain ⟨x, hx⟩ := (isEdgeConnected_component hC).1
  have hx0 := component_subset hC hx
  have hx1 : x ∈ translate (vH P.cells - eCell) (diagramInterior P.cells) := by
    rw [← he] at hx
    exact mem_translate.mpr (component_subset hE (mem_translate.mp hx))
  have ha := interior_content_strict P.isConnectedSkew_cells hx0
  have hb := interior_content_strict P.isConnectedSkew_cells (mem_translate.mp hx1)
  rw [P.minContent_cells, P.maxContent_cells] at ha hb
  have hw := originalVerticalDisplacement_content P
  simp only [content, Prod.fst_sub, Prod.snd_sub] at ha hb hw
  omega

namespace SelectedCoordinate

variable {D : Diagram} {hD : IsConnectedSkew D}

/-- The vertical closure retains both complete selected inventories before taking classes. -/
theorem originalVerticalClosure_selected_inventory {n : ℕ} (P : Profile n) :
    selectedComponentInventory (hD := hD) (originalVerticalClosure P) =
      selectedComponentInventory (hD := hD) P.cells ∪
        (selectedComponentInventory (hD := hD) P.cells).image (translate (vH P.cells - eCell)) := by
  ext C
  simp only [mem_selectedComponentInventory, originalVerticalClosure_components,
    Finset.mem_union, Finset.mem_image]
  constructor
  · rintro ⟨hC | hC, hs, he⟩
    · exact Or.inl ⟨hC, hs, he⟩
    · obtain ⟨E, hE, rfl⟩ := hC
      have hEs := isSkew_component P.isConnectedSkew_cells.1.interior hE
      refine Or.inr ⟨E, ⟨hE, hEs, ?_⟩, rfl⟩
      exact he.trans (cellSchur_translate E hEs (vH P.cells - eCell))
  · rintro (hC | ⟨E, hE, rfl⟩)
    · exact hC.imp_left Or.inl
    · obtain ⟨hE, hs, he⟩ := hE
      refine ⟨Or.inr ⟨E, hE, rfl⟩,
        isSkew_translate (vH P.cells - eCell) hs, ?_⟩
      exact he.trans (cellSchur_translate E hs (vH P.cells - eCell)).symm

/-- Repeated selected functions in different closure copies contribute twice to the count. -/
theorem originalVerticalClosure_selected_card {n : ℕ} (P : Profile n) :
    (selectedComponentInventory (hD := hD) (originalVerticalClosure P)).card =
      2 * originalSelectedCount (hD := hD) P := by
  have hsub : selectedComponentInventory (hD := hD) P.cells ⊆
      edgeComponents (diagramInterior P.cells) := Finset.filter_subset _ _
  have hdisj := (originalVerticalClosure_component_disjoint P).mono hsub
    (Finset.image_subset_image hsub)
  rw [originalVerticalClosure_selected_inventory, Finset.card_union_of_disjoint hdisj,
    Finset.card_image_of_injective _ (fun _ _ h => translate_injective _ h),
    selectedComponentInventory_card]
  omega

/-- Every translated profile of the literal closure has twice the original selected count. -/
theorem originalVerticalClosure_profile_selected_count {n m : ℕ}
    (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalVerticalClosure P = translate v Q.cells) :
    originalSelectedCount (hD := hD) Q = 2 * originalSelectedCount (hD := hD) P := by
  have hcard := originalVerticalClosure_selected_card (hD := hD) P
  rw [hQ, selectedComponentInventory_translate Q.cells Q.isConnectedSkew_cells.1 v,
    Finset.card_image_of_injective _ (fun _ _ h => translate_injective _ h),
    selectedComponentInventory_card] at hcard
  exact hcard

end SelectedCoordinate
end SkewCornerDescent.Matrix
