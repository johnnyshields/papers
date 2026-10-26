/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.OriginalComponentSelection
import SkewCornerDescent.Matrix.OriginalHessenbergInventory

/-!
# Selected whole-component inventories

Supports `shields-2026-skew-corner-descent.tex`, «Actual responses and residue classes»
(`sec:normal-chart`, `lem:actual-words`). Selection is exact function equality on whole
geometric components. Different occurrences remain different inventory members, even
when their Schur functions coincide. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

attribute [local instance] Classical.propDecidable

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Whole geometric occurrences with the selected function, not a set of function classes. -/
noncomputable def selectedComponentInventory (X : Diagram) : Finset Diagram :=
  (edgeComponents (diagramInterior X)).filter fun C =>
    ∃ hC : IsSkew C, cellSchur D hD.1 = cellSchur C hC

/-- The inventory predicate retains the original geometric component witness. -/
theorem mem_selectedComponentInventory (X C : Diagram) :
    C ∈ selectedComponentInventory (hD := hD) X ↔
      C ∈ edgeComponents (diagramInterior X) ∧
        ∃ hC : IsSkew C, cellSchur D hD.1 = cellSchur C hC := by
  simp only [selectedComponentInventory, Finset.mem_filter]

/-- Canonical selected blocks cannot describe the same nonempty occurrence twice. -/
theorem originalSelectedBlock_cells_injective {n : ℕ} (P : Profile n) :
    Function.Injective (fun b : OriginalSelectedBlocks (hD := hD) P =>
      interiorBlockCells P b.val.val) := by
  intro b e he
  change interiorBlockCells P b.val.val = interiorBlockCells P e.val.val at he
  have hb := originalBlockSelected_nonempty P b.val b.property
  obtain ⟨x, hx⟩ := (interiorBlockCells_connected P b.val.val hb).2.1
  obtain ⟨r, s⟩ := x
  have hx' := hx
  rw [he] at hx'
  obtain ⟨i, hi, hr, _, _⟩ := (mem_interiorBlockCells P b.val.val r s).mp hx
  obtain ⟨j, hj, hs, _, _⟩ := (mem_interiorBlockCells P e.val.val r s).mp hx'
  have hij : i = j := by
    apply Fin.ext
    omega
  have hlabel : interiorBlock P b.val.val = interiorBlock P e.val.val := by
    rw [← hi, ← hj, hij]
  exact Subtype.ext (originalBlocks_label_injective P hlabel)

/-- Every selected whole occurrence occurs once in the actual source block enumeration. -/
theorem selectedComponentInventory_eq_original_image {n : ℕ} (P : Profile n) :
    selectedComponentInventory (hD := hD) P.cells =
      Finset.univ.image (fun b : OriginalSelectedBlocks (hD := hD) P =>
        interiorBlockCells P b.val.val) := by
  ext C
  rw [mem_selectedComponentInventory, Finset.mem_image]
  constructor
  · rintro ⟨hC, hs, he⟩
    obtain ⟨b, hb⟩ := exists_originalSelectedBlock_of_component (hD := hD) P C hC he
    exact ⟨b, Finset.mem_univ _, hb⟩
  · rintro ⟨b, _, rfl⟩
    have hb := originalBlockSelected_nonempty P b.val b.property
    refine ⟨interiorBlockCells_mem_components P b.val.val hb,
      (interiorBlockCells_connected P b.val.val hb).1, ?_⟩
    exact (dvd_originalBlock_iff (hD := hD) P b.val.val hb).mp b.property

/-- The literal selected count is the cardinality of the whole-component inventory. -/
theorem selectedComponentInventory_card {n : ℕ} (P : Profile n) :
    (selectedComponentInventory (hD := hD) P.cells).card =
      originalSelectedCount (hD := hD) P := by
  rw [selectedComponentInventory_eq_original_image,
    Finset.card_image_of_injective _ (originalSelectedBlock_cells_injective P)]
  exact Finset.card_univ

/-- Literal translation preserves selected occurrences and their complete functions. -/
theorem selectedComponentInventory_translate (X : Diagram) (hX : IsSkew X) (v : ℤ × ℤ) :
    selectedComponentInventory (hD := hD) (translate v X) =
      (selectedComponentInventory (hD := hD) X).image (SkewGluing.translate v) := by
  ext C
  simp only [mem_selectedComponentInventory, interior_translate,
    edgeComponents_translate, Finset.mem_image]
  constructor
  · rintro ⟨⟨E, hE, rfl⟩, hs, he⟩
    have hEs := isSkew_component hX.interior hE
    exact ⟨E, ⟨hE, hEs, he.trans (cellSchur_translate E hEs v)⟩, rfl⟩
  · rintro ⟨E, ⟨hE, hs, he⟩, rfl⟩
    exact ⟨⟨E, hE, rfl⟩, isSkew_translate v hs,
      he.trans (cellSchur_translate E hs v).symm⟩

/-- The horizontal closure retains both complete selected inventories before taking classes. -/
theorem originalHorizontalClosure_selected_inventory {n : ℕ} (P : Profile n) :
    selectedComponentInventory (hD := hD) (originalHorizontalClosure P) =
      selectedComponentInventory (hD := hD) P.cells ∪
        (selectedComponentInventory (hD := hD) P.cells).image (translate (vH P.cells)) := by
  ext C
  simp only [mem_selectedComponentInventory, originalHorizontalClosure_components,
    Finset.mem_union, Finset.mem_image]
  constructor
  · rintro ⟨hC | hC, hs, he⟩
    · exact Or.inl ⟨hC, hs, he⟩
    · obtain ⟨E, hE, rfl⟩ := hC
      have hEs := isSkew_component P.isConnectedSkew_cells.1.interior hE
      refine Or.inr ⟨E, ⟨hE, hEs, ?_⟩, rfl⟩
      exact he.trans (cellSchur_translate E hEs (vH P.cells))
  · rintro (hC | ⟨E, hE, rfl⟩)
    · exact hC.imp_left Or.inl
    · obtain ⟨hE, hs, he⟩ := hE
      refine ⟨Or.inr ⟨E, hE, rfl⟩,
        isSkew_translate (vH P.cells) hs, ?_⟩
      exact he.trans (cellSchur_translate E hs (vH P.cells)).symm

/-- Repeated selected functions in different closure copies contribute twice to the count. -/
theorem originalHorizontalClosure_selected_card {n : ℕ} (P : Profile n) :
    (selectedComponentInventory (hD := hD) (originalHorizontalClosure P)).card =
      2 * originalSelectedCount (hD := hD) P := by
  have hsub : selectedComponentInventory (hD := hD) P.cells ⊆
      edgeComponents (diagramInterior P.cells) := Finset.filter_subset _ _
  have hdisj := (originalHorizontalClosure_component_disjoint P).mono hsub
    (Finset.image_subset_image hsub)
  rw [originalHorizontalClosure_selected_inventory, Finset.card_union_of_disjoint hdisj,
    Finset.card_image_of_injective _ (fun _ _ h => translate_injective _ h),
    selectedComponentInventory_card]
  omega

/-- Every translated profile of the literal closure has twice the original selected count. -/
theorem originalHorizontalClosure_profile_selected_count {n m : ℕ}
    (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalHorizontalClosure P = translate v Q.cells) :
    originalSelectedCount (hD := hD) Q = 2 * originalSelectedCount (hD := hD) P := by
  have hcard := originalHorizontalClosure_selected_card (hD := hD) P
  rw [hQ, selectedComponentInventory_translate Q.cells Q.isConnectedSkew_cells.1 v,
    Finset.card_image_of_injective _ (fun _ _ h => translate_injective _ h),
    selectedComponentInventory_card] at hcard
  exact hcard

end SkewCornerDescent.Matrix.SelectedCoordinate
