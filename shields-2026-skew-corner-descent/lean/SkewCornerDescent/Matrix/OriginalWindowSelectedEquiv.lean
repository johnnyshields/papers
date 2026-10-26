/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.OriginalWindowSelectedOccurrences

/-!
# Ordered bijection of actual selected full-window occurrences

Supports `shields-2026-skew-corner-descent.tex` (`lem:actual-words`).
Complete windows produce a surjective ordered matching of the original selected prefix
and suffix occurrences. Its equality is literal translation of the whole component.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D}

/-- Selected source blocks wholly inside an actual content interval. -/
abbrev OriginalWindowSelected {n : ℕ} (P : Profile n) (lo hi : ℤ) :=
  {b : OriginalSelectedBlocks (hD := hD) P //
    ∀ x ∈ interiorBlockCells P b.val.val, lo ≤ content x ∧ content x < hi}

/-- Literal window equality produces the complete order isomorphism, not just an injection
of occurrences or a correspondence of their Schur-function classes. -/
theorem originalWindow_selected_orderIso {n : ℕ} (P : Profile n)
    (lo hi q : ℤ) (v : ℤ × ℤ) (hv : content v = q)
    (hprefix : IsSkew (P.cells.filter fun x => lo ≤ content x ∧ content x < hi - q))
    (hwindow : P.cells.filter (fun x => lo + q ≤ content x ∧ content x < hi) =
      translate v (P.cells.filter fun x => lo ≤ content x ∧ content x < hi - q))
    (hlo : ∀ x ∈ diagramInterior P.cells, content x ≠ lo)
    (hloq : ∀ x ∈ diagramInterior P.cells, content x ≠ lo + q)
    (hhiq : ∀ x ∈ diagramInterior P.cells, content x ≠ hi - q)
    (hhi : ∀ x ∈ diagramInterior P.cells, content x ≠ hi) :
    ∃ e : OriginalWindowSelected (hD := hD) P lo (hi - q) ≃o
        OriginalWindowSelected (hD := hD) P (lo + q) hi,
      ∀ b, interiorBlockCells P (e b).val.val.val =
        translate v (interiorBlockCells P b.val.val.val) := by
  classical
  let source := OriginalWindowSelected (hD := hD) P lo (hi - q)
  let target := OriginalWindowSelected (hD := hD) P (lo + q) hi
  have hex (b : source) : ∃ e : OriginalSelectedBlocks (hD := hD) P,
      interiorBlockCells P e.val.val = translate v (interiorBlockCells P b.val.val.val) :=
    (originalWindow_selected_occurrence P lo hi q v hprefix hwindow
      hlo hloq hhiq hhi b.val b.property).exists
  let f : source → target := fun b =>
    ⟨(hex b).choose, by
      intro x hx
      rw [(hex b).choose_spec] at hx
      have hy := mem_translate.mp hx
      have hb := b.property (x - v) hy
      have hc : content (x - v) = content x - q := by
        rw [← hv]
        simp only [content, Prod.fst_sub, Prod.snd_sub]
        ring
      rw [hc] at hb
      omega⟩
  have hf (b : source) : interiorBlockCells P (f b).val.val.val =
      translate v (interiorBlockCells P b.val.val.val) := (hex b).choose_spec
  have hfInject : Function.Injective f := by
    intro b a he
    apply Subtype.ext
    apply originalSelectedBlock_cells_injective P
    apply translate_injective v
    exact (hf b).symm.trans ((congrArg
      (fun t : target => interiorBlockCells P t.val.val.val) he).trans (hf a))
  have hfSurj : Function.Surjective f := by
    intro e
    have he : interiorBlockCells P e.val.val.val ∈
        selectedComponentInventory (hD := hD) P.cells := by
      rw [selectedComponentInventory_eq_original_image]
      exact Finset.mem_image.mpr ⟨e.val, Finset.mem_univ _, rfl⟩
    have he' : interiorBlockCells P e.val.val.val ∈
        (selectedComponentInventory (hD := hD) P.cells).filter
          (fun C => ∀ x ∈ C, lo + q ≤ content x ∧ content x < hi) :=
      Finset.mem_filter.mpr ⟨he, e.property⟩
    rw [selectedComponentInventory_literal_windows P.cells lo hi q v
      hprefix hwindow hlo hloq hhiq hhi] at he'
    obtain ⟨C, hC, hCe⟩ := Finset.mem_image.mp he'
    obtain ⟨hC, hbound⟩ := Finset.mem_filter.mp hC
    rw [selectedComponentInventory_eq_original_image] at hC
    obtain ⟨b, _, hb⟩ := Finset.mem_image.mp hC
    let a : source := ⟨b, hb ▸ hbound⟩
    refine ⟨a, ?_⟩
    apply Subtype.ext
    apply originalSelectedBlock_cells_injective P
    exact (hf a).trans ((congrArg (SkewGluing.translate v) hb).trans hCe)
  have hfMono : StrictMono f := by
    intro b a hba
    have ho := originalSelected_order_of_translated_cells P P v
      (f b).val (f a).val b.val a.val (hf b).symm (hf a).symm
    exact ho.mp hba
  let e : source ≃o target :=
    { Equiv.ofBijective f ⟨hfInject, hfSurj⟩ with map_rel_iff' := hfMono.le_iff_le }
  exact ⟨e, hf⟩

end SkewCornerDescent.Matrix.SelectedCoordinate
