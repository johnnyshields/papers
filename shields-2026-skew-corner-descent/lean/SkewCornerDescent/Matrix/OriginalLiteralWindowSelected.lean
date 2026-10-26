/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalLiteralWindowResponses
import SkewCornerDescent.Matrix.OriginalWindowSelectedEquiv

/-!
# Actual selected order between complete literal profile windows

Supports `shields-2026-skew-corner-descent.tex` (`lem:actual-words`). Complete window
cells and private cuts produce every selected counterpart in both directions. The ordered
bijection preserves literal occurrences, not only their Schur functions. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D}

/-- Every whole selected occurrence has its unique literal counterpart in the other profile. -/
theorem originalLiteralWindow_selected_occurrence {n m : ℕ} (P : Profile n) (Q : Profile m)
    (lo hi q : ℤ) (v : ℤ × ℤ)
    (hwindow : Q.cells.filter (fun x => lo + q ≤ content x ∧ content x < hi + q) =
      translate v (P.cells.filter fun x => lo ≤ content x ∧ content x < hi))
    (hlo : ∀ x ∈ diagramInterior P.cells, content x ≠ lo)
    (hloq : ∀ x ∈ diagramInterior Q.cells, content x ≠ lo + q)
    (hhi : ∀ x ∈ diagramInterior P.cells, content x ≠ hi)
    (hhiq : ∀ x ∈ diagramInterior Q.cells, content x ≠ hi + q)
    (b : OriginalSelectedBlocks (hD := hD) P)
    (hb : ∀ x ∈ interiorBlockCells P b.val.val, lo ≤ content x ∧ content x < hi) :
    ∃! d : OriginalSelectedBlocks (hD := hD) Q,
      interiorBlockCells Q d.val.val = translate v (interiorBlockCells P b.val.val) := by
  obtain ⟨d, he, _⟩ := originalLiteralWindow_nonempty_block_occurrence P Q lo hi q v
    hwindow hlo hloq hhi hhiq b.val
    (originalBlockSelected_nonempty P b.val b.property) hb
  have hd := (originalBlockSelected_translated_iff P Q b.val d.val
    (originalBlockSelected_nonempty P b.val b.property) d.property v he.symm).mp b.property
  refine ⟨⟨d.val, hd⟩, he, ?_⟩
  intro a ha
  exact originalSelectedBlock_cells_injective Q (ha.trans he.symm)

/-- The complete selected inventories of literal profile windows are order isomorphic. -/
theorem originalLiteralWindow_selected_orderIso {n m : ℕ} (P : Profile n) (Q : Profile m)
    (lo hi q : ℤ) (v : ℤ × ℤ) (hv : content v = q)
    (hwindow : Q.cells.filter (fun x => lo + q ≤ content x ∧ content x < hi + q) =
      translate v (P.cells.filter fun x => lo ≤ content x ∧ content x < hi))
    (hlo : ∀ x ∈ diagramInterior P.cells, content x ≠ lo)
    (hloq : ∀ x ∈ diagramInterior Q.cells, content x ≠ lo + q)
    (hhi : ∀ x ∈ diagramInterior P.cells, content x ≠ hi)
    (hhiq : ∀ x ∈ diagramInterior Q.cells, content x ≠ hi + q) :
    ∃ e : OriginalWindowSelected (hD := hD) P lo hi ≃o
        OriginalWindowSelected (hD := hD) Q (lo + q) (hi + q),
      ∀ b, interiorBlockCells Q (e b).val.val.val =
        translate v (interiorBlockCells P b.val.val.val) := by
  classical
  let source := OriginalWindowSelected (hD := hD) P lo hi
  let target := OriginalWindowSelected (hD := hD) Q (lo + q) (hi + q)
  have hex (b : source) : ∃ d : OriginalSelectedBlocks (hD := hD) Q,
      interiorBlockCells Q d.val.val = translate v (interiorBlockCells P b.val.val.val) :=
    (originalLiteralWindow_selected_occurrence P Q lo hi q v hwindow
      hlo hloq hhi hhiq b.val b.property).exists
  let f : source → target := fun b =>
    ⟨(hex b).choose, by
      intro x hx
      rw [(hex b).choose_spec] at hx
      have hb := b.property (x - v) (mem_translate.mp hx)
      have hc : content (x - v) = content x - q := by
        simp only [content, Prod.fst_sub, Prod.snd_sub] at hv ⊢
        omega
      rw [hc] at hb
      omega⟩
  have hf (b : source) : interiorBlockCells Q (f b).val.val.val =
      translate v (interiorBlockCells P b.val.val.val) := (hex b).choose_spec
  have hfMono : StrictMono f := by
    intro b a hba
    have ho := originalSelected_order_of_translated_cells Q P v
      (f b).val (f a).val b.val a.val (hf b).symm (hf a).symm
    exact ho.mp hba
  have hrev : P.cells.filter (fun x => lo ≤ content x ∧ content x < hi) =
      translate (-v) (Q.cells.filter fun x => lo + q ≤ content x ∧ content x < hi + q) := by
    rw [hwindow, translate_translate, neg_add_cancel, translate_zero]
  have hrev' : P.cells.filter (fun x => lo + q + -q ≤ content x ∧
      content x < hi + q + -q) =
      translate (-v) (Q.cells.filter fun x => lo + q ≤ content x ∧ content x < hi + q) := by
    simpa only [add_neg_cancel_right] using hrev
  have hlo' : ∀ x ∈ diagramInterior P.cells, content x ≠ lo + q + -q := by
    simpa only [add_neg_cancel_right] using hlo
  have hhi' : ∀ x ∈ diagramInterior P.cells, content x ≠ hi + q + -q := by
    simpa only [add_neg_cancel_right] using hhi
  have hfSurj : Function.Surjective f := by
    intro d
    obtain ⟨a, ha, _⟩ := originalLiteralWindow_selected_occurrence Q P
      (lo + q) (hi + q) (-q) (-v) hrev' hloq hlo' hhiq hhi' d.val d.property
    have hband : ∀ x ∈ interiorBlockCells P a.val.val, lo ≤ content x ∧ content x < hi := by
      intro x hx
      rw [ha] at hx
      have hd := d.property (x - -v) (mem_translate.mp hx)
      have hc : content (x - -v) = content x + q := by
        simp only [content, Prod.fst_sub, Prod.snd_sub, Prod.fst_neg, Prod.snd_neg] at hv ⊢
        omega
      rw [hc] at hd
      omega
    let b : source := ⟨a, hband⟩
    refine ⟨b, ?_⟩
    apply Subtype.ext
    apply originalSelectedBlock_cells_injective Q
    change interiorBlockCells Q (f b).val.val.val = interiorBlockCells Q d.val.val.val
    rw [hf b]
    change translate v (interiorBlockCells P a.val.val) = interiorBlockCells Q d.val.val.val
    rw [ha, translate_translate, add_neg_cancel, translate_zero]
  exact ⟨{ Equiv.ofBijective f ⟨hfMono.injective, hfSurj⟩ with
    map_rel_iff' := hfMono.le_iff_le }, hf⟩

end SkewCornerDescent.Matrix.SelectedCoordinate
