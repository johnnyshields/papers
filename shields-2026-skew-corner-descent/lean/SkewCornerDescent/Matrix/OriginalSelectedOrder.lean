/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.OriginalSelectedInventory

/-!
# Source order of selected whole components

Supports `shields-2026-skew-corner-descent.tex`, «Actual responses and residue classes»
(`sec:normal-chart`, `lem:actual-words`). Literal least contents determine the actual
selected occurrence order. Translation matches occurrences without identifying different
occurrences of the same function. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

attribute [local instance] Classical.propDecidable

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The actual selected source order is strictly opposite to least-content order. -/
theorem originalSelected_minContent_strictAnti {n : ℕ} (P : Profile n) :
    StrictAnti (fun b : OriginalSelectedBlocks (hD := hD) P =>
      minContent (interiorBlockCells P b.val.val)) := by
  intro b e hbe
  obtain ⟨coord⟩ := exists_selectedCoordinate hD
  have hij := (originalSelectedEnumeration (hD := hD) P).symm.strictMono hbe
  have hlabels := originalSelectedEnumeration_label_strictMono P hij
  simp only [OrderIso.apply_symm_apply] at hlabels
  have hg := coord.originalSelected_gap_gt_top P b e hlabels
  change minContent (interiorBlockCells P e.val.val) <
    minContent (interiorBlockCells P b.val.val)
  rw [interiorBlockCells_minContent P b.val.val
    (originalBlockSelected_nonempty P b.val b.property),
    interiorBlockCells_minContent P e.val.val
      (originalBlockSelected_nonempty P e.val e.property)]
  have hpos := coord.top.pos
  omega

/-- Least-content comparison is equivalent to comparison of the actual selected blocks. -/
theorem originalSelected_lt_iff_minContent {n : ℕ} (P : Profile n)
    (b e : OriginalSelectedBlocks (hD := hD) P) :
    b < e ↔ minContent (interiorBlockCells P e.val.val) <
      minContent (interiorBlockCells P b.val.val) := by
  constructor
  · intro h
    exact originalSelected_minContent_strictAnti P h
  · intro h
    rcases lt_trichotomy b e with hbe | hbe | heb
    · exact hbe
    · subst e
      exact False.elim (lt_irrefl _ h)
    · exact False.elim (lt_asymm h (originalSelected_minContent_strictAnti P heb))

/-- Matching two whole translated occurrences produces the same source order on both sides. -/
theorem originalSelected_order_of_translated_cells {n m : ℕ}
    (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (b e : OriginalSelectedBlocks (hD := hD) P)
    (b' e' : OriginalSelectedBlocks (hD := hD) Q)
    (hb : translate v (interiorBlockCells Q b'.val.val) = interiorBlockCells P b.val.val)
    (he : translate v (interiorBlockCells Q e'.val.val) = interiorBlockCells P e.val.val) :
    b' < e' ↔ b < e := by
  have hminb := congrArg minContent hb
  have hmine := congrArg minContent he
  rw [minContent_translate (interiorBlockCells_connected Q b'.val.val
    (originalBlockSelected_nonempty Q b'.val b'.property)).2.1] at hminb
  rw [minContent_translate (interiorBlockCells_connected Q e'.val.val
    (originalBlockSelected_nonempty Q e'.val e'.property)).2.1] at hmine
  rw [originalSelected_lt_iff_minContent Q, originalSelected_lt_iff_minContent P]
  omega

/-- An intact translated selected component has one and only one canonical source occurrence. -/
theorem existsUnique_originalSelectedBlock_of_translated_component {n : ℕ} (P : Profile n)
    (v : ℤ × ℤ) (C : Diagram)
    (hC : C ∈ edgeComponents (diagramInterior (translate v P.cells)))
    (he : cellSchur D hD.1 = cellSchur C
      (isSkew_component (isSkew_translate v P.isConnectedSkew_cells.1).interior hC)) :
    ∃! b : OriginalSelectedBlocks (hD := hD) P,
      translate v (interiorBlockCells P b.val.val) = C := by
  obtain ⟨b, hb⟩ := exists_originalSelectedBlock_of_translated_component (hD := hD) P v C hC he
  refine ⟨b, hb, ?_⟩
  intro e he
  exact originalSelectedBlock_cells_injective P (translate_injective v (he.trans hb.symm))

end SkewCornerDescent.Matrix.SelectedCoordinate
