/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.SquareWordRootShape
import SkewCornerDescent.EmptyLineCopies
import SkewCornerDescent.EmptyColumn

/-!
# No actual five-copy empty line root for the square word

Supports `shields-2026-skew-corner-descent.tex` (`rem:square-word`).
Actual composition area and span force the entire inner to be a translated
square. Its two possible line-copy row counts both differ from the source.
Sorry-free.
-/

namespace SkewCornerDescent.SquareWordProfiles

open SkewGluing

/-- The area/span constraint classifies the entire actual connected inner. -/
theorem four_cell_connected_span_three_square (E : Diagram) (hE : IsConnectedSkew E)
    (harea : E.card = 4) (hspan : span E = 3) :
    ∃ w, E = translate w square.cells := by
  obtain ⟨n, P, w, hp⟩ := hE.exists_profile_cells
  have hParea : ∑ i, P.r i = 4 := by
    rw [← profile_actual_area, ← original_card_translate w P.cells, ← hp]
    exact harea
  have hPspan : (P.topVar : ℕ) = 3 := by
    rw [hp, span_translate, P.span_cells_eq_topVar] at hspan
    exact hspan
  have htop := P.topVar_coe
  rw [hPspan] at htop
  norm_num at htop
  have hshape := (four_cell_span_three_square P hParea htop.symm).2
  exact ⟨w, hp.trans (congrArg (SkewGluing.translate w) hshape)⟩

/-- Any actual five-cell, span-five empty composite equal to this source
has a complete square inner. The outer's area/span facts are not inferred from a function. -/
theorem source_empty_five_inner_square (E D : Diagram)
    (hE : IsConnectedSkew E) (hD : IsConnectedSkew D)
    (hinj : Set.InjOn content (D : Set (ℤ × ℤ)))
    (hcardD : D.card = 5) (hspanD : span D = 5) (v : ℤ × ℤ)
    (heq : source.cells = translate v ((emptyMarkH E).compose D)) :
    ∃ w, E = translate w square.cells := by
  have hareaSource : source.cells.card = 20 := by decide
  have hspanSource : span source.cells = 15 := by decide
  have hc := congrArg Finset.card heq
  rw [original_card_translate, empty_compose_card E hE D hD.2.1 hinj, hcardD,
    hareaSource] at hc
  have harea : E.card = 4 := by omega
  have hp : (emptyMarkH E).period = (span E : ℤ) := by
    have h := (emptyMarkH_isLegal hE).1.span_eq
    have hw : (emptyMarkH E).width = 0 := by
      simp [MarkedInner.width, emptyMarkH, span, contents]
    simp only [hw, Nat.cast_zero, add_zero] at h
    exact h.symm
  have hs := congrArg span heq
  rw [span_translate, hspanSource] at hs
  have hs' := MarkedInner.span_compose hD (emptyMarkH_isLegal hE)
  have hw : (emptyMarkH E).width = 0 := by
    simp [MarkedInner.width, emptyMarkH, span, contents]
  rw [hspanD, hp, hw] at hs'
  have hspan : span E = 3 := by omega
  exact four_cell_connected_span_three_square E hE harea hspan

/-- Five complete horizontal square copies have six occupied original rows. -/
theorem horizontal_five_square_rows :
    (((emptyMarkH square.cells).compose (horizontalRow 5)).image Prod.fst).card = 6 := by decide

/-- Five complete vertical square copies have ten occupied original rows. -/
theorem vertical_five_square_rows :
    (((emptyMarkH square.cells).compose (verticalColumn 5)).image Prod.fst).card = 10 := by decide

/-- The actual source has neither an empty row nor an empty column five-copy root,
including every translated connected inner and every placement of the whole composite. -/
theorem source_no_actual_five_copy_line_root (E : Diagram) (hE : IsConnectedSkew E)
    (v : ℤ × ℤ) :
    source.cells ≠ translate v ((emptyMarkH E).compose (horizontalRow 5)) ∧
      source.cells ≠ translate v ((emptyMarkH E).compose (verticalColumn 5)) := by
  have hsource : (source.cells.image Prod.fst).card = 8 := by decide
  constructor
  · intro heq
    have hinj : Set.InjOn content (horizontalRow 5 : Set (ℤ × ℤ)) := by
      intro a ha b hb hab
      have ha0 := (mem_horizontalRow.mp ha).1
      have hb0 := (mem_horizontalRow.mp hb).1
      apply Prod.ext
      · exact ha0.trans hb0.symm
      · simpa only [content, ha0, hb0, sub_zero] using hab
    obtain ⟨w, hw⟩ := source_empty_five_inner_square E (horizontalRow 5) hE
      (isConnectedSkew_horizontalRow (by decide)) hinj (by decide) (by decide) v heq
    rw [hw, empty_compose_translate square.cells (horizontalRow 5)
      square.isConnectedSkew_cells.2.1 w, translate_translate] at heq
    have h := congrArg (fun S : Diagram => (S.image Prod.fst).card) heq
    rw [rowCount_translate, hsource, horizontal_five_square_rows] at h
    omega
  · intro heq
    have hinj : Set.InjOn content (verticalColumn 5 : Set (ℤ × ℤ)) := by
      intro a ha b hb hab
      have ha0 := (mem_verticalColumn.mp ha).1
      have hb0 := (mem_verticalColumn.mp hb).1
      apply Prod.ext
      · have h := hab
        simp only [content, ha0, hb0, zero_sub] at h
        exact neg_injective h
      · exact ha0.trans hb0.symm
    obtain ⟨w, hw⟩ := source_empty_five_inner_square E (verticalColumn 5) hE
      (verticalColumn_isConnectedSkew (by decide)) hinj (by decide) (by decide) v heq
    rw [hw, empty_compose_translate square.cells (verticalColumn 5)
      square.isConnectedSkew_cells.2.1 w, translate_translate] at heq
    have h := congrArg (fun S : Diagram => (S.image Prod.fst).card) heq
    rw [rowCount_translate, hsource, vertical_five_square_rows] at h
    omega

end SkewCornerDescent.SquareWordProfiles
