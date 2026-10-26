/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.SquareWordNoRoot
import SkewCornerDescent.SquareWordCoordinate

/-!
# Actual ordinary full private windows of the square word

Supports `shields-2026-skew-corner-descent.tex` (`rem:square-word`).
Both full windows, vertical private attachments, connected removals, maximality,
and the entire periodic hatted nonadjacency condition are proved. Sorry-free.
-/

namespace SkewCornerDescent.SquareWordProfiles

open SkewGluing

/-- The actual ordinary vertical/vertical shared-window mark. -/
def marked : MarkedInner where
  E := source.cells
  W := translate (5,5) window.cells
  v := (-5,4)
  case := .b

private def upperRemainder : Profile 4 where
  r := ![2,4,2,2,2]
  g := ![1,1,0,1]
  r_pos := by decide
  g_lt_castSucc := by decide
  g_lt_succ := by decide

private def lowerRemainder : Profile 4 where
  r := ![2,2,2,4,2]
  g := ![1,0,1,1]
  r_pos := by decide
  g_lt_castSucc := by decide
  g_lt_succ := by decide

/-- Every original cell on the lower complete window's contents belongs to that window. -/
theorem marked_lower_full : marked.W = source.cells.filter (fun x => content x < 6) := by decide

/-- The upper copy is the whole other actual two-copy window. -/
theorem marked_upper_full : marked.upper = translate (0,9) window.cells := by decide

/-- Both genuine private attachment edges are vertical. -/
theorem marked_vertical_edges : marked.LowerV ∧ marked.UpperV := by
  constructor
  · exact ⟨(4,10), by decide, by decide, by decide⟩
  · exact ⟨(3,11), by decide, by decide, by decide⟩

/-- The marked source is actually well formed, without supplied attachment flags. -/
theorem marked_wellFormed : marked.IsWellFormed := by
  refine ⟨source.isConnectedSkew_cells, Or.inr ?_⟩
  refine ⟨⟨(7,7), by decide⟩, isConnectedSkew_translate (5,5) window.isConnectedSkew_cells,
    by decide, by decide, by decide, by decide, ?_⟩
  simp only [MarkedInner.AttachmentMatches, marked]
  exact ⟨by simp, fun _ => marked_vertical_edges, by simp, by simp⟩

private theorem marked_window_contents : contents marked.W = Finset.Icc 0 5 := by decide

/-- Fullness itself makes enlargement on the same contents impossible. -/
theorem marked_maximal : marked.IsMaximal := by
  intro W hW hstrict _ hcontents _ _
  have hsub : W ⊆ marked.W := by
    intro x hx
    have hxE := (Finset.mem_powerset.mp hW) hx
    have hxc : content x ∈ contents W := Finset.mem_image.mpr ⟨x, hx, rfl⟩
    rw [hcontents, marked_window_contents, Finset.mem_Icc] at hxc
    rw [marked_lower_full]
    exact Finset.mem_filter.mpr ⟨hxE, by omega⟩
  have hlt := Finset.card_lt_card hstrict
  have hle := Finset.card_le_card hsub
  omega

/-- Removing either whole original end window leaves an actual connected skew diagram. -/
theorem marked_removals_connected : marked.RemovalsConnected := by
  have hl : marked.E \ marked.W = translate (0,6) upperRemainder.cells := by decide
  have hu : marked.E \ marked.upper = translate (3,3) lowerRemainder.cells := by decide
  exact ⟨hl.symm ▸ isConnectedSkew_translate (0,6) upperRemainder.isConnectedSkew_cells,
    hu.symm ▸ isConnectedSkew_translate (3,3) lowerRemainder.isConnectedSkew_cells⟩

/-- The actual middle has precisely its one protected interior cell. -/
theorem marked_middle_interior : diagramInterior marked.middle = {(3,10)} := by decide

/-- Periodic hatted copies stay nonadjacent for every pair of integer shifts. -/
theorem marked_noHatAdjacency : marked.NoHatAdjacency := by
  intro k m x hx y hy hxy
  have hv : content marked.v = 9 := by decide
  change x ∈ translate (k • marked.v) marked.middle ∧
    x + eCell ∈ translate (k • marked.v) marked.middle at hx
  have hx' : x - k • marked.v ∈ diagramInterior marked.middle := by
    apply Finset.mem_filter.mpr
    refine ⟨mem_translate.mp hx.1, ?_⟩
    have h := mem_translate.mp hx.2
    simpa only [show x + eCell - k • marked.v = x - k • marked.v + eCell by abel] using h
  rw [marked_middle_interior, Finset.mem_singleton] at hx'
  have hcx := congrArg content hx'
  rw [MarkedInner.content_sub, MarkedInner.content_smul, hv] at hcx
  have hcy : 0 ≤ content y - m * 9 ∧ content y - m * 9 ≤ 5 := by
    change (y ∈ marked.periodicUnion ∧ y + eCell ∈ translate (m • marked.v) marked.W) ∨
      (y ∈ translate (m • marked.v) marked.W ∧ y + eCell ∈ marked.periodicUnion) at hy
    rcases hy with h | h
    · have hz := mem_translate.mp h.2
      have hc : content (y + eCell - m • marked.v) ∈ contents marked.W :=
        Finset.mem_image.mpr ⟨_, hz, rfl⟩
      rw [marked_window_contents, Finset.mem_Icc] at hc
      simpa only [MarkedInner.content_sub, MarkedInner.content_smul, hv,
        MarkedInner.content_eCell_add] using hc
    · have hz := mem_translate.mp h.1
      have hc : content (y - m • marked.v) ∈ contents marked.W :=
        Finset.mem_image.mpr ⟨_, hz, rfl⟩
      rw [marked_window_contents, Finset.mem_Icc] at hc
      simpa only [MarkedInner.content_sub, MarkedInner.content_smul, hv] using hc
  have hadj : content x = content y + 1 ∨ content y = content x + 1 := by
    rw [cellAdj_iff] at hxy
    simp only [content]
    omega
  have hcval : content x = 7 + k * 9 := by
    change content x - k * 9 = 10 - 3 at hcx
    omega
  omega

/-- The complete square-word mark satisfies every original legality condition. -/
theorem marked_isLegal : marked.IsLegal := by
  exact ⟨marked_wellFormed, marked_maximal, by decide,
    marked_removals_connected, marked_noHatAdjacency⟩

/-- The literal private diagonals are both singleton cuts. -/
theorem marked_private_diagonals :
    diagLo source.cells 6 = diagHi source.cells 6 ∧
      diagLo source.cells 9 = diagHi source.cells 9 := by decide

/-- The whole actual upper window is the translation of the whole lower window. -/
theorem marked_complete_window_match :
    source.cells.filter (fun x => 9 ≤ content x ∧ content x < 15) =
      translate (-5,4) (source.cells.filter (fun x => 0 ≤ content x ∧ content x < 6)) := by
  decide

/-- The full original row amalgamation is the actual normalized union profile. -/
theorem marked_amalgamation_profile :
    marked.compose (horizontalRow 2) = translate (-5,-5) amalgamation.cells := by decide

/-- The complete actual horizontal source closure has the displayed normalized profile. -/
theorem source_actual_horizontal_closure :
    SkewCornerDescent.Matrix.originalHorizontalClosure source =
      translate (-7,-7) closure.cells := by decide

/-- The square's complete original corner cofactor is the selected one-cell prime. -/
theorem square_original_cofactor :
    (jtMatrix (fun i : Fin 1 => square.xi i.succ)
      (fun j => square.zeta j.castSucc)).det = MvPolynomial.X (1 : ℕ+) := by
  rw [Matrix.det_unique]
  change hh (square.xi 1 - square.zeta 0) = _
  have hi : square.xi 1 - square.zeta 0 = 1 := by decide
  rw [hi]
  norm_num [hh, hPos]

/-- The actual square interior is a translated copy of the selected one-cell diagram. -/
theorem square_selected_interior :
    diagramInterior square.cells = translate (0,1) selectedCell.cells := by decide

end SkewCornerDescent.SquareWordProfiles
