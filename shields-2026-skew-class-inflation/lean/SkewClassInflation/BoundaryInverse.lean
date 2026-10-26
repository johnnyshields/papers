/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.BoundaryBridge
import SkewClassInflation.NoEscape

/-!
# Two observations reconstruct the actual full beta diagram

Formalizes the consumed sibling theorem `eq:boundary-reconstruction-input`
in `shields-2026-skew-class-inflation.tex`.  The reconstruction theorem is
proved in the copied dependency, not carried as a hypothesis.  Rational
polynomial equality is reflected through the injective integral coefficient
extension before that theorem is invoked.  Sorry-free.
-/

namespace SkewClassInflation

open SkewJacobiNegative

/-- Delete the entire first row without canceling any common beta entry. -/
def firstRowTail {n : ℕ} (D : BetaDiagram (n + 1)) : BetaDiagram n where
  row i := D.row i.succ
  col i := D.col i.succ
  row_strictAnti := D.row_strictAnti.comp_strictMono Fin.strictMono_succ
  col_strictAnti := D.col_strictAnti.comp_strictMono Fin.strictMono_succ
  row_nonempty i := D.row_nonempty i.succ

/-- The partition realization is connected whenever the original full board is connected. -/
theorem boundary_realization_connected {n : ℕ} (D : BetaDiagram n) (hD : D.Connected) :
    (D.toDiagram hD.1).Connected := by
  apply (BetaDiagram.ofDiagram_connected_iff _).mp
  obtain ⟨c, hr, hc⟩ := D.ofDiagram_toDiagram_translation hD.1
  refine ⟨hD.1, ?_⟩
  intro i hi
  have ho := hD.2 i hi
  have h1 := hr ⟨i.val + 1, hi⟩
  have h2 := hc i
  omega

/-- First-row deletion commutes with the genuine integral/rational determinant bridge. -/
theorem boundary_realization_tail_schur {n : ℕ} (D : BetaDiagram (n + 1))
    (hn : 0 < n + 1) :
    integerLift (D.toDiagram hn).deleteFirstRow.schurFunction = (firstRowTail D).schur := by
  rw [SkewSchurReconstruction.Diagram.schurFunction_eq_jacobiTrudiDet, integerLift_det]
  apply congrArg Matrix.det
  apply Matrix.ext
  intro i j
  have hi := D.row_nonempty i.succ
  have hci := D.translated_col_nonneg hn i.succ
  have hcj := D.translated_col_nonneg hn j.succ
  change complete
    (((D.row i.succ - D.bottomCol hn + i.succ.val).toNat : ℤ) -
      (D.col j.succ - D.bottomCol hn + j.succ.val).toNat - i.val + j.val) =
    complete (D.row i.succ - D.col j.succ)
  congr 1
  simp only [Fin.val_succ] at *
  omega

/-- The sibling's boundary inverse now applies directly to the manuscript's full beta lists. -/
theorem boundary_reconstruction {n : ℕ} (D E : BetaDiagram (n + 1))
    (hD : D.Connected) (hE : E.Connected) (he : D.schur = E.schur)
    (ht : (firstRowTail D).schur = (firstRowTail E).schur) :
    D.TranslationEquivalent E := by
  have hs : (D.toDiagram hD.1).schurFunction = (E.toDiagram hE.1).schurFunction := by
    apply integerLift_injective
    simpa only [BetaDiagram.toDiagram_schur] using he
  have hchild : (D.toDiagram hD.1).deleteFirstRow.schurFunction =
      (E.toDiagram hE.1).deleteFirstRow.schurFunction := by
    apply integerLift_injective
    simpa only [boundary_realization_tail_schur] using ht
  obtain ⟨_, t, hbound⟩ := SkewSchurReconstruction.Diagram.boundary_reconstruction_deletion
    (D.toDiagram hD.1) (E.toDiagram hE.1)
    (boundary_realization_connected D hD) (boundary_realization_connected E hE) hs hchild
  refine ⟨t + D.bottomCol hD.1 - E.bottomCol hE.1, ?_, ?_⟩
  · intro i
    have hb := (hbound i i rfl).1
    have hDrow := D.row_nonempty i
    have hErow := E.row_nonempty i
    have hDc := D.translated_col_nonneg hD.1 i
    have hEc := E.translated_col_nonneg hE.1 i
    change ((D.row i - D.bottomCol hD.1 + i.val).toNat : ℤ) =
      (E.row i - E.bottomCol hE.1 + i.val).toNat + t at hb
    omega
  · intro i
    have hb := (hbound i i rfl).2
    have hDc := D.translated_col_nonneg hD.1 i
    have hEc := E.translated_col_nonneg hE.1 i
    change ((D.col i - D.bottomCol hD.1 + i.val).toNat : ℤ) =
      (E.col i - E.bottomCol hE.1 + i.val).toNat + t at hb
    omega

end SkewClassInflation
