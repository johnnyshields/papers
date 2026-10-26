/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalLiteralWindowRows
import SkewCornerDescent.Matrix.OriginalWindowRemovedBlocks

/-!
# Whole block occurrences between literal windows of different profiles

Supports `shields-2026-skew-corner-descent.tex` (`lem:actual-words`). Private cuts
and complete parent-cell equality produce each whole connected block occurrence in the
other profile. Selection and proper-minor sizes are not matching hypotheses. Sorry-free.
-/

namespace SkewCornerDescent.Matrix

open SkewGluing

/-- Complete equal end windows match every nonempty block, with no selection assumption. -/
theorem originalLiteralWindow_nonempty_block_occurrence {n m : ℕ} (P : Profile n)
    (Q : Profile m)
    (lo hi q : ℤ) (v : ℤ × ℤ)
    (hwindow : Q.cells.filter (fun x => lo + q ≤ content x ∧ content x < hi + q) =
      translate v (P.cells.filter fun x => lo ≤ content x ∧ content x < hi))
    (hlo : ∀ x ∈ diagramInterior P.cells, content x ≠ lo)
    (hloq : ∀ x ∈ diagramInterior Q.cells, content x ≠ lo + q)
    (hhiq : ∀ x ∈ diagramInterior P.cells, content x ≠ hi)
    (hhi : ∀ x ∈ diagramInterior Q.cells, content x ≠ hi + q)
    (b : OriginalBlocks P) (hb : P.zeta b.val.castSucc < P.xi b.val.succ)
    (hband : ∀ x ∈ interiorBlockCells P b.val, lo ≤ content x ∧ content x < hi) :
    ∃! d : {d : OriginalBlocks Q // Q.zeta d.val.castSucc < Q.xi d.val.succ},
      interiorBlockCells Q d.val.val = translate v (interiorBlockCells P b.val) := by
  classical
  have hc : interiorBlockCells P b.val ∈
      edgeComponents (diagramInterior (P.cells.filter
        fun x => lo ≤ content x ∧ content x < hi)) := by
    rw [interior_content_filter P.cells (fun k => lo ≤ k ∧ k < hi),
      edgeComponents_interval_of_gaps lo (hi) hlo hhiq, Finset.mem_filter]
    exact ⟨interiorBlockCells_mem_components P b.val hb, hband⟩
  have hct : translate v (interiorBlockCells P b.val) ∈
      edgeComponents (diagramInterior (Q.cells.filter
        fun x => lo + q ≤ content x ∧ content x < hi + q)) := by
    rw [hwindow, interior_translate, edgeComponents_translate]
    exact Finset.mem_image.mpr ⟨_, hc, rfl⟩
  rw [interior_content_filter Q.cells (fun k => lo + q ≤ k ∧ k < hi + q),
    edgeComponents_interval_of_gaps (lo + q) (hi + q) hloq hhi, Finset.mem_filter] at hct
  obtain ⟨d, hd, he⟩ := exists_originalBlock_of_component Q _ hct.1
  refine ⟨⟨d, hd⟩, he, ?_⟩
  intro e he'
  apply Subtype.ext
  exact originalBlock_nonempty_cells_unique Q e.val d e.property hd (he'.trans he.symm)
end SkewCornerDescent.Matrix
