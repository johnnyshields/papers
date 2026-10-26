/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.BoundaryParentSets

/-!
# The actual first-boundary parent is the literal sorted restoration

The parent identification in `lem:boundary-core` and
`eq:boundary-beta-lists` of
`shields-2026-skew-class-inflation.tex`.  Both full beta supports and
the produced row count identify the actual inflated determinant with
the restored suffix-core determinant.  Sorry-free.
-/

namespace SkewClassInflation

open SkewJacobiNegative

/-- Transporting only the finite order leaves the whole upper beta set unchanged. -/
theorem reindexOrder_rowSet {n m : ℕ} (D : BetaDiagram n) (h : m = n) :
    (D.reindexOrder h).rowSet = D.rowSet := by cases h; rfl

/-- The corresponding whole lower beta set is unchanged under the same proved order transport. -/
theorem reindexOrder_colSet {n m : ℕ} (D : BetaDiagram n) (h : m = n) :
    (D.reindexOrder h).colSet = D.colSet := by cases h; rfl

namespace ThinParameters

variable (B : ThinParameters)

/-- The original inflated determinant is exactly the restored suffix-core parent determinant. -/
theorem boundary_schur_eq_restored {M : ℕ} (α : Composition M) (hM : 0 < M) :
    (Profile.inflate B.boundary.p (B.diagram α hM).2).toBetaDiagram.schur =
      (B.boundary.restoredParent M hM (suffixSet α) (suffixSet_subset α)).schur := by
  let D := (Profile.inflate B.boundary.p (B.diagram α hM).2).toBetaDiagram
  let E := B.boundary.restoredParent M hM (suffixSet α) (suffixSet_subset α)
  have hd := B.diagram_row_count α hM
  have hc := suffixSet_card α hM
  have hz := B.boundary.commonBetas_card (suffixSet α)
  have hn : M + 1 + (B.boundary.commonBetas (suffixSet α)).card = (B.diagram α hM).1 + 1 := by
    omega
  have hr : (D.reindexOrder hn).rowSet = E.rowSet := by
    rw [reindexOrder_rowSet]
    exact (B.boundary_rowSet α hM).trans
      (B.boundary.restoredParent_rowSet M hM _ (suffixSet_subset α)).symm
  have hl : (D.reindexOrder hn).colSet = E.colSet := by
    rw [reindexOrder_colSet]
    exact (B.boundary_colSet α hM).trans
      (B.boundary.restoredParent_colSet M hM _ (suffixSet_subset α)).symm
  have he := BetaDiagram.ext_sets (D.reindexOrder hn) E hr hl
  have hs := congrArg BetaDiagram.schur he
  simpa only [BetaDiagram.reindexOrder_schur] using hs

end ThinParameters
end SkewClassInflation
