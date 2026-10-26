/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.VertexBetaResponse
import SkewCornerDescent.Matrix.OriginalPrivateUnitProjection

/-!
# Exact full response correction of an actual surviving private unit

Supports `shields-2026-skew-corner-descent.tex` (`prop:closure-pin`).
The source produces the complete old and new interval inverses and strict
no-feedback geometry. The full original residue response, not only its mixed
Hessian, changes by the product of the two effective cut responses. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The actual full private response has its exact unit correction. Every
remaining nonunit index and every coupling of its fresh inverse are retained. -/
theorem originalInterval_private_unit_response {n : ℕ} (P : Profile n)
    (b d : Option (OriginalSelectedBlocks (hD := hD) P)) (k : ℤ)
    (hcur : diagLo P.cells k = diagHi P.cells k)
    (hprev : diagLo P.cells (k - 1) = diagHi P.cells (k - 1))
    (u : OriginalResponseInterval (hD := hD) P b d)
    (hunit : originalResponseRows P u.1.1 = k ∧ originalResponseCols P u.1.1 = k) :
    letI := c.originalIntervalWithoutPrivateUnitInverse P b d k hcur hprev u hunit
    let row := fun i : {i : OriginalResponseInterval (hD := hD) P b d //
      ¬ (originalResponseRows P i.1.1 = k ∧ originalResponseCols P i.1.1 = k)} =>
        originalResponseRows P i.val.1.1
    let col := fun i : {i : OriginalResponseInterval (hD := hD) P b d //
      ¬ (originalResponseRows P i.1.1 = k ∧ originalResponseCols P i.1.1 = k)} =>
        originalResponseCols P i.val.1.1
    let x := P.xi (originalRowSplitEquiv (hD := hD) P (.inl b))
    let y := P.zeta (originalColSplitEquiv (hD := hD) P (.inl d))
    c.regularResidue (c.originalLocalResponse P b d) =
      vertexBetaResponse c.residueMap row col x y -
        vertexBetaResponse c.residueMap row col x k *
          vertexBetaResponse c.residueMap row col k y := by
  classical
  let := c.originalIntervalWithoutPrivateUnitInverse P b d k hcur hprev u hunit
  let row := fun i : {i : OriginalResponseInterval (hD := hD) P b d //
    ¬ (originalResponseRows P i.1.1 = k ∧ originalResponseCols P i.1.1 = k)} =>
      originalResponseRows P i.val.1.1
  let col := fun i : {i : OriginalResponseInterval (hD := hD) P b d //
    ¬ (originalResponseRows P i.1.1 = k ∧ originalResponseCols P i.1.1 = k)} =>
      originalResponseCols P i.val.1.1
  let x := P.xi (originalRowSplitEquiv (hD := hD) P (.inl b))
  let y := P.zeta (originalColSplitEquiv (hD := hD) P (.inl d))
  have hsep (i) : (row i < k ∧ col i < k) ∨ (k < row i ∧ k < col i) :=
    originalRemaining_private_cut_without_unit P k hcur hprev ⟨i.val.1.1, i.property⟩
  let e := originalIntervalPrivateUnitEquiv (hD := hD) P b d k u hunit
  let row' := Sum.elim row (fun _ : Unit => k)
  let col' := Sum.elim col (fun _ : Unit => k)
  let : Invertible (vertexBetaMatrix c.residueMap row' col') := by
    change Invertible (vertexBetaMatrix c.residueMap
      (Sum.elim row (fun _ : Unit => k)) (Sum.elim col (fun _ : Unit => k)))
    rw [vertexBetaMatrix_insert]
    exact unitVertexInverse _ _ _ (geometric_unit_vertex_feedback_zero c.residueMap row col k hsep)
  let := c.originalResponseResidueIntervalInverse P b d
  have hr (i) : originalResponseRows P (e i).1.1 = row' i := by
    rcases i with i | i
    · rfl
    · cases i
      exact hunit.1
  have hc (i) : originalResponseCols P (e i).1.1 = col' i := by
    rcases i with i | i
    · rfl
    · cases i
      exact hunit.2
  have hcopy := vertexBetaResponse_affine_reindex c.residueMap e row' col'
    (fun i => originalResponseRows P i.1.1) (fun i => originalResponseCols P i.1.1) x y 0
    (fun i => by simpa only [add_zero] using hr i)
    (fun i => by simpa only [add_zero] using hc i)
  simp only [add_zero] at hcopy
  have hfull := c.originalLocalResponse_residue_pruned P b d
  change c.regularResidue (c.originalLocalResponse P b d) =
    vertexBetaResponse c.residueMap
      (fun i : OriginalResponseInterval (hD := hD) P b d => originalResponseRows P i.1.1)
      (fun i => originalResponseCols P i.1.1) x y at hfull
  dsimp only
  rw [hfull, ← hcopy]
  exact vertexBetaResponse_unit_insert c.residueMap row col k x y hsep

end SkewCornerDescent.Matrix.SelectedCoordinate
