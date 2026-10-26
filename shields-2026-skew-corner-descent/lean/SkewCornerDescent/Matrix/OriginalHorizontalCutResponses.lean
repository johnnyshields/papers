/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.VertexCutResponse
import SkewCornerDescent.Matrix.OriginalHorizontalJoinCapVectors

/-!
# Complete effective join responses are the actual source caps

Supports `shields-2026-skew-corner-descent.tex` (`prop:closure-pin`).
Strict original beta geometry localizes each full cut response to its own
retained side. Complete source-cap list transport then identifies the whole
rational function with the actual exterior-cap response. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The entire effective response into the horizontal join is the actual
source lower cap, including all off-diagonal entries of full unit inverses. -/
theorem originalHorizontalClosure_into_cut_response {n m : ℕ}
    (P : Profile n) (H : Profile m) (v : ℤ × ℤ)
    (hH : originalHorizontalClosure P = translate v H.cells)
    (b d : OriginalSelectedBlocks (hD := hD) P) :
    let bH := originalHorizontalClosureSelectedCopy P H v hH true b
    let dH := originalHorizontalClosureSelectedCopy P H v hH false d
    letI := c.originalResponseResidueIntervalInverse H (some bH) (some dH)
    let row := fun i : OriginalResponseInterval (hD := hD) H (some bH) (some dH) =>
      originalResponseRows H i.1.1
    let col := fun i : OriginalResponseInterval (hD := hD) H (some bH) (some dH) =>
      originalResponseCols H i.1.1
    vertexBetaResponse c.residueMap row col
        (H.xi (originalRowSplitEquiv (hD := hD) H (.inl (some bH)))) (P.xi 0) =
      c.regularResidue (c.originalLocalResponse P (some b) none) := by
  classical
  intro bH dH
  let row := fun i : OriginalResponseInterval (hD := hD) H (some bH) (some dH) =>
    originalResponseRows H i.1.1
  let col := fun i : OriginalResponseInterval (hD := hD) H (some bH) (some dH) =>
    originalResponseCols H i.1.1
  let := c.originalResponseResidueIntervalInverse H (some bH) (some dH)
  let := c.originalResponseResidueIntervalInverse P (some b) none
  have hpriv := originalHorizontalClosure_profile_join_private P H v hH
  have hsep (i) : (row i < P.xi 0 ∧ col i < P.xi 0) ∨
      (P.xi 0 < row i ∧ P.xi 0 < col i) :=
    originalRemaining_private_cut_without_unit H (P.xi 0) hpriv.1 hpriv.2
      ⟨i.1.1, fun h => originalHorizontalClosure_join_no_unit P H v hH i.1.1 h.2⟩
  let := vertexAboveBetaInverse c.residueMap row col (P.xi 0) hsep
  obtain ⟨e, he⟩ := originalHorizontalClosure_above_cap_vectors P H v hH b d
  let rowP := fun i : OriginalResponseInterval (hD := hD) P (some b) none =>
    originalResponseRows P i.1.1
  let colP := fun i : OriginalResponseInterval (hD := hD) P (some b) none =>
    originalResponseCols P i.1.1
  let x := P.xi (originalRowSplitEquiv (hD := hD) P (.inl (some b)))
  have hcopy := vertexBetaResponse_affine_reindex c.residueMap e rowP colP
    (fun i => row i.val) (fun i => col i.val) x 0 (P.xi 0)
    (fun i => (he i).1) (fun i => (he i).2)
  simp only [zero_add] at hcopy
  have hx := (originalHorizontalClosure_retained_endpoints P H v hH true b).1
  simp only [originalClosureBlockDisplacement, ↓reduceIte, sub_zero] at hx
  have hsource := c.originalLocalResponse_residue_pruned P (some b) none
  change c.regularResidue (c.originalLocalResponse P (some b) none) =
    vertexBetaResponse c.residueMap rowP colP x
      (P.zeta (originalColSplitEquiv (hD := hD) P (.inl none))) at hsource
  rw [originalColSplitEquiv_corner, P.zeta_last] at hsource
  dsimp only
  rw [vertexBetaResponse_into_cut c.residueMap row col (P.xi 0) _ hsep, hx,
    ← hcopy, ← hsource]

/-- The entire effective response out of the horizontal join is the actual
source upper cap, with its complete retained inverse supplied. -/
theorem originalHorizontalClosure_out_of_cut_response {n m : ℕ}
    (P : Profile n) (H : Profile m) (v : ℤ × ℤ)
    (hH : originalHorizontalClosure P = translate v H.cells)
    (b d : OriginalSelectedBlocks (hD := hD) P) :
    let bH := originalHorizontalClosureSelectedCopy P H v hH true b
    let dH := originalHorizontalClosureSelectedCopy P H v hH false d
    letI := c.originalResponseResidueIntervalInverse H (some bH) (some dH)
    let row := fun i : OriginalResponseInterval (hD := hD) H (some bH) (some dH) =>
      originalResponseRows H i.1.1
    let col := fun i : OriginalResponseInterval (hD := hD) H (some bH) (some dH) =>
      originalResponseCols H i.1.1
    vertexBetaResponse c.residueMap row col (P.xi 0)
        (H.zeta (originalColSplitEquiv (hD := hD) H (.inl (some dH)))) =
      c.regularResidue (c.originalLocalResponse P none (some d)) := by
  classical
  intro bH dH
  let row := fun i : OriginalResponseInterval (hD := hD) H (some bH) (some dH) =>
    originalResponseRows H i.1.1
  let col := fun i : OriginalResponseInterval (hD := hD) H (some bH) (some dH) =>
    originalResponseCols H i.1.1
  let := c.originalResponseResidueIntervalInverse H (some bH) (some dH)
  let := c.originalResponseResidueIntervalInverse P none (some d)
  have hpriv := originalHorizontalClosure_profile_join_private P H v hH
  have hsep (i) : (row i < P.xi 0 ∧ col i < P.xi 0) ∨
      (P.xi 0 < row i ∧ P.xi 0 < col i) :=
    originalRemaining_private_cut_without_unit H (P.xi 0) hpriv.1 hpriv.2
      ⟨i.1.1, fun h => originalHorizontalClosure_join_no_unit P H v hH i.1.1 h.2⟩
  let := vertexBelowBetaInverse c.residueMap row col (P.xi 0) hsep
  obtain ⟨e, he⟩ := originalHorizontalClosure_below_cap_vectors P H v hH b d
  let rowP := fun i : OriginalResponseInterval (hD := hD) P none (some d) =>
    originalResponseRows P i.1.1
  let colP := fun i : OriginalResponseInterval (hD := hD) P none (some d) =>
    originalResponseCols P i.1.1
  let y := P.zeta (originalColSplitEquiv (hD := hD) P (.inl (some d)))
  have hcopy := vertexBetaResponse_affine_reindex c.residueMap e rowP colP
    (fun i => row i.val) (fun i => col i.val) (P.xi 0) y 0
    (fun i => by simpa only [add_zero] using (he i).1)
    (fun i => by simpa only [add_zero] using (he i).2)
  simp only [add_zero] at hcopy
  have hy := (originalHorizontalClosure_retained_endpoints P H v hH false d).2
  simp only [originalClosureBlockDisplacement, Bool.false_eq_true, ↓reduceIte,
    add_sub_cancel_right] at hy
  have hsource := c.originalLocalResponse_residue_pruned P none (some d)
  change c.regularResidue (c.originalLocalResponse P none (some d)) =
    vertexBetaResponse c.residueMap rowP colP
      (P.xi (originalRowSplitEquiv (hD := hD) P (.inl none))) y at hsource
  rw [originalRowSplitEquiv_corner] at hsource
  dsimp only
  rw [vertexBetaResponse_out_of_cut c.residueMap row col (P.xi 0) _ hsep, hy,
    ← hcopy, ← hsource]

end SkewCornerDescent.Matrix.SelectedCoordinate
