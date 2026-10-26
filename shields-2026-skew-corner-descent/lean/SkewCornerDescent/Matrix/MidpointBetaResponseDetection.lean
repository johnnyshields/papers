/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.UnitVertexDetection
import SkewCornerDescent.Matrix.VertexBetaResponse

/-!
# Midpoint nonvanishing for complete beta responses

Formalizes `shields-2026-skew-corner-descent.tex`, `lem:early-recovery`.
The full matrix unit-insertion nonvanishing theorem is identified with the
complete beta-response API, retaining both genuine inverse constructions.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate
open SkewGluing
variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The full beta-response API detects the separating midpoint vertex.  The
matrix-form nonvanishing theorem supplies both effective lower corrections. -/
theorem midpoint_vertex_beta_response_ne {ν : Type*} [Fintype ν] [DecidableEq ν]
    (row col : ν → ℤ) (m x y : ℤ) (J : ℕ+) (hJ : c.top < J)
    [Invertible (vertexBetaMatrix c.residueMap row col)]
    (hsep : ∀ i, (row i < m ∧ col i < m) ∨ (m < row i ∧ m < col i))
    (hx : ∀ i, row i < x) (hy : ∀ i, y < col i)
    (hxm : x - m = (J : ℤ)) (hmy : m - y = (J : ℤ)) :
    letI := vertexBetaUnitInverse c.residueMap row col m hsep
    vertexBetaResponse c.residueMap (Sum.elim row (fun _ : Unit => m))
        (Sum.elim col (fun _ : Unit => m)) x y ≠
      vertexBetaResponse c.residueMap row col x y := by
  let := vertexBetaUnitInverse c.residueMap row col m hsep
  have h := c.original_midpoint_vertex_changes_response row col m x y J hJ hsep hx hy hxm hmy
  dsimp only at h ⊢
  have hr : vertexOutgoing c.residueMap (Sum.elim col (fun _ : Unit => m)) x =
      Matrix.fromCols (vertexOutgoing c.residueMap col x)
        (Matrix.of fun _ _ => c.residueMap (hh (x - m))) := by
    ext i j
    rcases j with j | j <;> rfl
  have hc : vertexIncoming c.residueMap (Sum.elim row (fun _ : Unit => m)) y =
      Matrix.fromRows (vertexIncoming c.residueMap row y)
        (Matrix.of fun _ _ => c.residueMap (hh (m - y))) := by
    ext i j
    rcases i with i | i <;> rfl
  unfold vertexBetaResponse
  simp only [Matrix.invOf_eq_nonsing_inv] at h ⊢
  rw [vertexBetaMatrix_insert, hr, hc]
  simpa only [Matrix.sub_apply, Matrix.of_apply] using h

end SkewCornerDescent.Matrix.SelectedCoordinate
