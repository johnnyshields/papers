/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.ProjectionTransport
import SkewCornerDescent.Matrix.BlockResponseLocality
import SkewCornerDescent.Matrix.UnitVertexDetection

/-!
# Full retained beta responses and literal unit insertion

Supports `shields-2026-skew-corner-descent.tex` (`prop:closure-pin`).
Both boundary vectors and every old inverse entry remain in the response.
Affine copying supplies full response equality; strict private geometry
supplies the inserted-unit inverse and its exact response correction.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix

open SkewGluing

/-- The full retained response over the given original coefficient map.
A genuine inverse is part of the construction, not an implicit singular convention. -/
noncomputable def vertexBetaResponse {ν R : Type*} [Fintype ν] [DecidableEq ν] [CommRing R]
    (ι : Lambda →+* R) (row col : ν → ℤ) [Invertible (vertexBetaMatrix ι row col)]
    (x y : ℤ) : R :=
  ι (hh (x-y)) -
    (vertexOutgoing ι col x * ⅟(vertexBetaMatrix ι row col) * vertexIncoming ι row y) () ()

/-- Full affine beta copying preserves the complete retained response. -/
theorem vertexBetaResponse_affine_reindex {ν μ R : Type*}
    [Fintype ν] [DecidableEq ν] [Fintype μ] [DecidableEq μ] [CommRing R]
    (ι : Lambda →+* R) (e : ν ≃ μ) (row col : ν → ℤ) (row' col' : μ → ℤ)
    [Invertible (vertexBetaMatrix ι row col)] [Invertible (vertexBetaMatrix ι row' col')]
    (x y shift : ℤ)
    (hr : ∀ i, row' (e i) = row i + shift)
    (hc : ∀ i, col' (e i) = col i + shift) :
    vertexBetaResponse ι row col x y =
      vertexBetaResponse ι row' col' (x+shift) (y+shift) := by
  have hM := vertexBetaMatrix_affine_reindex ι e row col row' col' shift hr hc
  have hrow : (fun i => ι (hh (x-col i))) =
      (fun j => ι (hh (x+shift-col' j))) ∘ e := by
    funext i
    simp only [Function.comp_apply, hc]
    congr 2
    omega
  have hcol : (fun i => ι (hh (row i-y))) =
      (fun j => ι (hh (row' j-(y+shift)))) ∘ e := by
    funext i
    simp only [Function.comp_apply, hr]
    congr 2
    omega
  unfold vertexBetaResponse
  rw [vertex_boundary_contraction_eq, vertex_boundary_contraction_eq]
  rw [hrow, hcol, ← hM, inverseContraction_equiv]
  rw [show x + shift - (y + shift) = x - y by omega]

/-- Strict private geometry produces the complete inserted beta inverse. -/
@[instance_reducible]
noncomputable def vertexBetaUnitInverse {ν R : Type*}
    [Fintype ν] [DecidableEq ν] [CommRing R]
    (ι : Lambda →+* R) (row col : ν → ℤ) (k : ℤ)
    [Invertible (vertexBetaMatrix ι row col)]
    (hsep : ∀ i, (row i < k ∧ col i < k) ∨ (k < row i ∧ k < col i)) :
    Invertible (vertexBetaMatrix ι (Sum.elim row (fun _ : Unit => k))
      (Sum.elim col (fun _ : Unit => k))) := by
  rw [vertexBetaMatrix_insert]
  exact unitVertexInverse _ _ _ (geometric_unit_vertex_feedback_zero ι row col k hsep)

/-- A literal private unit changes the full response by the product of its
complete effective left and right responses, with no inverse approximation. -/
theorem vertexBetaResponse_unit_insert {ν R : Type*}
    [Fintype ν] [DecidableEq ν] [CommRing R]
    (ι : Lambda →+* R) (row col : ν → ℤ) (k x y : ℤ)
    [Invertible (vertexBetaMatrix ι row col)]
    (hsep : ∀ i, (row i < k ∧ col i < k) ∨ (k < row i ∧ k < col i)) :
    letI := vertexBetaUnitInverse ι row col k hsep
    vertexBetaResponse ι (Sum.elim row (fun _ : Unit => k))
        (Sum.elim col (fun _ : Unit => k)) x y =
      vertexBetaResponse ι row col x y -
        vertexBetaResponse ι row col x k * vertexBetaResponse ι row col k y := by
  let := vertexBetaUnitInverse ι row col k hsep
  have h := geometric_unit_vertex_response_correction ι row col k x y hsep
  have he := congrArg (fun M : Matrix Unit Unit R => M () ()) h
  have hr : vertexOutgoing ι (Sum.elim col (fun _ : Unit => k)) x =
      Matrix.fromCols (vertexOutgoing ι col x) (Matrix.of fun _ _ => ι (hh (x - k))) := by
    ext i j
    rcases j with j | j <;> rfl
  have hc : vertexIncoming ι (Sum.elim row (fun _ : Unit => k)) y =
      Matrix.fromRows (vertexIncoming ι row y) (Matrix.of fun _ _ => ι (hh (k - y))) := by
    ext i j
    rcases i with i | i <;> rfl
  unfold vertexBetaResponse
  simp only [Matrix.invOf_eq_nonsing_inv] at he ⊢
  rw [vertexBetaMatrix_insert, hr, hc]
  simpa only [Matrix.sub_apply, Matrix.mul_apply, Finset.univ_unique,
    Finset.sum_singleton, Matrix.of_apply] using he

end SkewCornerDescent.Matrix
