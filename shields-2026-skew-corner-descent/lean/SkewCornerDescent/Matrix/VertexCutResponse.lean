/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.VertexBetaResponse
import SkewCornerDescent.Matrix.SeparatedCapProjection

/-!
# Full effective responses on both sides of a private cut

Supports `shields-2026-skew-corner-descent.tex` (`prop:closure-pin`).
The complete response into the cut uses the above-cut retained matrix; the
response out of the cut uses the below-cut retained matrix. Strict beta order
supplies both fresh inverses and removes only impossible cross-cut paths.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix

open SkewGluing

@[instance_reducible]
noncomputable def vertexAboveBetaInverse {ν R : Type*}
    [Fintype ν] [DecidableEq ν] [CommRing R]
    (ι : Lambda →+* R) (row col : ν → ℤ) (k : ℤ)
    [Invertible (vertexBetaMatrix ι row col)]
    (hsep : ∀ i, (row i < k ∧ col i < k) ∨ (k < row i ∧ k < col i)) :
    Invertible (vertexBetaMatrix ι (fun i : {i : ν // k < col i} => row i.val)
      (fun i => col i.val)) := by
  change Invertible ((vertexBetaMatrix ι row col).toBlock (fun i => k < col i) (fun i => k < col i))
  exact separatedAboveInverse ι row col k hsep

@[instance_reducible]
noncomputable def vertexBelowBetaInverse {ν R : Type*}
    [Fintype ν] [DecidableEq ν] [CommRing R]
    (ι : Lambda →+* R) (row col : ν → ℤ) (k : ℤ)
    [Invertible (vertexBetaMatrix ι row col)]
    (hsep : ∀ i, (row i < k ∧ col i < k) ∨ (k < row i ∧ k < col i)) :
    Invertible (vertexBetaMatrix ι (fun i : {i : ν // row i < k} => row i.val)
      (fun i => col i.val)) := by
  change Invertible ((vertexBetaMatrix ι row col).toBlock (fun i => row i < k) (fun i => row i < k))
  exact separatedBelowInverse ι row col k hsep

/-- The full effective incoming response at a private cut equals its complete
above-cut response, with a produced retained inverse. -/
theorem vertexBetaResponse_into_cut {ν R : Type*}
    [Fintype ν] [DecidableEq ν] [CommRing R]
    (ι : Lambda →+* R) (row col : ν → ℤ) (k x : ℤ)
    [Invertible (vertexBetaMatrix ι row col)]
    (hsep : ∀ i, (row i < k ∧ col i < k) ∨ (k < row i ∧ k < col i)) :
    letI := vertexAboveBetaInverse ι row col k hsep
    vertexBetaResponse ι row col x k =
      vertexBetaResponse ι (fun i : {i : ν // k < col i} => row i.val)
        (fun i => col i.val) x k := by
  classical
  let := vertexAboveBetaInverse ι row col k hsep
  let order := vertexBlockOrder row k
  have htri := vertexBetaMatrix_blockTriangular ι row col k hsep
  let e : {i : ν // order i = -1} ≃ {i : ν // k < col i} :=
    Equiv.subtypeEquivRight (fun i => by
      rcases hsep i with h | h
      · have hr := not_lt_of_gt h.1
        have hc := not_lt_of_gt h.2
        simp [order, vertexBlockOrder, hr, hc]
      · simp [order, vertexBlockOrder, h.1, h.2])
  have hloc := inverseContraction_same_block
    (fun i => ι (hh (x-col i))) (fun i => ι (hh (row i-k)))
    (vertexBetaMatrix ι row col) order htri (-1)
    (fun i hi => by simp only [order, vertexBlockOrder] at hi; split_ifs at hi <;> omega)
    (fun i hi => by
      have h := hsep i
      simp only [order, vertexBlockOrder] at hi
      split_ifs at hi
      · omega
      · rw [hh_of_neg (by omega), map_zero])
  have hM : (vertexBetaMatrix ι
      (fun i : {i : ν // k < col i} => row i.val) (fun i => col i.val)).submatrix e e =
      (vertexBetaMatrix ι row col).toSquareBlock order (-1) := by
    apply Matrix.ext
    intro i j
    rfl
  unfold vertexBetaResponse
  rw [vertex_boundary_contraction_eq, vertex_boundary_contraction_eq, hloc]
  rw [← hM]
  exact congrArg (fun z => ι (hh (x-k)) - z)
    (inverseContraction_equiv e (fun i => ι (hh (x-col i.val)))
      (fun i => ι (hh (row i.val-k))) _)

/-- The full effective outgoing response uses its complete below-cut retained
matrix, not a diagonal-only inverse. -/
theorem vertexBetaResponse_out_of_cut {ν R : Type*}
    [Fintype ν] [DecidableEq ν] [CommRing R]
    (ι : Lambda →+* R) (row col : ν → ℤ) (k y : ℤ)
    [Invertible (vertexBetaMatrix ι row col)]
    (hsep : ∀ i, (row i < k ∧ col i < k) ∨ (k < row i ∧ k < col i)) :
    letI := vertexBelowBetaInverse ι row col k hsep
    vertexBetaResponse ι row col k y =
      vertexBetaResponse ι (fun i : {i : ν // row i < k} => row i.val)
        (fun i => col i.val) k y := by
  classical
  let := vertexBelowBetaInverse ι row col k hsep
  let order := vertexBlockOrder row k
  have htri := vertexBetaMatrix_blockTriangular ι row col k hsep
  let e : {i : ν // order i = 1} ≃ {i : ν // row i < k} :=
    Equiv.subtypeEquivRight (fun i => by
      rcases hsep i with h | h
      · have hr := not_lt_of_gt h.1
        simp [order, vertexBlockOrder, hr, h.1]
      · have hr := not_lt_of_gt h.1
        simp [order, vertexBlockOrder, h.1, hr])
  have hloc := inverseContraction_same_block
    (fun i => ι (hh (k-col i))) (fun i => ι (hh (row i-y)))
    (vertexBetaMatrix ι row col) order htri 1
    (fun i hi => by
      have h := hsep i
      simp only [order, vertexBlockOrder] at hi
      split_ifs at hi
      · rw [hh_of_neg (by omega), map_zero]
      · omega)
    (fun i hi => by simp only [order, vertexBlockOrder] at hi; split_ifs at hi <;> omega)
  have hM : (vertexBetaMatrix ι
      (fun i : {i : ν // row i < k} => row i.val) (fun i => col i.val)).submatrix e e =
      (vertexBetaMatrix ι row col).toSquareBlock order 1 := by
    apply Matrix.ext
    intro i j
    rfl
  unfold vertexBetaResponse
  rw [vertex_boundary_contraction_eq, vertex_boundary_contraction_eq, hloc]
  rw [← hM]
  exact congrArg (fun z => ι (hh (k-y)) - z)
    (inverseContraction_equiv e (fun i => ι (hh (k-col i.val)))
      (fun i => ι (hh (row i.val-y))) _)

end SkewCornerDescent.Matrix
