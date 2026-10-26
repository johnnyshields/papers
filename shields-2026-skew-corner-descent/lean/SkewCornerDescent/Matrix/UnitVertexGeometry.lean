/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.UnitVertexResponse
import SkewGluing.SchurFunction

/-!
# Geometric no-feedback for an original h-zero vertex

Supports `shields-2026-skew-corner-descent.tex` (`lem:early-recovery`). Original
row and column beta coordinates on either side of a separating vertex give the
actual triangular block order and both unit-vertex cutoffs. Negative Jacobi--Trudi
indices supply the zero rectangle; the entire old inverse is kept. Sorry-free.
-/

namespace SkewCornerDescent.Matrix

open SkewGluing

/-- The full removed beta matrix over the given original coefficient homomorphism. -/
noncomputable def vertexBetaMatrix {ν R : Type*} [CommRing R]
    (ι : Lambda →+* R) (row col : ν → ℤ) : Matrix ν ν R :=
  Matrix.of fun i j => ι (hh (row i - col j))

/-- The column coupling of the new original vertex to every old row. -/
noncomputable def vertexIncoming {ν R : Type*} [CommRing R]
    (ι : Lambda →+* R) (row : ν → ℤ) (m : ℤ) : Matrix ν Unit R :=
  Matrix.of fun i _ => ι (hh (row i - m))

/-- The row coupling of the new original vertex to every old column. -/
noncomputable def vertexOutgoing {ν R : Type*} [CommRing R]
    (ι : Lambda →+* R) (col : ν → ℤ) (m : ℤ) : Matrix Unit ν R :=
  Matrix.of fun _ j => ι (hh (m - col j))

/-- The actual two-sided block order around the proposed beta vertex. -/
def vertexBlockOrder {ν : Type*} (row : ν → ℤ) (m : ℤ) (i : ν) : ℤ :=
  if m < row i then -1 else 1

/-- Original beta separation gives the exact zero rectangle in the full matrix. -/
theorem vertexBetaMatrix_blockTriangular {ν R : Type*} [CommRing R]
    (ι : Lambda →+* R) (row col : ν → ℤ) (m : ℤ)
    (hsep : ∀ i, (row i < m ∧ col i < m) ∨ (m < row i ∧ m < col i)) :
    (vertexBetaMatrix ι row col).BlockTriangular (vertexBlockOrder row m) := by
  intro i j hij
  by_cases hi : m < row i <;> by_cases hj : m < row j
  · simp only [vertexBlockOrder, ite_eq_left hi, ite_eq_left hj] at hij
    omega
  · simp only [vertexBlockOrder, ite_eq_left hi, ite_eq_right hj] at hij
    omega
  · have hRi := ((hsep i).resolve_right (fun h => hi h.1)).1
    have hCj := ((hsep j).resolve_left (fun h => lt_asymm hj h.1)).2
    change ι (hh (row i - col j)) = 0
    rw [hh_of_neg (by omega), map_zero]
  · simp only [vertexBlockOrder, ite_eq_right hi, ite_eq_right hj] at hij
    omega

/-- A separating original beta coordinate supplies exact no-feedback, rather
than carrying that derived contraction as an assumption. -/
theorem geometric_unit_vertex_feedback_zero {ν R : Type*}
    [Fintype ν] [DecidableEq ν] [CommRing R]
    (ι : Lambda →+* R) (row col : ν → ℤ) (m : ℤ)
    [Invertible (vertexBetaMatrix ι row col)]
    (hsep : ∀ i, (row i < m ∧ col i < m) ∨ (m < row i ∧ m < col i)) :
    vertexOutgoing ι col m * ⅟(vertexBetaMatrix ι row col) * vertexIncoming ι row m = 0 := by
  let order := vertexBlockOrder row m
  have htri := vertexBetaMatrix_blockTriangular ι row col m hsep
  apply unit_vertex_feedback_zero_of_order (vertexBetaMatrix ι row col) order htri 0
  · intro i hi
    have hRi : row i < m := by
      by_cases hr : m < row i
      · simp only [order, vertexBlockOrder, ite_eq_left hr] at hi
        omega
      · exact ((hsep i).resolve_right (fun h => hr h.1)).1
    change ι (hh (row i - m)) = 0
    rw [hh_of_neg (by omega), map_zero]
  · intro i hi
    have hCi : m < col i := by
      by_cases hr : m < row i
      · exact ((hsep i).resolve_left (fun h => lt_asymm hr h.1)).2
      · simp only [order, vertexBlockOrder, ite_eq_right hr] at hi
        omega
    change ι (hh (m - col i)) = 0
    rw [hh_of_neg (by omega), map_zero]

/-- The block insertion is exactly the original beta matrix with one row and
one column of coordinate `m`; the new diagonal is the original h-zero unit. -/
theorem vertexBetaMatrix_insert {ν R : Type*} [CommRing R]
    (ι : Lambda →+* R) (row col : ν → ℤ) (m : ℤ) :
    vertexBetaMatrix ι (Sum.elim row (fun _ : Unit => m)) (Sum.elim col (fun _ : Unit => m)) =
      Matrix.fromBlocks (vertexBetaMatrix ι row col) (vertexIncoming ι row m)
        (vertexOutgoing ι col m) 1 := by
  ext i j
  rcases i with i | i <;> rcases j with j | j
  · rfl
  · rfl
  · rfl
  · cases i
    cases j
    simp only [vertexBetaMatrix, Matrix.of_apply, Sum.elim_inr, sub_self, hh_zero,
      map_one, Matrix.fromBlocks_apply₂₂, Matrix.one_apply_eq]

/-- Geometry supplies the no-feedback producer in the exact original response
formula. Every old inverse coupling and both original endpoint vectors remain. -/
theorem geometric_unit_vertex_response_correction {ν R : Type*}
    [Fintype ν] [DecidableEq ν] [CommRing R]
    (ι : Lambda →+* R) (row col : ν → ℤ) (m x y : ℤ)
    [Invertible (vertexBetaMatrix ι row col)]
    (hsep : ∀ i, (row i < m ∧ col i < m) ∨ (m < row i ∧ m < col i)) :
    let P := vertexBetaMatrix ι row col
    let u := vertexIncoming ι row m
    let v := vertexOutgoing ι col m
    let r := vertexOutgoing ι col x
    let c := vertexIncoming ι row y
    let a : Matrix Unit Unit R := Matrix.of fun _ _ => ι (hh (x - m))
    let b : Matrix Unit Unit R := Matrix.of fun _ _ => ι (hh (m - y))
    let top : Matrix Unit Unit R := Matrix.of fun _ _ => ι (hh (x - y))
    letI := unitVertexInverse P u v (geometric_unit_vertex_feedback_zero ι row col m hsep)
    top - Matrix.fromCols r a * ⅟(Matrix.fromBlocks P u v 1) * Matrix.fromRows c b =
      (top - r * ⅟P * c) - (a - r * ⅟P * u) * (b - v * ⅟P * c) :=
  unit_vertex_response_correction _ _ _ (geometric_unit_vertex_feedback_zero ι row col m hsep)
    _ _ _ _ _

end SkewCornerDescent.Matrix
