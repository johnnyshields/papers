/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Tactic.Abel

/-!
# Exact response change from an acyclic unit vertex

Supports `shields-2026-skew-corner-descent.tex` (`lem:early-recovery`). Adjoining
one original h-zero vertex gives the product of its effective incoming and outgoing
coefficients as the response correction. The full old inverse and all couplings
remain; no diagonal-only inverse is substituted. Sorry-free.
-/

namespace SkewCornerDescent.Matrix

/-- The exact no-feedback condition follows from the original block order and
the vertex's incoming/outgoing cutoffs. Every inverse coupling is retained. -/
theorem unit_vertex_feedback_zero_of_order {ν α R : Type*}
    [Fintype ν] [DecidableEq ν] [LinearOrder α] [CommRing R]
    (P : Matrix ν ν R) [Invertible P] (order : ν → α)
    (hP : P.BlockTriangular order) (cut : α)
    (u : Matrix ν Unit R) (v : Matrix Unit ν R)
    (hu : ∀ i, cut ≤ order i → u i () = 0)
    (hv : ∀ i, order i ≤ cut → v () i = 0) : v * ⅟P * u = 0 := by
  classical
  ext a b
  cases a
  cases b
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro j _
  by_cases hj : cut ≤ order j
  · rw [hu j hj, mul_zero]
  · have hjlt : order j < cut := lt_of_not_ge hj
    rw [Matrix.mul_apply]
    have hinner : (∑ i, v () i * ⅟P i j) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      by_cases hi : order i ≤ cut
      · rw [hv i hi, zero_mul]
      · have hij : order j < order i := hjlt.trans (lt_of_not_ge hi)
        rw [Matrix.invOf_eq_nonsing_inv,
          Matrix.blockTriangular_inv_of_blockTriangular hP hij, mul_zero]
    rw [hinner, zero_mul]

/-- Acyclicity gives Schur complement one, hence a produced full inverse after
adjoining the unit vertex. No generic inverse of a singular matrix is used. -/
@[instance_reducible]
noncomputable def unitVertexInverse {ν R : Type*} [Fintype ν] [DecidableEq ν] [CommRing R]
    (P : Matrix ν ν R) [Invertible P] (u : Matrix ν Unit R) (v : Matrix Unit ν R)
    (hfeedback : v * ⅟P * u = 0) : Invertible (Matrix.fromBlocks P u v 1) := by
  let : Invertible ((1 : Matrix Unit Unit R) - v * ⅟P * u) :=
    ⟨1, by rw [hfeedback, sub_zero, Matrix.one_mul],
      by rw [hfeedback, sub_zero, Matrix.mul_one]⟩
  exact Matrix.fromBlocks₁₁Invertible P u v 1

/-- The full original Schur response changes by the product of the two effective
vertex coefficients. Acyclicity is stated as the exact no-feedback contraction. -/
theorem unit_vertex_response_correction {ν R : Type*}
    [Fintype ν] [DecidableEq ν] [CommRing R]
    (P : Matrix ν ν R) [Invertible P] (u : Matrix ν Unit R) (v : Matrix Unit ν R)
    (hfeedback : v * ⅟P * u = 0)
    (row : Matrix Unit ν R) (col : Matrix ν Unit R)
    (a b top : Matrix Unit Unit R) :
    letI := unitVertexInverse P u v hfeedback
    top - Matrix.fromCols row a * ⅟(Matrix.fromBlocks P u v 1) * Matrix.fromRows col b =
      (top - row * ⅟P * col) - (a - row * ⅟P * u) * (b - v * ⅟P * col) := by
  let : Invertible ((1 : Matrix Unit Unit R) - v * ⅟P * u) :=
    ⟨1, by rw [hfeedback, sub_zero, Matrix.one_mul],
      by rw [hfeedback, sub_zero, Matrix.mul_one]⟩
  let := unitVertexInverse P u v hfeedback
  have hSchur : ⅟((1 : Matrix Unit Unit R) - v * ⅟P * u) = 1 := rfl
  rw [Matrix.invOf_fromBlocks₁₁_eq, hSchur]
  simp only [Matrix.one_mul, Matrix.mul_one, Matrix.fromCols_mul_fromBlocks,
    Matrix.fromCols_mul_fromRows, Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub,
    Matrix.sub_mul, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
  abel

end SkewCornerDescent.Matrix
