/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.ProjectionTransport

/-!
# The exact inverse-projection correction of a private unit vertex

Supports `shields-2026-skew-corner-descent.tex` (`prop:closure-pin`).
Strict original endpoint separation produces no feedback and the full inserted
inverse. All old within-component inverse entries remain; only the new unit's
self-contraction survives ordinary endpoint support. Sorry-free.
-/

namespace SkewCornerDescent.Matrix

open SkewGluing
open scoped BigOperators

/-- Inserting the actual zero-index vertex changes the full projection by its
single self-contraction. No full nonrow inverse is replaced by its diagonal. -/
theorem geometric_unit_vertex_projection_insert {ν F : Type*}
    [Fintype ν] [DecidableEq ν] [CommRing F]
    (ι : Lambda →+* F) (row col : ν → ℤ) (m : ℤ)
    [Invertible (vertexBetaMatrix ι row col)]
    (hsep : ∀ i, (row i < m ∧ col i < m) ∨ (m < row i ∧ m < col i))
    (A B : LaurentPolynomial F) (z : ℤ)
    (hA : ∀ k, k < 0 → A.coeff k = 0) (hB : ∀ k, k < 0 → B.coeff k = 0) :
    let P := vertexBetaMatrix ι row col
    let u := vertexIncoming ι row m
    let v := vertexOutgoing ι col m
    letI := unitVertexInverse P u v (geometric_unit_vertex_feedback_zero ι row col m hsep)
    profileInverseProjection (Sum.elim row (fun _ : Unit => m))
        (Sum.elim col (fun _ : Unit => m)) (⅟(Matrix.fromBlocks P u v 1)) A B z =
      profileInverseProjection row col (⅟P) A B z + A.coeff (z - m) * B.coeff (m - z) := by
  classical
  let P := vertexBetaMatrix ι row col
  let u := vertexIncoming ι row m
  let v := vertexOutgoing ι col m
  have hfeedback : v * ⅟P * u = 0 := geometric_unit_vertex_feedback_zero ι row col m hsep
  let := unitVertexInverse P u v hfeedback
  let : Invertible ((1 : Matrix Unit Unit F) - v * ⅟P * u) :=
    ⟨1, by rw [hfeedback, sub_zero, Matrix.one_mul],
      by rw [hfeedback, sub_zero, Matrix.mul_one]⟩
  have hSchur : ⅟((1 : Matrix Unit Unit F) - v * ⅟P * u) = 1 := rfl
  have hI : (⅟P).BlockTriangular (vertexBlockOrder row m) := by
    rw [Matrix.invOf_eq_nonsing_inv]
    exact Matrix.blockTriangular_inv_of_blockTriangular
      (vertexBetaMatrix_blockTriangular ι row col m hsep)
  have hU (i : ν) (hi : row i < m) : (⅟P * u) i () = 0 := by
    rw [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro j _
    rcases hsep j with hj | hj
    · have hu : u j () = 0 := by
        change ι (hh (row j - m)) = 0
        rw [hh_of_neg (sub_neg.mpr hj.1), map_zero]
      rw [hu, mul_zero]
    · have hij : vertexBlockOrder row m j < vertexBlockOrder row m i := by
        simp [vertexBlockOrder, hj.1, not_lt_of_ge hi.le]
      rw [hI hij, zero_mul]
  have hV (j : ν) (hj : m < row j) : (v * ⅟P) () j = 0 := by
    rw [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro i _
    rcases hsep i with hi | hi
    · have hij : vertexBlockOrder row m j < vertexBlockOrder row m i := by
        simp [vertexBlockOrder, hj, not_lt_of_ge hi.1.le]
      rw [hI hij, mul_zero]
    · have hv : v () i = 0 := by
        change ι (hh (m - col i)) = 0
        rw [hh_of_neg (sub_neg.mpr hi.2), map_zero]
      rw [hv, zero_mul]
  have huTerm (i : ν) :
      A.coeff (z - col i) * (⅟P * u) i () * B.coeff (m - z) = 0 := by
    rcases hsep i with hi | hi
    · rw [hU i hi.1, mul_zero, zero_mul]
    · by_cases hz : z - col i < 0
      · rw [hA _ hz, zero_mul, zero_mul]
      · rw [hB _ (by omega), mul_zero]
  have hvTerm (j : ν) :
      A.coeff (z - m) * (v * ⅟P) () j * B.coeff (row j - z) = 0 := by
    rcases hsep j with hj | hj
    · by_cases hz : row j - z < 0
      · rw [hB _ hz, mul_zero]
      · rw [hA _ (by omega), zero_mul, zero_mul]
    · rw [hV j hj.1, mul_zero, zero_mul]
  have hProduct (i j : ν) : ((⅟P * u) * (v * ⅟P)) i j =
      (⅟P * u) i () * (v * ⅟P) () j := by
    change (∑ k : Unit, (⅟P * u) i k * (v * ⅟P) k j) = _
    simp only [Fintype.sum_unique]
  have hCorrection (i j : ν) : A.coeff (z - col i) *
      ((⅟P * u) * (v * ⅟P)) i j * B.coeff (row j - z) = 0 := by
    rw [hProduct]
    rcases hsep i with hi | hi
    · rw [hU i hi.1, zero_mul, mul_zero, zero_mul]
    · rcases hsep j with hj | hj
      · by_cases hz : z - col i < 0
        · rw [hA _ hz, zero_mul, zero_mul]
        · rw [hB _ (by omega), mul_zero]
      · rw [hV j hj.1, mul_zero, mul_zero, zero_mul]
  have hOldTerm (i j : ν) : A.coeff (z - col i) *
      (⅟P + (⅟P * u) * (v * ⅟P)) i j * B.coeff (row j - z) =
      A.coeff (z - col i) * ⅟P i j * B.coeff (row j - z) := by
    rw [Matrix.add_apply, mul_add, add_mul, hCorrection, add_zero]
  have hInv : ⅟(Matrix.fromBlocks P u v 1) =
      Matrix.fromBlocks (⅟P + (⅟P * u) * (v * ⅟P)) (-(⅟P * u)) (-(v * ⅟P)) 1 := by
    have h := Matrix.invOf_fromBlocks₁₁_eq P u v (1 : Matrix Unit Unit F)
    rw [hSchur] at h
    simpa only [Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc] using h
  dsimp only
  rw [hInv]
  simp only [profileInverseProjection, Fintype.sum_sum_type, Fintype.sum_unique,
    Sum.elim_inl, Sum.elim_inr, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
    Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.one_apply_eq,
    Matrix.neg_apply, mul_neg, neg_mul, hOldTerm, huTerm, hvTerm, neg_zero,
    add_zero, mul_one]
  simp only [zero_add, Finset.sum_const_zero]
  rfl

end SkewCornerDescent.Matrix
