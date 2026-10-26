/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.ProjectionTransport

/-!
# Exact full inverse projection localization at a separated cut

Supports `shields-2026-skew-corner-descent.tex` (`prop:closure-pin`).
Ordinary weight support removes the opposite side of the cut. The retained
matrix has its own produced inverse, with all nonrow off-diagonal entries
preserved. Empty sides are included. Sorry-free.
-/

namespace SkewCornerDescent.Matrix

open SkewGluing

private theorem cut_order_row {ν : Type*} {row col : ν → ℤ} {m : ℤ}
    (hsep : ∀ i, (row i < m ∧ col i < m) ∨ (m < row i ∧ m < col i))
    {i j : ν} (hi : row i < m) (hj : ¬ row j < m) :
    vertexBlockOrder row m j < vertexBlockOrder row m i := by
  have hi' := hsep i
  have hj' := hsep j
  unfold vertexBlockOrder
  split_ifs <;> omega

private theorem cut_order_col {ν : Type*} {row col : ν → ℤ} {m : ℤ}
    (hsep : ∀ i, (row i < m ∧ col i < m) ∨ (m < row i ∧ m < col i))
    {i j : ν} (hi : ¬ m < col i) (hj : m < col j) :
    vertexBlockOrder row m j < vertexBlockOrder row m i := by
  have hi' := hsep i
  have hj' := hsep j
  unfold vertexBlockOrder
  split_ifs <;> omega

private theorem cut_order_separation {ν : Type*} {row col : ν → ℤ} {m : ℤ}
    (hsep : ∀ i, (row i < m ∧ col i < m) ∨ (m < row i ∧ m < col i))
    (i j : ν) (hij : vertexBlockOrder row m i < vertexBlockOrder row m j) :
    row j < col i := by
  have hi' := hsep i
  have hj' := hsep j
  unfold vertexBlockOrder at hij
  split_ifs at hij <;> omega

/-- The complete below-cut beta matrix receives its own right-inverse producer. -/
@[instance_reducible]
noncomputable def separatedBelowInverse {ν F : Type*}
    [Fintype ν] [DecidableEq ν] [CommRing F]
    (ι : Lambda →+* F) (row col : ν → ℤ) (m : ℤ)
    [Invertible (vertexBetaMatrix ι row col)]
    (hsep : ∀ i, (row i < m ∧ col i < m) ∨ (m < row i ∧ m < col i)) :
    Invertible ((vertexBetaMatrix ι row col).toBlock (fun i => row i < m)
      (fun i => row i < m)) := by
  let M := vertexBetaMatrix ι row col
  let p := fun i => row i < m
  have htri := vertexBetaMatrix_blockTriangular ι row col m hsep
  have hm : M.toBlock p p * M⁻¹.toBlock p p +
      M.toBlock p (fun i => ¬ p i) * M⁻¹.toBlock (fun i => ¬ p i) p = 1 := by
    rw [← Matrix.toBlock_mul_eq_add, Matrix.mul_inv_of_invertible M, Matrix.toBlock_one_self]
  have hz : M.toBlock p (fun i => ¬ p i) = 0 := by
    apply Matrix.ext
    intro i j
    exact htri (cut_order_row hsep i.property j.property)
  simp only [hz, Matrix.zero_mul, add_zero] at hm
  exact invertibleOfRightInverse _ _ hm

/-- The complete above-cut beta matrix receives its own left-inverse producer. -/
@[instance_reducible]
noncomputable def separatedAboveInverse {ν F : Type*}
    [Fintype ν] [DecidableEq ν] [CommRing F]
    (ι : Lambda →+* F) (row col : ν → ℤ) (m : ℤ)
    [Invertible (vertexBetaMatrix ι row col)]
    (hsep : ∀ i, (row i < m ∧ col i < m) ∨ (m < row i ∧ m < col i)) :
    Invertible ((vertexBetaMatrix ι row col).toBlock (fun i => m < col i)
      (fun i => m < col i)) := by
  let M := vertexBetaMatrix ι row col
  let p := fun i => m < col i
  have htri := vertexBetaMatrix_blockTriangular ι row col m hsep
  have hm : M⁻¹.toBlock p p * M.toBlock p p +
      M⁻¹.toBlock p (fun i => ¬ p i) * M.toBlock (fun i => ¬ p i) p = 1 := by
    rw [← Matrix.toBlock_mul_eq_add, Matrix.inv_mul_of_invertible M, Matrix.toBlock_one_self]
  have hz : M.toBlock (fun i => ¬ p i) p = 0 := by
    apply Matrix.ext
    intro i j
    exact htri (cut_order_col hsep i.property j.property)
  simp only [hz, Matrix.mul_zero, add_zero] at hm
  exact invertibleOfLeftInverse _ _ hm

private theorem retained_projection_predicate_congr {ν F : Type*}
    [Fintype ν] [DecidableEq ν] [CommRing F]
    (row col : ν → ℤ) (M : Matrix ν ν F) (p q : ν → Prop)
    [dp : DecidablePred p] [dq : DecidablePred q] (hpq : p = q)
    (A B : LaurentPolynomial F) (z : ℤ) :
    profileInverseProjection (fun i : {i // p i} => row i.val)
        (fun i : {i // p i} => col i.val) (M.toBlock p p)⁻¹ A B z =
      profileInverseProjection (fun i : {i // q i} => row i.val)
        (fun i : {i // q i} => col i.val) (M.toBlock q q)⁻¹ A B z := by
  subst q
  have hd : dp = dq := Subsingleton.elim _ _
  cases hd
  rfl

/-- At or below the cut, the full projection uses exactly the actual retained
below-cut inverse. Every within-component off-diagonal entry remains. -/
theorem profileInverseProjection_le_retained {ν F : Type*}
    [Fintype ν] [DecidableEq ν] [CommRing F]
    (ι : Lambda →+* F) (row col : ν → ℤ) (m : ℤ)
    (hsep : ∀ i, (row i < m ∧ col i < m) ∨ (m < row i ∧ m < col i))
    [Invertible (vertexBetaMatrix ι row col)]
    (A B : LaurentPolynomial F) (hA : ∀ d, d < 0 → A.coeff d = 0)
    (hB : ∀ d, d < 0 → B.coeff d = 0) (z : ℤ) (hz : z ≤ m) :
    profileInverseProjection row col (⅟(vertexBetaMatrix ι row col)) A B z =
      profileInverseProjection (fun i : {i : ν // row i < m} => row i.val)
        (fun i : {i : ν // row i < m} => col i.val)
        ((vertexBetaMatrix ι row col).toBlock (fun i => row i < m) (fun i => row i < m))⁻¹
        A B z := by
  have hM := vertexBetaMatrix_blockTriangular ι row col m hsep
  have hout : ∀ a, ¬ (0 : ℤ) < a →
      (∀ i, vertexBlockOrder row m i = a → row i < z) ∨
        (∀ i, vertexBlockOrder row m i = a → z < col i) := by
    intro a ha
    right
    intro i hi
    rw [← hi] at ha
    unfold vertexBlockOrder at ha
    rcases hsep i with hi' | hi' <;> split_ifs at ha <;> omega
  have he : (fun i => 0 < vertexBlockOrder row m i) = fun i => row i < m := by
    funext i
    apply propext
    have hi := hsep i
    unfold vertexBlockOrder
    split_ifs <;> omega
  exact (profileInverseProjection_suffix_cap row col (vertexBetaMatrix ι row col)
      (vertexBlockOrder row m) hM (cut_order_separation hsep) 0 A B z hA hB hout).trans
    (retained_projection_predicate_congr row col (vertexBetaMatrix ι row col)
      (fun i => 0 < vertexBlockOrder row m i) (fun i => row i < m) he A B z)

/-- At or above the cut, the full projection uses the actual retained above-cut
inverse, without restricting a noncontiguous full inverse submatrix by assumption. -/
theorem profileInverseProjection_ge_retained {ν F : Type*}
    [Fintype ν] [DecidableEq ν] [CommRing F]
    (ι : Lambda →+* F) (row col : ν → ℤ) (m : ℤ)
    (hsep : ∀ i, (row i < m ∧ col i < m) ∨ (m < row i ∧ m < col i))
    [Invertible (vertexBetaMatrix ι row col)]
    (A B : LaurentPolynomial F) (hA : ∀ d, d < 0 → A.coeff d = 0)
    (hB : ∀ d, d < 0 → B.coeff d = 0) (z : ℤ) (hz : m ≤ z) :
    profileInverseProjection row col (⅟(vertexBetaMatrix ι row col)) A B z =
      profileInverseProjection (fun i : {i : ν // m < col i} => row i.val)
        (fun i : {i : ν // m < col i} => col i.val)
        ((vertexBetaMatrix ι row col).toBlock (fun i => m < col i) (fun i => m < col i))⁻¹
        A B z := by
  have hM := vertexBetaMatrix_blockTriangular ι row col m hsep
  have hout : ∀ a, ¬ a < (0 : ℤ) →
      (∀ i, vertexBlockOrder row m i = a → row i < z) ∨
        (∀ i, vertexBlockOrder row m i = a → z < col i) := by
    intro a ha
    left
    intro i hi
    rw [← hi] at ha
    unfold vertexBlockOrder at ha
    rcases hsep i with hi' | hi' <;> split_ifs at ha <;> omega
  have he : (fun i => vertexBlockOrder row m i < 0) = fun i => m < col i := by
    funext i
    apply propext
    have hi := hsep i
    unfold vertexBlockOrder
    split_ifs <;> omega
  exact (profileInverseProjection_prefix_cap row col (vertexBetaMatrix ι row col)
      (vertexBlockOrder row m) hM (cut_order_separation hsep) 0 A B z hA hB hout).trans
    (retained_projection_predicate_congr row col (vertexBetaMatrix ι row col)
      (fun i => vertexBlockOrder row m i < 0) (fun i => m < col i) he A B z)

end SkewCornerDescent.Matrix
