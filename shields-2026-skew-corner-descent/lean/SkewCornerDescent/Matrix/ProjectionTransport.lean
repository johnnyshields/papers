/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.ProfileInverseProjection
import SkewCornerDescent.Matrix.ProfileProjectionBlocks
import SkewCornerDescent.Matrix.UnitVertexGeometry

/-!
# Full weighted inverse contractions under literal affine copies

Supports `shields-2026-skew-corner-descent.tex` (`prop:closure-pin`).
A complete reindexing of every row, column, and inverse entry transports the
entire weighted contraction. Off-diagonal entries and empty intervals are
retained. Sorry-free.
-/

namespace SkewCornerDescent.Matrix

/-- Full affine copying preserves the entire inverse projection, without
reducing a nonrow unit inverse to its diagonal entries. -/
theorem profileInverseProjection_reindex_translate {ι κ F : Type*}
    [Fintype ι] [Fintype κ] [CommRing F]
    (e : ι ≃ κ) (row col : ι → ℤ) (row' col' : κ → ℤ)
    (I : Matrix ι ι F) (I' : Matrix κ κ F) (A B : LaurentPolynomial F) (z shift : ℤ)
    (hr : ∀ i, row' (e i) = row i + shift)
    (hc : ∀ i, col' (e i) = col i + shift)
    (hI : ∀ i j, I' (e i) (e j) = I i j) :
    profileInverseProjection row col I A B z =
      profileInverseProjection row' col' I' A B (z + shift) := by
  unfold profileInverseProjection
  refine Fintype.sum_equiv e _ _ fun i => ?_
  refine Fintype.sum_equiv e _ _ fun j => ?_
  rw [hr, hc, hI]
  have hp : z + shift - (col i + shift) = z - col i := by omega
  have hq : row j + shift - (z + shift) = row j - z := by omega
  rw [hp, hq]

/-- A literal affine copy identifies every full beta entry over the same
original coefficient homomorphism, including zero-index units. -/
theorem vertexBetaMatrix_affine_reindex {ν μ F : Type*} [CommRing F]
    (ι : SkewGluing.Lambda →+* F) (e : ν ≃ μ)
    (row col : ν → ℤ) (row' col' : μ → ℤ) (shift : ℤ)
    (hr : ∀ i, row' (e i) = row i + shift)
    (hc : ∀ i, col' (e i) = col i + shift) :
    (vertexBetaMatrix ι row' col').submatrix e e = vertexBetaMatrix ι row col := by
  apply Matrix.ext
  intro i j
  simp only [Matrix.submatrix_apply, vertexBetaMatrix, Matrix.of_apply, hr, hc,
    add_sub_add_right_eq_sub]

/-- Full literal beta copying produces the inverse-entry equality needed to
transport the entire projection. It is not a raw compatibility hypothesis. -/
theorem profileInverseProjection_affine_beta_copy {ν μ F : Type*}
    [Fintype ν] [DecidableEq ν] [Fintype μ] [DecidableEq μ] [CommRing F]
    (ι : SkewGluing.Lambda →+* F) (e : ν ≃ μ)
    (row col : ν → ℤ) (row' col' : μ → ℤ)
    [Invertible (vertexBetaMatrix ι row col)] [Invertible (vertexBetaMatrix ι row' col')]
    (A B : LaurentPolynomial F) (z shift : ℤ)
    (hr : ∀ i, row' (e i) = row i + shift)
    (hc : ∀ i, col' (e i) = col i + shift) :
    profileInverseProjection row col (⅟(vertexBetaMatrix ι row col)) A B z =
      profileInverseProjection row' col' (⅟(vertexBetaMatrix ι row' col')) A B (z + shift) := by
  have hM := vertexBetaMatrix_affine_reindex ι e row col row' col' shift hr hc
  have hInv : (⅟(vertexBetaMatrix ι row' col')).submatrix e e =
      ⅟(vertexBetaMatrix ι row col) := by
    rw [Matrix.invOf_eq_nonsing_inv, Matrix.invOf_eq_nonsing_inv,
      ← Matrix.inv_submatrix_equiv, hM]
  apply profileInverseProjection_reindex_translate e row col row' col'
    (⅟(vertexBetaMatrix ι row col)) (⅟(vertexBetaMatrix ι row' col')) A B z shift hr hc
  intro i j
  exact congrArg (fun I => I i j) hInv

/-- A full unit block strictly before the candidate position contributes
nothing, even if its inverse has nonzero off-diagonal entries. -/
theorem profileInverseProjection_eq_zero_of_rows_lt {ι F : Type*}
    [Fintype ι] [CommRing F] (row col : ι → ℤ) (I : Matrix ι ι F)
    (A B : LaurentPolynomial F) (z : ℤ)
    (hB : ∀ k : ℤ, k < 0 → B.coeff k = 0) (hr : ∀ j, row j < z) :
    profileInverseProjection row col I A B z = 0 := by
  unfold profileInverseProjection
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro j _
  rw [hB _ (by have h := hr j; omega), mul_zero]

/-- A full unit block strictly after the candidate position contributes
nothing; no entry of its inverse needs to be discarded or simplified. -/
theorem profileInverseProjection_eq_zero_of_cols_gt {ι F : Type*}
    [Fintype ι] [CommRing F] (row col : ι → ℤ) (I : Matrix ι ι F)
    (A B : LaurentPolynomial F) (z : ℤ)
    (hA : ∀ k : ℤ, k < 0 → A.coeff k = 0) (hc : ∀ i, z < col i) :
    profileInverseProjection row col I A B z = 0 := by
  unfold profileInverseProjection
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro j _
  rw [hA _ (by have h := hc i; omega), zero_mul, zero_mul]

/-- Whole blocks outside the candidate content position can be removed from the
full inverse projection. The retained principal inverse entries, including all
off-diagonal entries inside nonrow blocks, are unchanged. -/
theorem profileInverseProjection_restrict_blocks {ν α F : Type*}
    [Fintype ν] [LinearOrder α] [CommRing F]
    (row col : ν → ℤ) (I : Matrix ν ν F) (label : ν → α)
    (hI : I.BlockTriangular label)
    (hseparation : ∀ i j, label i < label j → row j < col i)
    (keep : α → Prop) [DecidablePred keep] (A B : LaurentPolynomial F) (z : ℤ)
    (hA : ∀ k, k < 0 → A.coeff k = 0) (hB : ∀ k, k < 0 → B.coeff k = 0)
    (houtside : ∀ a, ¬ keep a →
      (∀ i, label i = a → row i < z) ∨ (∀ i, label i = a → z < col i)) :
    profileInverseProjection row col I A B z =
      profileInverseProjection (fun i : {i : ν // keep (label i)} => row i.val)
        (fun i : {i : ν // keep (label i)} => col i.val)
        (I.submatrix Subtype.val Subtype.val) A B z := by
  classical
  let term := fun i j : ν =>
    if label i = label j then A.coeff (z - col i) * I i j * B.coeff (row j - z) else 0
  have hsum (g : ν → F) (hg : ∀ i, ¬ keep (label i) → g i = 0) :
      ∑ i, g i = ∑ i : {i : ν // keep (label i)}, g i.val := by
    calc
      _ = ∑ i ∈ Finset.univ.filter (fun i => keep (label i)), g i := by
        symm
        apply Finset.sum_subset (Finset.filter_subset _ _)
        intro i _ hi
        apply hg i
        simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hi
      _ = _ := Finset.sum_subtype _ (by simp) g
  have houter (i : ν) (hi : ¬ keep (label i)) : ∑ j, term i j = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    by_cases he : label i = label j
    · simp only [term, ite_eq_left he]
      rcases houtside (label i) hi with hrow | hcol
      · rw [hB _ (by have h := hrow j he.symm; omega), mul_zero]
      · rw [hA _ (by have h := hcol i rfl; omega), zero_mul, zero_mul]
    · simp only [term, ite_eq_right he]
  have hinner (i : {i : ν // keep (label i)}) (j : ν)
      (hj : ¬ keep (label j)) : term i.val j = 0 := by
    have he : label i.val ≠ label j := by
      intro he
      apply hj
      rw [← he]
      exact i.property
    simp only [term, ite_eq_right he]
  have hI' : (I.submatrix Subtype.val Subtype.val).BlockTriangular
      (fun i : {i : ν // keep (label i)} => label i.val) := by
    intro i j hij
    exact hI hij
  rw [profile_inverse_projection_same_blocks row col I label hI hseparation A B hA hB z,
    profile_inverse_projection_same_blocks _ _ _ _ hI'
      (fun i j hij => hseparation i.val j.val hij) A B hA hB z]
  change (∑ i, ∑ j, term i j) =
    ∑ i : {i : ν // keep (label i)}, ∑ j : {i : ν // keep (label i)}, term i.val j.val
  rw [hsum _ houter]
  apply Finset.sum_congr rfl
  intro i _
  exact hsum _ (hinner i)

/-- A complete prefix cap has the inverse of its actual retained matrix, not
merely a submatrix guessed from the full inverse. Mathlib supplies this equality. -/
theorem profileInverseProjection_prefix_cap {ν α F : Type*}
    [Fintype ν] [DecidableEq ν] [LinearOrder α] [CommRing F]
    (row col : ν → ℤ) (M : Matrix ν ν F) [Invertible M] (label : ν → α)
    (hM : M.BlockTriangular label)
    (hseparation : ∀ i j, label i < label j → row j < col i)
    (k : α) (A B : LaurentPolynomial F) (z : ℤ)
    (hA : ∀ d, d < 0 → A.coeff d = 0) (hB : ∀ d, d < 0 → B.coeff d = 0)
    (houtside : ∀ a, ¬ a < k →
      (∀ i, label i = a → row i < z) ∨ (∀ i, label i = a → z < col i)) :
    profileInverseProjection row col (⅟M) A B z =
      profileInverseProjection (fun i : {i : ν // label i < k} => row i.val)
        (fun i : {i : ν // label i < k} => col i.val)
        (M.toBlock (fun i => label i < k) (fun i => label i < k))⁻¹ A B z := by
  classical
  rw [Matrix.invOf_eq_nonsing_inv, hM.inv_toBlock k]
  exact profileInverseProjection_restrict_blocks row col M⁻¹ label
    (Matrix.blockTriangular_inv_of_blockTriangular hM) hseparation
    (fun a => a < k) A B z hA hB houtside

/-- A complete suffix cap likewise retains the full inverse of its actual
matrix. The triangular zero rectangle supplies its exact right-inverse identity. -/
theorem profileInverseProjection_suffix_cap {ν α F : Type*}
    [Fintype ν] [DecidableEq ν] [LinearOrder α] [CommRing F]
    (row col : ν → ℤ) (M : Matrix ν ν F) [Invertible M] (label : ν → α)
    (hM : M.BlockTriangular label)
    (hseparation : ∀ i j, label i < label j → row j < col i)
    (k : α) (A B : LaurentPolynomial F) (z : ℤ)
    (hA : ∀ d, d < 0 → A.coeff d = 0) (hB : ∀ d, d < 0 → B.coeff d = 0)
    (houtside : ∀ a, ¬ k < a →
      (∀ i, label i = a → row i < z) ∨ (∀ i, label i = a → z < col i)) :
    profileInverseProjection row col (⅟M) A B z =
      profileInverseProjection (fun i : {i : ν // k < label i} => row i.val)
        (fun i : {i : ν // k < label i} => col i.val)
        (M.toBlock (fun i => k < label i) (fun i => k < label i))⁻¹ A B z := by
  classical
  have he : (M.toBlock (fun i => k < label i) (fun i => k < label i))⁻¹ =
      M⁻¹.toBlock (fun i => k < label i) (fun i => k < label i) := by
    let p := fun i => k < label i
    have hm : M.toBlock p p * M⁻¹.toBlock p p +
        M.toBlock p (fun i => ¬ p i) * M⁻¹.toBlock (fun i => ¬ p i) p = 1 := by
      rw [← Matrix.toBlock_mul_eq_add, Matrix.mul_inv_of_invertible M,
        Matrix.toBlock_one_self]
    have hz : M.toBlock p (fun i => ¬ p i) = 0 := by
      apply Matrix.ext
      intro i j
      exact hM ((le_of_not_gt j.property).trans_lt i.property)
    simp only [hz, Matrix.zero_mul, add_zero] at hm
    exact Matrix.inv_eq_right_inv hm
  rw [Matrix.invOf_eq_nonsing_inv, he]
  exact profileInverseProjection_restrict_blocks row col M⁻¹ label
    (Matrix.blockTriangular_inv_of_blockTriangular hM) hseparation
    (fun a => k < a) A B z hA hB houtside

end SkewCornerDescent.Matrix
