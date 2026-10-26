/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.OrderedLocality

/-!
# Complete block response locality

Supports `shields-2026-skew-corner-descent.tex`, «Equal windows and the determinant defect»
(`sec:normal-chart`, `lem:actual-elimination`). Ordered inverse support excludes paths
below their endpoints and identifies a same-block contraction with the full block inverse.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix

variable {ν α R : Type*} [Fintype ν] [DecidableEq ν] [LinearOrder α] [CommRing R]

/-- A full inverse contraction vanishes when its outgoing block precedes its incoming block. -/
theorem inverseContraction_zero_of_order (r c : ν → R) (M : Matrix ν ν R)
    [Invertible M] (b : ν → α) (hM : M.BlockTriangular b) (lo hi : α) (hlt : hi < lo)
    (hr : ∀ i, b i < lo → r i = 0) (hc : ∀ j, hi < b j → c j = 0) :
    inverseContraction r c M = 0 := by
  unfold inverseContraction
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro j _
  by_cases hir : b i < lo
  · rw [hr i hir, zero_mul, zero_mul]
  · by_cases hij : b j < b i
    · rw [Matrix.blockTriangular_inv_of_blockTriangular hM hij, mul_zero, zero_mul]
    · rw [hc j (lt_of_lt_of_le hlt ((le_of_not_gt hir).trans (le_of_not_gt hij))), mul_zero]

omit [DecidableEq ν] in
/-- Diagonal blocks of a product of complete upper block-triangular matrices multiply exactly. -/
theorem blockTriangular_toSquareBlock_mul (M N : Matrix ν ν R) (b : ν → α)
    (hM : M.BlockTriangular b) (hN : N.BlockTriangular b) (k : α) :
    (M * N).toSquareBlock b k = M.toSquareBlock b k * N.toSquareBlock b k := by
  classical
  apply Matrix.ext
  intro i j
  change (∑ l, M i.val l * N l j.val) =
    ∑ l : {l : ν // b l = k}, M i.val l.val * N l.val j.val
  apply Finset.sum_congr_set {l : ν | b l = k}
  · intro l _
    rfl
  · intro l hl
    rcases lt_or_gt_of_ne hl with hlt | hgt
    · rw [hM (by rw [i.property]; exact hlt), zero_mul]
    · rw [hN (by rw [j.property]; exact hgt), mul_zero]

/-- The complete original inverse restricts to the complete inverse of every diagonal block. -/
theorem blockTriangular_inverse_toSquareBlock (M : Matrix ν ν R) [Invertible M]
    (b : ν → α) (hM : M.BlockTriangular b) (k : α) :
    M⁻¹.toSquareBlock b k = (M.toSquareBlock b k)⁻¹ := by
  classical
  have hI := Matrix.blockTriangular_inv_of_blockTriangular hM
  have he := blockTriangular_toSquareBlock_mul M⁻¹ M b hI hM k
  rw [Matrix.inv_mul_of_invertible] at he
  have hone : (1 : Matrix ν ν R).toSquareBlock b k = 1 := by
    apply Matrix.ext
    intro i j
    change (1 : Matrix ν ν R) i.val j.val = (1 : Matrix {i : ν // b i = k} {i : ν // b i = k} R) i j
    simp only [Matrix.one_apply, Subtype.val_inj]
  rw [hone] at he
  let := invertibleOfLeftInverse (M.toSquareBlock b k) (M⁻¹.toSquareBlock b k) he.symm
  simpa only [Matrix.invOf_eq_nonsing_inv] using (invOf_eq_left_inv he.symm).symm

/-- Same-block endpoint support keeps every inverse entry inside that complete block. -/
theorem inverseContraction_same_block (r c : ν → R) (M : Matrix ν ν R)
    [Invertible M] (b : ν → α) (hM : M.BlockTriangular b) (k : α)
    (hr : ∀ i, b i < k → r i = 0) (hc : ∀ j, k < b j → c j = 0) :
    inverseContraction r c M = inverseContraction
      (fun i : {i : ν // b i = k} => r i.val) (fun j => c j.val)
      (M.toSquareBlock b k) := by
  classical
  unfold inverseContraction
  apply Finset.sum_congr_set {i : ν | b i = k}
  · intro i hi
    apply Finset.sum_congr_set {j : ν | b j = k}
    · intro j hj
      have he := congrFun (congrFun (blockTriangular_inverse_toSquareBlock M b hM k)
        ⟨i, hi⟩) ⟨j, hj⟩
      change M⁻¹ i j = (M.toSquareBlock b k)⁻¹ ⟨i, hi⟩ ⟨j, hj⟩ at he
      rw [he]
    · intro j hj
      rcases lt_or_gt_of_ne hj with hjlt | hjgt
      · rw [Matrix.blockTriangular_inv_of_blockTriangular hM (hi ▸ hjlt), mul_zero, zero_mul]
      · rw [hc j hjgt, mul_zero]
  · intro i hi
    apply Finset.sum_eq_zero
    intro j _
    rcases lt_or_gt_of_ne hi with hilt | higt
    · rw [hr i hilt, zero_mul, zero_mul]
    · by_cases hj : k < b j
      · rw [hc j hj, mul_zero]
      · rw [Matrix.blockTriangular_inv_of_blockTriangular hM
          (lt_of_le_of_lt (le_of_not_gt hj) higt), mul_zero, zero_mul]

/-- Independent row and column reindexings preserve the complete inverse
contraction; the inverse exchanges the two equivalences. -/
theorem inverseContraction_equiv_rows_cols {τ : Type*} [Fintype τ] [DecidableEq τ]
    (rows cols : τ ≃ ν) (r c : ν → R) (M : Matrix ν ν R) :
    inverseContraction (r ∘ cols) (c ∘ rows) (M.submatrix rows cols) =
      inverseContraction r c M := by
  unfold inverseContraction
  rw [Matrix.inv_submatrix_equiv]
  apply Fintype.sum_equiv cols
  intro i
  apply Fintype.sum_equiv rows
  intro j
  rfl

/-- Reindexing a complete contraction preserves every inverse entry and both endpoint vectors. -/
theorem inverseContraction_equiv {τ : Type*} [Fintype τ] [DecidableEq τ]
    (e : τ ≃ ν) (r c : ν → R) (M : Matrix ν ν R) :
    inverseContraction (r ∘ e) (c ∘ e) (M.submatrix e e) = inverseContraction r c M := by
  exact inverseContraction_equiv_rows_cols e e r c M

/-- A produced full inverse contraction commutes with a ring homomorphism. -/
theorem map_inverseContraction {S : Type*} [CommRing S] (f : R →+* S)
    (r c : ν → R) (M : Matrix ν ν R) [Invertible M] :
    f (inverseContraction r c M) =
      inverseContraction (f ∘ r) (f ∘ c) (M.map f) := by
  let : Invertible (M.map f) := Invertible.map f.mapMatrix M
  let := Invertible.map f.mapMatrix M
  have hi := map_invOf f.mapMatrix M
  have he (i j : ν) : f ((⅟M) i j) = (⅟(M.map f)) i j :=
    congrFun (congrFun hi i) j
  unfold inverseContraction
  simp only [← Matrix.invOf_eq_nonsing_inv, map_sum, map_mul, Function.comp_apply, he]

end SkewCornerDescent.Matrix
