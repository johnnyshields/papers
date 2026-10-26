/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.UnitJoinCoefficients

/-!
# Retained-unit coefficients at one actual zero cut

Formalizes the ordered zero-cut step in `thm:two-row-thin-class` of
`shields-2026-skew-class-inflation.tex`.  Cutting a genuine zero seam
factors the actual constant coefficient into its two connected principal
profiles.  No Hessenberg assumption is needed for this constant layer.
Sorry-free.
-/

namespace SkewClassInflation

open SkewJacobiNegative SkewJacobiNegative.GeneralHessenberg

-- TODO-COPIED: skew-jacobi-negative/lean/SkewJacobiNegative/GeneralHessenberg.lean,
-- leftOfSeam_block, restricted to the underlying matrix reindexing and generalized in the entries.
/-- The left principal block is the actual first consecutive finite interval. -/
theorem left_principal_det {R : Type*} [CommRing R] {n : ℕ}
    (M : Matrix (Fin (n + 2)) (Fin (n + 2)) R) (c : Fin (n + 1)) :
    (M.toSquareBlockProp (fun i => i.val ≤ c.val)).det =
      (M.submatrix (sliceEmbedding 0 c.val (by omega))
        (sliceEmbedding 0 c.val (by omega))).det := by
  classical
  let e : {i : Fin (n + 2) // i.val ≤ c.val} ≃ Fin (c.val + 1) :=
    { toFun := fun i => ⟨i.val.val, by omega⟩
      invFun := fun i => ⟨⟨i.val, by have := c.isLt; have := i.isLt; omega⟩,
        by change i.val ≤ c.val; have := i.isLt; omega⟩
      left_inv := by intro i; apply Subtype.ext; apply Fin.ext; rfl
      right_inv := by intro i; apply Fin.ext; rfl }
  rw [← Matrix.det_reindex_self e]
  apply congrArg Matrix.det
  apply Matrix.ext
  intro i j
  have hi : (e.symm i).val = sliceEmbedding 0 c.val (by omega) i := by
    apply Fin.ext
    change i.val = 0 + i.val
    omega
  have hj : (e.symm j).val = sliceEmbedding 0 c.val (by omega) j := by
    apply Fin.ext
    change j.val = 0 + j.val
    omega
  change M (e.symm i).val (e.symm j).val = M _ _
  rw [hi, hj]

-- TODO-COPIED: skew-jacobi-negative/lean/SkewJacobiNegative/GeneralHessenberg.lean,
-- rightOfSeam_block, restricted to the matrix reindexing and generalized in the entries.
/-- The right principal block is the actual following consecutive interval. -/
theorem right_principal_det {R : Type*} [CommRing R] {n : ℕ}
    (M : Matrix (Fin (n + 2)) (Fin (n + 2)) R) (c : Fin (n + 1)) :
    (M.toSquareBlockProp (fun i => ¬ i.val ≤ c.val)).det =
      (M.submatrix (sliceEmbedding (c.val + 1) (n - c.val) (by have := c.isLt; omega))
        (sliceEmbedding (c.val + 1) (n - c.val) (by have := c.isLt; omega))).det := by
  classical
  let e : {i : Fin (n + 2) // ¬ i.val ≤ c.val} ≃ Fin (n - c.val + 1) :=
    { toFun := fun i => ⟨i.val.val - (c.val + 1), by
        have := i.val.isLt; have := c.isLt; omega⟩
      invFun := fun i => ⟨⟨c.val + 1 + i.val, by
        have := i.isLt; have := c.isLt; omega⟩,
        by change ¬ c.val + 1 + i.val ≤ c.val; omega⟩
      left_inv := by
        intro i
        apply Subtype.ext
        apply Fin.ext
        change c.val + 1 + (i.val.val - (c.val + 1)) = i.val.val
        have hi := i.property
        omega
      right_inv := by intro i; apply Fin.ext; simp }
  rw [← Matrix.det_reindex_self e]
  apply congrArg Matrix.det
  apply Matrix.ext
  intro i j
  have hi : (e.symm i).val =
      sliceEmbedding (c.val + 1) (n - c.val) (by have := c.isLt; omega) i := by
    apply Fin.ext
    rfl
  have hj : (e.symm j).val =
      sliceEmbedding (c.val + 1) (n - c.val) (by have := c.isLt; omega) j := by
    apply Fin.ext
    rfl
  change M (e.symm i).val (e.symm j).val = M _ _
  rw [hi, hj]

/-- Constant matrices of normalized subprofiles are the genuine original principal submatrices. -/
theorem unit_constant_slice {n : ℕ} (P : Profile n) (a k : ℕ) (h : a + k ≤ n) :
    (unitSchur (slice P a k h)).coeff 0 =
      ((Matrix.of fun i j : Fin (n + 1) => (unitEntry (P.xi i - P.zeta j)).coeff 0).submatrix
        (sliceEmbedding a k h) (sliceEmbedding a k h)).det := by
  rw [unitSchur_constant_matrix]
  obtain ⟨hx, hz⟩ := slice_beta P a k h
  apply congrArg Matrix.det
  apply Matrix.ext
  intro i j
  change (unitEntry ((slice P a k h).xi i - (slice P a k h).zeta j)).coeff 0 = _
  rw [congrFun hx i, congrFun hz j]
  apply congrArg (fun z : ℤ => (unitEntry z).coeff 0)
  ring

/-- The ordered genuine zero cut produces its two exact unspecialized component coefficients. -/
theorem unit_zero_cut_constant {n : ℕ} (P : Profile (n + 1)) (c : Fin (n + 1))
    (hc : P.g c = 0) :
    (unitSchur P).coeff 0 =
      (unitSchur (leftOfSeam P c)).coeff 0 * (unitSchur (rightOfSeam P c)).coeff 0 := by
  let M : Matrix (Fin (n + 2)) (Fin (n + 2)) CompleteRing :=
    Matrix.of fun i j => (unitEntry (P.xi i - P.zeta j)).coeff 0
  have ht : ∀ i : Fin (n + 2), ¬ i.val ≤ c.val →
      ∀ j : Fin (n + 2), j.val ≤ c.val → M i j = 0 := by
    intro i hi j hj
    apply unitEntry_coeff_zero_of_nonpos
    have hx := P.xi_strictAnti.antitone
      (show c.succ ≤ i by change c.val + 1 ≤ i.val; omega)
    have hz := P.zeta_strictAnti.antitone
      (show j ≤ c.castSucc by change j.val ≤ c.val; exact hj)
    have hg := P.xi_succ_sub_zeta_castSucc c
    rw [hc] at hg
    omega
  rw [unitSchur_constant_matrix, Matrix.twoBlockTriangular_det _ (fun i => i.val ≤ c.val) ht,
    left_principal_det, right_principal_det]
  rw [leftOfSeam, rightOfSeam, unit_constant_slice, unit_constant_slice]

/-- A one-row connected profile has no unit coordinate and contributes its actual Schur function. -/
theorem unit_single_row_constant (P : Profile 0) :
    (unitSchur P).coeff 0 = P.toBetaDiagram.schur := by
  have ht : SkewJacobiNegative.Staircase.Thick P := by
    intro j
    exact Fin.elim0 j
  have hz := thick_positive_gaps_zeroFree P ht (fun j => Fin.elim0 j)
  rw [unitSchur_eq_C_of_zeroFree P hz, Polynomial.coeff_C_zero]

end SkewClassInflation
