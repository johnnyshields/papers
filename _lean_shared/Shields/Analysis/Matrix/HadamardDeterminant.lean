/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.MeanInequalities

/-!
# Hadamard's determinant inequality

For a positive semidefinite matrix the determinant is at most the product of the
diagonal entries:
\[
  \det A \le \prod_i A_{ii}.
\]

The determinant and the diagonal entries of a positive semidefinite matrix are
nonnegative reals, so the statement is phrased on their real parts.

## Main results

* `Shields.prod_le_one_of_sum_le_card` — arithmetic–geometric mean inequality in
  the product form `∑ zᵢ ≤ n → ∏ zᵢ ≤ 1`.
* `Shields.posSemidef_re_det_le_one_of_diag_le_one` — the normalized case, proved
  from AM–GM applied to the eigenvalues against the trace.
* `Shields.posSemidef_re_det_le_prod_re_diag` — **Hadamard's inequality**.

## Implementation notes

The degenerate case, a vanishing diagonal entry, is settled by the `2 × 2`
principal minor rather than by a limiting argument: positive semidefiniteness of
the minor on `{i, j}` gives `‖A i j‖² ≤ A i i * A j j`, so a zero diagonal entry
forces its whole row to vanish and both sides are zero.

## Papers depending on this file

* `growing-rank-edrei` — the Hilbert–Schmidt majorant for the Cauchy–Binet
  expansion of an excitation determinant.
-/

open Finset Matrix
open scoped ComplexOrder

namespace Shields

variable {n : Type*} [Fintype n] [DecidableEq n]

set_option linter.unusedSectionVars false
variable {𝕜 : Type*} [RCLike 𝕜]

/-- **Arithmetic–geometric mean inequality, product form.**  Nonnegative numbers
whose sum is at most the cardinality have product at most one. -/
theorem prod_le_one_of_sum_le_card {z : n → ℝ} (hz : ∀ i, 0 ≤ z i)
    (hsum : ∑ i, z i ≤ (Fintype.card n : ℝ)) : ∏ i, z i ≤ 1 := by
  rcases Nat.eq_zero_or_pos (Fintype.card n) with hN | hN
  · have hempty : (univ : Finset n) = ∅ := by
      rw [← Finset.card_eq_zero, Finset.card_univ]; exact hN
    simp [hempty]
  · set N := Fintype.card n with hNdef
    have hNpos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.2 hN
    have hw : ∑ _i : n, ((N : ℝ))⁻¹ = 1 := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← hNdef]
      field_simp
    have key := Real.geom_mean_le_arith_mean_weighted univ
      (fun _ => ((N : ℝ))⁻¹) z (fun i _ => by positivity) hw (fun i _ => hz i)
    have hP : (0 : ℝ) ≤ ∏ i, z i := Finset.prod_nonneg fun i _ => hz i
    have hL : ∏ i, z i ^ ((N : ℝ))⁻¹ = (∏ i, z i) ^ ((N : ℝ))⁻¹ :=
      Real.finsetProd_rpow _ _ (fun i _ => hz i) _
    have hR : ∑ i, ((N : ℝ))⁻¹ * z i ≤ 1 := by
      rw [← Finset.mul_sum]
      calc ((N : ℝ))⁻¹ * ∑ i, z i ≤ ((N : ℝ))⁻¹ * (N : ℝ) :=
            mul_le_mul_of_nonneg_left hsum (by positivity)
        _ = 1 := by field_simp
    have h1 : (∏ i, z i) ^ ((N : ℝ))⁻¹ ≤ 1 := hL ▸ key.trans hR
    calc ∏ i, z i = ((∏ i, z i) ^ ((N : ℝ))⁻¹) ^ N :=
          (Real.rpow_inv_natCast_pow hP hN.ne').symm
      _ ≤ 1 := pow_le_one₀ (Real.rpow_nonneg hP _) h1

/-- A positive semidefinite matrix whose diagonal entries are at most one has
determinant at most one: the eigenvalues are nonnegative and sum to the trace,
which is at most the cardinality. -/
theorem posSemidef_re_det_le_one_of_diag_le_one {A : Matrix n n 𝕜} (hA : A.PosSemidef)
    (h1 : ∀ i, RCLike.re (A i i) ≤ 1) : RCLike.re A.det ≤ 1 := by
  have hre : RCLike.re A.det = ∏ i, hA.1.eigenvalues i := by
    rw [hA.1.det_eq_prod_eigenvalues, ← RCLike.ofReal_prod, RCLike.ofReal_re]
  have htr : ∑ i, hA.1.eigenvalues i = ∑ i, RCLike.re (A i i) := by
    have h := hA.1.trace_eq_sum_eigenvalues
    rw [Matrix.trace] at h
    have := congrArg (RCLike.re (K := 𝕜)) h
    simpa [Matrix.diag, map_sum] using this.symm
  rw [hre]
  refine prod_le_one_of_sum_le_card (fun i => hA.eigenvalues_nonneg i) ?_
  rw [htr]
  calc ∑ i, RCLike.re (A i i) ≤ ∑ _i : n, (1 : ℝ) := Finset.sum_le_sum fun i _ => h1 i
    _ = (Fintype.card n : ℝ) := by simp [Finset.card_univ]

/-- In a positive semidefinite matrix a vanishing diagonal entry forces its whole
row to vanish: the `2 × 2` principal minor on `{i, j}` has nonnegative
determinant `A i i * A j j - ‖A i j‖²`. -/
theorem posSemidef_apply_eq_zero_of_diag_eq_zero {A : Matrix n n 𝕜} (hA : A.PosSemidef)
    {i : n} (hi : A i i = 0) (j : n) : A i j = 0 := by
  by_cases hij : j = i
  · subst hij; exact hi
  set e : Fin 2 → n := fun k => if k = 0 then i else j with he
  have hminor := (hA.submatrix e).det_nonneg
  have h00 : (A.submatrix e e) 0 0 = A i i := by simp [he]
  have h11 : (A.submatrix e e) 1 1 = A j j := by simp [he]
  have h01 : (A.submatrix e e) 0 1 = A i j := by simp [he]
  have h10 : (A.submatrix e e) 1 0 = A j i := by simp [he]
  rw [Matrix.det_fin_two, h00, h11, h01, h10, hi, zero_mul, zero_sub] at hminor
  have hherm : A j i = starRingEnd 𝕜 (A i j) := by
    have := hA.1.apply j i
    simpa using this.symm
  rw [hherm, RCLike.mul_conj] at hminor
  have : ‖A i j‖ ^ 2 ≤ 0 := by
    have h := RCLike.nonneg_iff.mp hminor |>.1
    simpa using h
  have : ‖A i j‖ = 0 := by nlinarith [norm_nonneg (A i j)]
  exact norm_eq_zero.mp this

/-- **Hadamard's determinant inequality.**  For a positive semidefinite matrix the
determinant is at most the product of the diagonal entries. -/
theorem posSemidef_re_det_le_prod_re_diag {A : Matrix n n 𝕜} (hA : A.PosSemidef) :
    RCLike.re A.det ≤ ∏ i, RCLike.re (A i i) := by
  have hdiag : ∀ i, (0 : ℝ) ≤ RCLike.re (A i i) := fun i =>
    (RCLike.nonneg_iff.mp hA.diag_nonneg).1
  by_cases hz : ∃ i, A i i = 0
  · obtain ⟨i, hi⟩ := hz
    have hrow : ∀ j, A i j = 0 := posSemidef_apply_eq_zero_of_diag_eq_zero hA hi
    have hdet : A.det = 0 := Matrix.det_eq_zero_of_row_eq_zero i hrow
    have hprod : ∏ j, RCLike.re (A j j) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) (by rw [hi, map_zero])
    rw [hdet, hprod, map_zero]
  · rw [not_exists] at hz
    -- every diagonal entry is a positive real
    have hreal : ∀ i, ((RCLike.re (A i i) : ℝ) : 𝕜) = A i i := fun i =>
      RCLike.conj_eq_iff_re.mp (by simpa using (hA.1.apply i i))
    have hpos : ∀ i, (0 : ℝ) < RCLike.re (A i i) := by
      intro i
      rcases (hdiag i).lt_or_eq with h | h
      · exact h
      · exact absurd (by rw [← hreal i, ← h, RCLike.ofReal_zero]) (hz i)
    set s : n → ℝ := fun i => Real.sqrt (RCLike.re (A i i)) with hs
    have hspos : ∀ i, 0 < s i := fun i => Real.sqrt_pos.mpr (hpos i)
    have hssq : ∀ i, s i * s i = RCLike.re (A i i) := fun i =>
      Real.mul_self_sqrt (hdiag i)
    set D : Matrix n n 𝕜 := Matrix.diagonal (fun i => (((s i)⁻¹ : ℝ) : 𝕜)) with hD
    have hDH : Dᴴ = D := by
      rw [hD, Matrix.diagonal_conjTranspose]
      congr 1
      funext i
      simp
    have hB : (D * A * D).PosSemidef := by
      have := hA.mul_mul_conjTranspose_same D
      rwa [hDH] at this
    have hBdiag : ∀ i, (D * A * D) i i = 1 := by
      intro i
      have hexp : (D * A * D) i i = (((s i)⁻¹ : ℝ) : 𝕜) * A i i * (((s i)⁻¹ : ℝ) : 𝕜) := by
        rw [hD]
        simp [Matrix.mul_apply, Matrix.diagonal_apply, Finset.sum_ite_eq,
          Finset.sum_ite_eq', mul_comm, mul_assoc, mul_left_comm]
      rw [hexp, ← hreal i]
      have h1 : ((s i)⁻¹ : ℝ) ≠ 0 := inv_ne_zero (hspos i).ne'
      rw [← RCLike.ofReal_mul, ← RCLike.ofReal_mul]
      rw [show ((s i)⁻¹ * RCLike.re (A i i) * (s i)⁻¹ : ℝ) = 1 by
        rw [← hssq i]; field_simp; exact div_self (hspos i).ne']
      simp
    have hBdet : RCLike.re (D * A * D).det ≤ 1 :=
      posSemidef_re_det_le_one_of_diag_le_one hB (fun i => by rw [hBdiag i]; simp)
    -- unwind the determinant of the scaled matrix
    have hDdet : D.det = (((∏ i, (s i)⁻¹ : ℝ)) : 𝕜) := by
      rw [hD, Matrix.det_diagonal, RCLike.ofReal_prod]
    have hfac : (D * A * D).det = (((∏ i, (s i)⁻¹ : ℝ)) : 𝕜) ^ 2 * A.det := by
      rw [Matrix.det_mul, Matrix.det_mul, hDdet]; ring
    have hprodpos : (0 : ℝ) < ∏ i, RCLike.re (A i i) :=
      Finset.prod_pos fun i _ => hpos i
    have hsq : ((∏ i, (s i)⁻¹ : ℝ)) ^ 2 = (∏ i, RCLike.re (A i i))⁻¹ := by
      rw [← Finset.prod_pow, ← Finset.prod_inv_distrib]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [← hssq i]
      field_simp
    have hkey : RCLike.re (D * A * D).det
        = (∏ i, RCLike.re (A i i))⁻¹ * RCLike.re A.det := by
      rw [hfac, ← RCLike.ofReal_pow, hsq, RCLike.re_ofReal_mul]
    rw [hkey] at hBdet
    have hmul := mul_le_mul_of_nonneg_left hBdet hprodpos.le
    rw [← mul_assoc, mul_inv_cancel₀ hprodpos.ne', one_mul, mul_one] at hmul
    exact hmul

/-! ### The general form -/

/-- The diagonal of the Gram matrix `M Mᴴ` is the squared norm of a row of `M`. -/
theorem self_mul_conjTranspose_diag (M : Matrix n n 𝕜) (i : n) :
    RCLike.re ((M * Mᴴ) i i) = ∑ j, ‖M i j‖ ^ 2 := by
  rw [Matrix.mul_apply, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.conjTranspose_apply, RCLike.star_def, RCLike.mul_conj]
  simp

/-- **Hadamard's determinant inequality, general form.**  The squared modulus of a
determinant is at most the product of the squared row norms.  It follows from the
positive semidefinite case applied to the Gram matrix `M Mᴴ`, whose determinant is
`‖det M‖²` and whose diagonal carries the row energies. -/
theorem normSq_det_le_prod_row_energy (M : Matrix n n 𝕜) :
    ‖M.det‖ ^ 2 ≤ ∏ i, ∑ j, ‖M i j‖ ^ 2 := by
  have hPSD : (M * Mᴴ).PosSemidef := Matrix.posSemidef_self_mul_conjTranspose M
  have hdet : RCLike.re ((M * Mᴴ).det) = ‖M.det‖ ^ 2 := by
    rw [Matrix.det_mul, Matrix.det_conjTranspose, RCLike.star_def, RCLike.mul_conj]
    simp
  have h := posSemidef_re_det_le_prod_re_diag hPSD
  rw [hdet] at h
  refine h.trans (le_of_eq ?_)
  exact Finset.prod_congr rfl fun i _ => self_mul_conjTranspose_diag M i

/-- Hadamard's inequality in the column form. -/
theorem normSq_det_le_prod_col_energy (M : Matrix n n 𝕜) :
    ‖M.det‖ ^ 2 ≤ ∏ j, ∑ i, ‖M i j‖ ^ 2 := by
  have h := normSq_det_le_prod_row_energy Mᵀ
  rw [Matrix.det_transpose] at h
  refine h.trans (le_of_eq (Finset.prod_congr rfl fun j _ => ?_))
  exact Finset.sum_congr rfl fun i _ => by rw [Matrix.transpose_apply]

end Shields
