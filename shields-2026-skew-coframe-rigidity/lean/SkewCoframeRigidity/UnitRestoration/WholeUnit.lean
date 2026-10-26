/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCoframeRigidity.UnitRestoration.Bordered
import SkewCoframeRigidity.UnitRestoration.UnitExpansion
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-!
# The whole-unit series

Formalizes `sc:whole-unit-series` in `shields-2026-skew-coframe-rigidity.tex` at the level of
matrices.  Order the rows and columns as the `u` units followed by the `k` core positions, scale
the positive letters by `ε = X`, and keep the units at `ν`: the matrix is
`[[ν + ε E, ε F], [ε G, ε K]]`, with `E` having zero diagonal (the diagonal entry of a unit
row is the unit itself).  Its determinant is
`ν^u ε^k det K - ε^{k+1} ν^{u-1} tr(F adj(K) G) + O(ε^{k+2})`, and
`tr(F adj(K) G) = ∑_b (row b of F) ⬝ adj(K) (column b of G)` is the sum of the bordered
derivatives `ṡ^{(b)}` of `sc:restoration-polynomial` up to sign.  Sorry-free.
-/

namespace SkewCoframeRigidity.UnitRestoration

open Matrix Polynomial

variable {F : Type*} [Field F] {υ κ : Type*} [Fintype υ] [DecidableEq υ] [Fintype κ]
  [DecidableEq κ]

/-- The matrix `[[ν + ε E, ε F], [ε G, ε K]]` over `F[X]`, `ε = X`. -/
noncomputable def unitBlock (ν : F) (E : Matrix υ υ F) (Fm : Matrix υ κ F) (G : Matrix κ υ F)
    (K : Matrix κ κ F) : Matrix (υ ⊕ κ) (υ ⊕ κ) F[X] :=
  Matrix.fromBlocks (Polynomial.C ν • (1 : Matrix υ υ F[X]) + (Polynomial.X : F[X]) • E.map Polynomial.C)
    ((Polynomial.X : F[X]) • Fm.map Polynomial.C) ((Polynomial.X : F[X]) • G.map Polynomial.C)
    ((Polynomial.X : F[X]) • K.map Polynomial.C)

/-- The first-order coefficient: `tr (W N₁)` for the inverse `W` of the unit-and-core matrix. -/
theorem trace_inv_mul (ν : F) (hν : ν ≠ 0) (E : Matrix υ υ F) (hE : ∀ i, E i i = 0)
    (Fm : Matrix υ κ F) (G : Matrix κ υ F) (K : Matrix κ κ F) :
    Matrix.trace
      (Matrix.fromBlocks (ν⁻¹ • (1 : Matrix υ υ F)) 0 (-(ν⁻¹ • (K⁻¹ * G))) K⁻¹ *
        Matrix.fromBlocks E Fm 0 0) = -ν⁻¹ * Matrix.trace (K⁻¹ * (G * Fm)) := by
  rw [Matrix.fromBlocks_multiply]
  simp only [Matrix.trace, Matrix.diag, Fintype.sum_sum_type, Matrix.fromBlocks_apply₁₁,
    Matrix.fromBlocks_apply₂₂, Matrix.add_apply, Matrix.mul_apply, Matrix.smul_apply,
    Matrix.neg_apply, Matrix.zero_apply, Matrix.one_apply, smul_eq_mul]
  simp [hE, Finset.mul_sum, Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  simp [mul_assoc]

/-- **The whole-unit series** (`sc:whole-unit-series`) for the matrix `[[ν + ε E, ε F], [ε G, ε K]]`:
`det = ν^u ε^k det K - ε^{k+1} ν^{u-1} tr(F adj(K) G) + ε^{k+2} q`. -/
theorem det_unitBlock (ν : F) (hν : ν ≠ 0) (E : Matrix υ υ F) (hE : ∀ i, E i i = 0)
    (Fm : Matrix υ κ F) (G : Matrix κ υ F) (K : Matrix κ κ F) (hK : K.det ≠ 0) :
    ∃ q : F[X], (unitBlock ν E Fm G K).det =
      Polynomial.C (ν ^ Fintype.card υ * K.det) * Polynomial.X ^ Fintype.card κ -
        Polynomial.C (ν ^ Fintype.card υ * ν⁻¹ * Matrix.trace (Fm * K.adjugate * G)) *
          Polynomial.X ^ (Fintype.card κ + 1) +
        Polynomial.X ^ (Fintype.card κ + 2) * q := by
  classical
  have hKu : IsUnit K.det := hK.isUnit
  let N0 : Matrix (υ ⊕ κ) (υ ⊕ κ) F := Matrix.fromBlocks (ν • (1 : Matrix υ υ F)) 0 G K
  let N1 : Matrix (υ ⊕ κ) (υ ⊕ κ) F := Matrix.fromBlocks E Fm 0 0
  let W : Matrix (υ ⊕ κ) (υ ⊕ κ) F :=
    Matrix.fromBlocks (ν⁻¹ • (1 : Matrix υ υ F)) 0 (-(ν⁻¹ • (K⁻¹ * G))) K⁻¹
  have hKK : K * K⁻¹ = 1 := Matrix.mul_nonsing_inv K hKu
  have hNW : N0 * W = 1 := by
    simp only [N0, W, Matrix.fromBlocks_multiply]
    rw [← Matrix.fromBlocks_one]
    congr 1
    · simp [smul_smul, hν]
    · simp
    · simp [Matrix.mul_smul, smul_smul, hν, ← Matrix.mul_assoc, hKK]
    · simpa using hKK
  -- the matrix with the core rows divided by `ε`
  let Nm : Matrix (υ ⊕ κ) (υ ⊕ κ) F[X] :=
    Matrix.fromBlocks (Polynomial.C ν • (1 : Matrix υ υ F[X]) +
      (Polynomial.X : F[X]) • E.map Polynomial.C)
      ((Polynomial.X : F[X]) • Fm.map Polynomial.C) (G.map Polynomial.C) (K.map Polynomial.C)
  have hS : unitBlock ν E Fm G K =
      Matrix.of fun i j => (Sum.elim (fun _ => (1 : F[X])) (fun _ => (Polynomial.X : F[X])) i) *
        Nm i j := by
    refine Matrix.ext fun i j => ?_
    rcases i with i | i <;> rcases j with j | j <;>
      simp [unitBlock, Nm, Matrix.one_apply] <;> split_ifs <;> simp
  have hNm : Nm = N0.map Polynomial.C + (Polynomial.X : F[X]) • N1.map Polynomial.C := by
    refine Matrix.ext fun i j => ?_
    rcases i with i | i <;> rcases j with j | j <;>
      simp [Nm, N0, N1, Matrix.one_apply] <;> split_ifs <;> simp
  have hmapNW : N0.map Polynomial.C * W.map Polynomial.C = 1 := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, ← map_mul, hNW, map_one]
  have hNm2 : Nm = N0.map Polynomial.C *
      (1 + (Polynomial.X : F[X]) • (W * N1).map Polynomial.C) := by
    rw [hNm, Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul]
    congr 2
    have h1 : N0 * (W * N1) = N1 := by rw [← Matrix.mul_assoc, hNW, Matrix.one_mul]
    rw [← Matrix.map_mul, h1]
  have hdet0 : N0.det = ν ^ Fintype.card υ * K.det := by
    simp only [N0]
    rw [Matrix.det_fromBlocks_zero₁₂, Matrix.det_smul, Matrix.det_one, mul_one]
  have htr : Matrix.trace (W * N1) = -ν⁻¹ * (K.det)⁻¹ * Matrix.trace (Fm * K.adjugate * G) := by
    simp only [W, N1]
    rw [trace_inv_mul ν hν E hE Fm G K, Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_mul,
      Matrix.trace_smul, smul_eq_mul]
    rw [mul_assoc, Matrix.trace_mul_comm K.adjugate (G * Fm), Matrix.mul_assoc G Fm,
      Matrix.trace_mul_comm G, Matrix.mul_assoc]
  have hX := Matrix.det_one_add_X_smul (W * N1)
  set d := (1 + (Polynomial.X : F[X]) • (W * N1).map Polynomial.C).det with hd
  set q := d.divX.divX with hq
  have hX' : d = 1 + Polynomial.C (-ν⁻¹ * (K.det)⁻¹ * (Fm * K.adjugate * G).trace) *
      Polynomial.X + Polynomial.X ^ 2 * q := by
    rw [hX, htr, Algebra.smul_def, Polynomial.algebraMap_eq]
    ring
  refine ⟨Polynomial.C (ν ^ Fintype.card υ * K.det) * q, ?_⟩
  have hdm : (N0.map Polynomial.C).det = Polynomial.C N0.det := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
  rw [hS, Matrix.det_mul_column, hNm2, Matrix.det_mul, hdm, ← hd, hdet0, Fintype.prod_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, Finset.prod_const_one, Finset.prod_const,
    Finset.card_univ, one_mul]
  have hKd : Polynomial.C K.det * Polynomial.C K.det⁻¹ = (1 : F[X]) := by
    rw [← Polynomial.C_mul, mul_inv_cancel₀ hK, Polynomial.C_1]
  rw [hX']
  simp only [map_mul, map_neg, map_pow]
  linear_combination (-(Polynomial.C ν ^ Fintype.card υ * Polynomial.C ν⁻¹ *
      Polynomial.C (Fm * K.adjugate * G).trace * Polynomial.X ^ (Fintype.card κ + 1))) * hKd

section Diagram

open SkewCoframeRigidity.Coframe

variable {n : ℕ}

open scoped Classical in
/-- The unit-unit block (zero diagonal), unit-core block, core-unit block of a diagram with units,
for the pairing `φ` of unit rows with unit columns and `e` of core rows with core columns. -/
noncomputable def unitE (h : ℕ → F) (row col : Fin n → ℤ)
    (φ : {i // i ∈ unitRows row col} ≃ {j // j ∈ unitCols row col}) :
    Matrix {i // i ∈ unitRows row col} {i // i ∈ unitRows row col} F :=
  Matrix.of fun i j => if i = j then 0 else letterOf h (row i.1 - col (φ j).1)

noncomputable def unitF (h : ℕ → F) (row col : Fin n → ℤ)
    (e : {i // i ∉ unitRows row col} ≃ {j // j ∉ unitCols row col}) :
    Matrix {i // i ∈ unitRows row col} {i // i ∉ unitRows row col} F :=
  Matrix.of fun i c => letterOf h (row i.1 - col (e c).1)

noncomputable def unitG (h : ℕ → F) (row col : Fin n → ℤ)
    (φ : {i // i ∈ unitRows row col} ≃ {j // j ∈ unitCols row col}) :
    Matrix {i // i ∉ unitRows row col} {i // i ∈ unitRows row col} F :=
  Matrix.of fun r j => letterOf h (row r.1 - col (φ j).1)

open scoped Classical in
/-- **The whole-unit determinant of a diagram** (`sc:whole-unit-series`): the scaled
Jacobi–Trudi determinant is the sorting sign times the determinant of the unit block matrix
with `ν = 1`, whose core block is `coreMatrix`. -/
theorem det_scaledMatrix_eq (h : ℕ → F) (row col : Fin n → ℤ) (hr : Function.Injective row)
    (hc : Function.Injective col)
    (φ : {i // i ∈ unitRows row col} ≃ {j // j ∈ unitCols row col})
    (hφ : ∀ i, row i.1 = col (φ i).1)
    (e : {i // i ∉ unitRows row col} ≃ {j // j ∉ unitCols row col}) :
    ∃ σ : ℤˣ, (scaledMatrix h row col).det = ((σ : ℤ) : F[X]) *
      (unitBlock 1 (unitE h row col φ) (unitF h row col e) (unitG h row col φ)
        (coreMatrix h row col e)).det := by
  set ι := Equiv.sumCompl (fun i => i ∈ unitRows row col) with hι
  set κ := (Equiv.sumCongr φ e).trans (Equiv.sumCompl (fun j => j ∈ unitCols row col)) with hκ
  set A := scaledMatrix h row col with hA
  set π := κ.trans ι.symm with hπ
  have hdet : (A.submatrix ι κ).det = ((Equiv.Perm.sign π : ℤˣ) : ℤ) * A.det := by
    have : A.submatrix ι κ = (A.submatrix ι ι).submatrix id π := by
      ext a b; simp [π]
    rw [this, Matrix.det_permute', Matrix.det_submatrix_equiv_self]
  have hsq : ((Equiv.Perm.sign π : ℤˣ) : ℤ) * ((Equiv.Perm.sign π : ℤˣ) : ℤ) = 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign π) with h1 | h1 <;> simp [h1]
  have hA' : A.submatrix ι κ = unitBlock 1 (unitE h row col φ) (unitF h row col e)
      (unitG h row col φ) (coreMatrix h row col e) := by
    refine Matrix.ext fun a b => ?_
    rcases a with i | r <;> rcases b with j | c
    · by_cases hij : i = j
      · subst hij
        simp only [unitBlock, A, scaledMatrix, hκ, hι, unitE, Matrix.submatrix_apply, Matrix.of_apply, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr, Equiv.sumCompl_apply_inl, Equiv.sumCompl_apply_inr,
          Matrix.fromBlocks_apply₁₁, Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply,
          Matrix.of_apply, Matrix.one_apply_eq, if_true, hφ i, sub_self, scaledLetter, smul_eq_mul]
        simp
      · have hne : row i.1 - col (φ j).1 ≠ 0 := by
          intro h0
          apply hij
          have h1 : col (φ i).1 = col (φ j).1 := by rw [← hφ i]; omega
          exact φ.injective (Subtype.ext (hc h1))
        simp only [unitBlock, A, scaledMatrix, hκ, hι, unitE, Matrix.submatrix_apply, Matrix.of_apply, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr, Equiv.sumCompl_apply_inl, Equiv.sumCompl_apply_inr,
          Matrix.fromBlocks_apply₁₁, Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply,
          Matrix.of_apply, Matrix.one_apply_ne hij, if_neg hij, scaledLetter_of_ne h hne,
          smul_eq_mul]
        ring
    · have hne : row i.1 - col (e c).1 ≠ 0 := by
        intro h0
        exact (e c).2 ⟨i.1, by omega⟩
      simp only [unitBlock, A, scaledMatrix, hκ, hι, unitF, Matrix.submatrix_apply, Matrix.of_apply, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr, Equiv.sumCompl_apply_inl, Equiv.sumCompl_apply_inr,
        Matrix.fromBlocks_apply₁₂, Matrix.smul_apply, Matrix.map_apply, Matrix.of_apply,
        scaledLetter_of_ne h hne, smul_eq_mul]
    · have hne : row r.1 - col (φ j).1 ≠ 0 := by
        intro h0
        exact r.2 ⟨(φ j).1, by omega⟩
      simp only [unitBlock, A, scaledMatrix, hκ, hι, unitG, Matrix.submatrix_apply, Matrix.of_apply, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr, Equiv.sumCompl_apply_inl, Equiv.sumCompl_apply_inr,
        Matrix.fromBlocks_apply₂₁, Matrix.smul_apply, Matrix.map_apply, Matrix.of_apply,
        scaledLetter_of_ne h hne, smul_eq_mul]
    · have hne : row r.1 - col (e c).1 ≠ 0 := by
        intro h0
        exact r.2 ⟨(e c).1, by omega⟩
      simp only [unitBlock, A, scaledMatrix, hκ, hι, coreMatrix, Matrix.submatrix_apply, Matrix.of_apply, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr, Equiv.sumCompl_apply_inl, Equiv.sumCompl_apply_inr,
        Matrix.fromBlocks_apply₂₂, Matrix.smul_apply, Matrix.map_apply, Matrix.of_apply,
        scaledLetter_of_ne h hne, smul_eq_mul]
  refine ⟨Equiv.Perm.sign π, ?_⟩
  rw [← hA', hdet]
  push_cast
  rw [← mul_assoc, ← Int.cast_mul, hsq]; simp

open scoped Classical in
/-- **The whole-unit series of a diagram** (`sc:whole-unit-series`): with `k` core rows, the
scaled determinant is `σ ε^k (s_B - ε T + ε² q)`, where `s_B = det (coreMatrix)` and
`T = tr (F adj(K) G)` is the sum over the unit positions of the bordered derivatives
`-ṡ^{(b)} = b_b adj(M_B) a_b`. -/
theorem det_scaledMatrix_series (h : ℕ → F) (row col : Fin n → ℤ) (hr : Function.Injective row)
    (hc : Function.Injective col)
    (φ : {i // i ∈ unitRows row col} ≃ {j // j ∈ unitCols row col})
    (hφ : ∀ i, row i.1 = col (φ i).1)
    (e : {i // i ∉ unitRows row col} ≃ {j // j ∉ unitCols row col})
    (hK : (coreMatrix h row col e).det ≠ 0) :
    ∃ (σ : ℤˣ) (q : F[X]), (scaledMatrix h row col).det = ((σ : ℤ) : F[X]) *
      (Polynomial.X ^ Fintype.card {i // i ∉ unitRows row col} *
        (Polynomial.C (coreMatrix h row col e).det -
          Polynomial.C (Matrix.trace (unitF h row col e * (coreMatrix h row col e).adjugate *
            unitG h row col φ)) * Polynomial.X + Polynomial.X ^ 2 * q)) := by
  obtain ⟨σ, hσ⟩ := det_scaledMatrix_eq h row col hr hc φ hφ e
  obtain ⟨q, hq⟩ := det_unitBlock (1 : F) one_ne_zero (unitE h row col φ)
    (fun i => by simp [unitE]) (unitF h row col e) (unitG h row col φ)
    (coreMatrix h row col e) hK
  refine ⟨σ, q, ?_⟩
  rw [hσ, hq]
  simp only [one_pow, one_mul, inv_one, mul_one, map_mul, map_one]
  ring

end Diagram

end SkewCoframeRigidity.UnitRestoration
