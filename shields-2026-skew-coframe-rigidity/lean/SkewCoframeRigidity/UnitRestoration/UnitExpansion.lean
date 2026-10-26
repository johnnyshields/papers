/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCoframeRigidity.Coframe.Defs

/-!
# The leading term of a diagram with units

Formalizes the first display of `sc:unit-expansion` in `shields-2026-skew-coframe-rigidity.tex`
(«The complete unit expansion and finite injectivity», `sc:core-leading-term`).  Positive raw
letters are scaled by `ε` (the variable `X` of `R[X]`) while every genuine unit stays one.  The
unit rows and columns are the common betas.  With `r` rows, `u` common betas and core matrix
the letter matrix of the remaining rows and columns, the determinant is
`σ ε^{r-u} (s_{A₀} + ε q)` with `σ = ±1` the simultaneous sorting sign.  Sorry-free.
-/

namespace SkewCoframeRigidity.UnitRestoration

open Polynomial Matrix SkewCoframeRigidity.Coframe

variable {R : Type*} [CommRing R] {n : ℕ}

/-- The scaled letter: positive raw letters carry one factor of `ε = X`, the unit is one. -/
noncomputable def scaledLetter (h : ℕ → R) (k : ℤ) : R[X] :=
  if k < 0 then 0 else if k = 0 then 1 else Polynomial.C (h k.toNat) * Polynomial.X

/-- The scaled Jacobi–Trudi matrix of row and column betas. -/
noncomputable def scaledMatrix (h : ℕ → R) (row col : Fin n → ℤ) : Matrix (Fin n) (Fin n) R[X] :=
  Matrix.of fun i j => scaledLetter h (row i - col j)

/-- The rows that are common betas. -/
def unitRows (row col : Fin n → ℤ) : Set (Fin n) := {i | ∃ j, row i = col j}

/-- The columns that are common betas. -/
def unitCols (row col : Fin n → ℤ) : Set (Fin n) := {j | ∃ i, row i = col j}

theorem scaledLetter_of_ne (h : ℕ → R) {k : ℤ} (hk : k ≠ 0) :
    scaledLetter h k = Polynomial.X * Polynomial.C (letterOf h k) := by
  unfold scaledLetter letterOf
  by_cases h1 : k < 0
  · simp [h1]
  · rw [if_neg h1, if_neg hk, if_neg h1, mul_comm]

theorem constantCoeff_scaledLetter (h : ℕ → R) (k : ℤ) :
    Polynomial.constantCoeff (scaledLetter h k) = if k = 0 then 1 else 0 := by
  unfold scaledLetter
  by_cases h1 : k < 0
  · simp [h1, show k ≠ 0 by omega]
  · by_cases h2 : k = 0 <;> simp [h1, h2]

/-- The common betas pair unit rows with unit columns. -/
theorem exists_unit_equiv (row col : Fin n → ℤ) (hr : Function.Injective row)
    (hc : Function.Injective col) :
    ∃ φ : {i // i ∈ unitRows row col} ≃ {j // j ∈ unitCols row col},
      ∀ i, row i.1 = col (φ i).1 := by
  classical
  let f : {i // i ∈ unitRows row col} → {j // j ∈ unitCols row col} := fun i =>
    ⟨Classical.choose i.2, ⟨i.1, Classical.choose_spec i.2⟩⟩
  have hf : ∀ i, row i.1 = col (f i).1 := fun i => Classical.choose_spec i.2
  have hinj : Function.Injective f := by
    intro i i' hii
    have h1 := hf i
    rw [hii, ← hf i'] at h1
    exact Subtype.ext (hr h1)
  have hsurj : Function.Surjective f := by
    rintro ⟨j, i, hij⟩
    refine ⟨⟨i, j, hij⟩, Subtype.ext ?_⟩
    exact hc (by rw [← hf ⟨i, j, hij⟩, hij])
  exact ⟨Equiv.ofBijective f ⟨hinj, hsurj⟩, hf⟩

/-- The numbers of core rows and core columns agree. -/
theorem nonempty_core_equiv (row col : Fin n → ℤ) (hr : Function.Injective row)
    (hc : Function.Injective col) :
    Nonempty ({i // i ∉ unitRows row col} ≃ {j // j ∉ unitCols row col}) := by
  classical
  obtain ⟨φ, -⟩ := exists_unit_equiv row col hr hc
  have h1 := Fintype.card_congr φ
  have h2 := Fintype.card_subtype_compl (fun i => i ∈ unitRows row col)
  have h3 := Fintype.card_subtype_compl (fun i => i ∈ unitCols row col)
  exact Fintype.card_eq.mp (by simp only [Fintype.card_subtype_compl] at *; omega)

open scoped Classical in
/-- The core letter matrix on the non-unit rows and columns, paired by `e`. -/
noncomputable def coreMatrix (h : ℕ → R) (row col : Fin n → ℤ)
    (e : {i // i ∉ unitRows row col} ≃ {j // j ∉ unitCols row col}) :
    Matrix {i // i ∉ unitRows row col} {i // i ∉ unitRows row col} R :=
  Matrix.of fun r c => letterOf h (row r.1 - col (e c).1)

open scoped Classical in
/-- The simultaneous sorting permutation: a unit row goes to its matching unit column through
`φ`, a core row to its partner column through `e`. -/
noncomputable def sortPerm (row col : Fin n → ℤ)
    (φ : {i // i ∈ unitRows row col} ≃ {j // j ∈ unitCols row col})
    (e : {i // i ∉ unitRows row col} ≃ {j // j ∉ unitCols row col}) : Equiv.Perm (Fin n) :=
  (Equiv.sumCompl (fun i => i ∈ unitRows row col)).symm.trans
    ((Equiv.sumCongr φ e).trans (Equiv.sumCompl (fun j => j ∈ unitCols row col)))

open scoped Classical in
/-- **Leading term of a diagram with units** (`sc:unit-expansion`, first display) with the
sorting sign made explicit: the scaled Jacobi–Trudi determinant is
`sign(τ) ε^{r-u} (s_{A₀} + ε q)`, where `τ` is the sorting permutation of the unit pairing `φ`
and the core pairing `e`, `r - u` is the number of core rows, and `s_{A₀}` is the core
determinant for `e`. -/
theorem det_scaledMatrix_of_equiv (h : ℕ → R) (row col : Fin n → ℤ) (hr : Function.Injective row)
    (hc : Function.Injective col)
    (φ : {i // i ∈ unitRows row col} ≃ {j // j ∈ unitCols row col})
    (hφ : ∀ i, row i.1 = col (φ i).1)
    (e : {i // i ∉ unitRows row col} ≃ {j // j ∉ unitCols row col}) :
    ∃ q : R[X], (scaledMatrix h row col).det =
      ((Equiv.Perm.sign (sortPerm row col φ e) : ℤ) : R[X]) *
        (Polynomial.X ^ Fintype.card {i // i ∉ unitRows row col} *
          (Polynomial.C (coreMatrix h row col e).det + Polynomial.X * q)) := by
  classical
  set ι := Equiv.sumCompl (fun i => i ∈ unitRows row col) with hι
  set κ := (Equiv.sumCongr φ e).trans (Equiv.sumCompl (fun j => j ∈ unitCols row col)) with hκ
  set A := scaledMatrix h row col with hA
  set A' := A.submatrix ι κ with hA'
  set π := κ.trans ι.symm with hπ
  have hdet : A'.det = ((Equiv.Perm.sign π : ℤˣ) : ℤ) * A.det := by
    have : A' = (A.submatrix ι ι).submatrix id π := by
      ext a b; simp [π, A']
    rw [this, Matrix.det_permute', Matrix.det_submatrix_equiv_self]
  have hsq : ((Equiv.Perm.sign π : ℤˣ) : ℤ) * ((Equiv.Perm.sign π : ℤˣ) : ℤ) = 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign π) with h1 | h1 <;> simp [h1]
  have hA_eq : A.det = ((Equiv.Perm.sign π : ℤˣ) : ℤ) * A'.det := by
    rw [hdet, ← mul_assoc]
    push_cast
    rw [← Int.cast_mul, hsq]; simp
  let N : Matrix ({i // i ∈ unitRows row col} ⊕ {i // i ∉ unitRows row col})
      ({i // i ∈ unitRows row col} ⊕ {i // i ∉ unitRows row col}) R[X] :=
    Matrix.of fun a b => match a with
      | Sum.inl i => A' (Sum.inl i) b
      | Sum.inr r => Polynomial.C (letterOf h (row r.1 - col (κ b)))
  let d : {i // i ∈ unitRows row col} ⊕ {i // i ∉ unitRows row col} → R[X] :=
    Sum.elim (fun _ => 1) (fun _ => Polynomial.X)
  have hAN : A' = Matrix.of fun a b => d a * N a b := by
    ext a b
    rcases a with i | r
    · simp [d, N]
    · have hne : row r.1 - col (κ b) ≠ 0 := by
        intro h0
        exact r.2 ⟨κ b, by omega⟩
      simp only [A', A, scaledMatrix, Matrix.submatrix_apply, Matrix.of_apply, d, N,
        Sum.elim_inr, hι, Equiv.sumCompl_apply_inr]
      rw [scaledLetter_of_ne h hne]
  have hdN : A'.det = Polynomial.X ^ Fintype.card {i // i ∉ unitRows row col} * N.det := by
    rw [hAN, Matrix.det_mul_column, Fintype.prod_sum_type]
    simp [d]
  obtain ⟨q, hq⟩ := Polynomial.X_dvd_sub_C (p := N.det)
  have hc0 : N.det.coeff 0 = (coreMatrix h row col e).det := by
    rw [← Polynomial.constantCoeff_apply, RingHom.map_det]
    have hblocks : (Polynomial.constantCoeff.mapMatrix N) =
        Matrix.fromBlocks 1 0 (Polynomial.constantCoeff.mapMatrix N).toBlocks₂₁
          (coreMatrix h row col e) := by
      ext a b
      rcases a with i | r <;> rcases b with i' | c
      · simp only [RingHom.mapMatrix_apply, Matrix.map_apply, N, A', A, scaledMatrix,
          Matrix.submatrix_apply, Matrix.of_apply, hκ, Equiv.trans_apply, Equiv.sumCongr_apply,
          Sum.map_inl, Equiv.sumCompl_apply_inl, hι, Matrix.fromBlocks_apply₁₁,
          constantCoeff_scaledLetter]
        by_cases hii : i = i'
        · subst hii; simp [hφ i]
        · have : row i.1 - col (φ i').1 ≠ 0 := by
            intro h0
            apply hii
            have h1 : col (φ i).1 = col (φ i').1 := by rw [← hφ i]; omega
            exact φ.injective (Subtype.ext (hc h1))
          simp [hii, this]
      · simp only [RingHom.mapMatrix_apply, Matrix.map_apply, N, A', A, scaledMatrix,
          Matrix.submatrix_apply, Matrix.of_apply, hκ, Equiv.trans_apply, Equiv.sumCongr_apply,
          Sum.map_inr, Equiv.sumCompl_apply_inr, hι, Equiv.sumCompl_apply_inl,
          Matrix.fromBlocks_apply₁₂, constantCoeff_scaledLetter, Matrix.zero_apply]
        have : row i.1 - col (e c).1 ≠ 0 := by
          intro h0
          exact (e c).2 ⟨i.1, by omega⟩
        simp [this]
      · simp [N, Matrix.toBlocks₂₁]
      · simp [N, hκ, coreMatrix]
    rw [hblocks, Matrix.det_fromBlocks_zero₁₂, Matrix.det_one, one_mul]
  have hsgn : Equiv.Perm.sign π = Equiv.Perm.sign (sortPerm row col φ e) := by
    rw [← Equiv.Perm.sign_permCongr (Equiv.sumCompl fun i => i ∈ unitRows row col).symm
      (sortPerm row col φ e)]
    congr 1
    ext b
    simp [π, κ, ι, sortPerm, Equiv.permCongr_apply]
  refine ⟨q, ?_⟩
  rw [← hsgn, hA_eq, hdN]
  have : N.det = Polynomial.C (coreMatrix h row col e).det + Polynomial.X * q := by
    rw [← hc0]; linear_combination hq
  rw [this]

open scoped Classical in
/-- **Leading term of a diagram with units** (`sc:unit-expansion`, first display): the scaled
Jacobi–Trudi determinant is `σ ε^{r-u} (s_{A₀} + ε q)` with `σ = ±1`, `r - u` the number of
core rows, and `s_{A₀}` the core determinant for the pairing `e`. -/
theorem det_scaledMatrix (h : ℕ → R) (row col : Fin n → ℤ) (hr : Function.Injective row)
    (hc : Function.Injective col)
    (e : {i // i ∉ unitRows row col} ≃ {j // j ∉ unitCols row col}) :
    ∃ (σ : ℤˣ) (q : R[X]), (scaledMatrix h row col).det =
      ((σ : ℤ) : R[X]) * (Polynomial.X ^ Fintype.card {i // i ∉ unitRows row col} *
        (Polynomial.C (coreMatrix h row col e).det + Polynomial.X * q)) := by
  obtain ⟨φ, hφ⟩ := exists_unit_equiv row col hr hc
  obtain ⟨q, hq⟩ := det_scaledMatrix_of_equiv h row col hr hc φ hφ e
  exact ⟨_, q, hq⟩

end SkewCoframeRigidity.UnitRestoration
