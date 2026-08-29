/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Shields.LinearAlgebra.Matrix.BlockMono
import Shields.LinearAlgebra.Matrix.TotallyNonneg.Basic

/-!
# Jacobi's complementary-minor identity

A minor of `A⁻¹` against the complementary minor of `A`.

## Main results

* `Shields.jacobi_minor`: for `A * C = 1` and a splitting `Fin k ⊕ Fin m ≃ Fin N`,
  `det A * det C_{F,G} = ± det A_{Gᶜ,Fᶜ}`, the sign being the checkerboard of the two selections.
* `Shields.det_mul_det_inv_submatrix`: the division-free core, `det B * det D₁₁ = det B₂₂`,
  obtained by taking determinants of two block-triangular matrices.
* `Shields.minorsNonneg_sigmaConj_inv`: the sign-conjugated inverse `Σ A⁻¹ Σ` of a matrix with
  nonnegative minors again has nonnegative minors.

## Implementation notes

The identity needs no adjugate and no division. Writing `B = A_{G,F}` and `D = (A⁻¹)_{F,G}`, so that
`B * D = 1`, the product of `B` with `D₁₁` bordered by an identity block is block triangular, and so
is the result; comparing the two determinants gives the statement.

Mathlib has neither this nor any compound-matrix machinery at the pinned revision -- the
`det … submatrix … inv` results there are all `Matrix.det_submatrix_equiv_self`, which is reindexing
invariance. Note that Desnanot--Jacobi (`Shields.desnanot_jacobi`) is a different theorem despite
the similar name: it relates `det A` to its corner minors, not a minor of `A⁻¹` to a minor of `A`.

## References

* [S. M. Fallat and C. R. Johnson, *Totally Nonnegative Matrices*][Fallat2011], Thm. 1.3.3

## Tags

determinant, minor, Jacobi identity, inverse, total positivity
-/

open Finset

namespace Shields

variable {R : Type*} [CommRing R] {k m N : ℕ}

/-! ### Splitting `Fin N` into a low and a high block -/

/-- The `a`-th index of the low block `{0,…,k-1}`. -/
def lowIdx (hN : k + m = N) (a : Fin k) : Fin N := ⟨a, by omega⟩

/-- The `b`-th index of the high block `{k,…,N-1}`. -/
def highIdx (hN : k + m = N) (b : Fin m) : Fin N := ⟨k + b, by omega⟩

@[simp] theorem lowIdx_val (hN : k + m = N) (a : Fin k) :
    ((lowIdx hN a : Fin N) : ℕ) = (a : ℕ) := rfl

@[simp] theorem highIdx_val (hN : k + m = N) (b : Fin m) :
    ((highIdx hN b : Fin N) : ℕ) = k + (b : ℕ) := rfl

theorem le_highIdx (hN : k + m = N) (b : Fin m) : k ≤ ((highIdx hN b : Fin N) : ℕ) :=
  Nat.le_add_right _ _

theorem strictMono_lowIdx (hN : k + m = N) : StrictMono (lowIdx hN (m := m)) :=
  fun _ _ hab => hab

theorem strictMono_highIdx (hN : k + m = N) : StrictMono (highIdx hN (k := k)) := by
  intro a b hab
  have hab' : (a : ℕ) < (b : ℕ) := hab
  exact Fin.mk_lt_mk.mpr (by omega)

/-- The low block is the image of `lowIdx`, so a sum over the indices below `k` re-indexes to a
sum over `Fin k`. -/
theorem sum_filter_lt_eq_sum_lowIdx (hN : k + m = N) {α : Type*} [AddCommMonoid α]
    (F : Fin N → α) :
    ∑ i ∈ univ.filter fun i : Fin N => (i : ℕ) < k, F i = ∑ a : Fin k, F (lowIdx hN a) := by
  have hset : (univ.filter fun i : Fin N => (i : ℕ) < k) = univ.image (lowIdx hN (m := m)) := by
    ext i
    simp only [mem_filter, mem_univ, true_and, Finset.mem_image]
    exact ⟨fun h => ⟨⟨i, h⟩, Fin.ext rfl⟩, by rintro ⟨a, rfl⟩; exact a.isLt⟩
  rw [hset, Finset.sum_image fun a _ b _ hab => (strictMono_lowIdx hN).injective hab]

/-- The high block of a block-monotone permutation is an increasing selection: `highIdx` lands
at or above `k`, where the permutation is strictly increasing. -/
theorem strictMono_comp_highIdx (hN : k + m = N) {τ : Equiv.Perm (Fin N)} (hτ : BlockMono k τ) :
    StrictMono fun b : Fin m => τ (highIdx hN b) :=
  fun a _ hab => hτ.upper _ _ (strictMono_highIdx hN hab) (le_highIdx hN a)

/-- The canonical splitting `Fin k ⊕ Fin m ≃ Fin N`. -/
def splitEquiv (hN : k + m = N) : Fin k ⊕ Fin m ≃ Fin N :=
  finSumFinEquiv.trans (finCongr hN)

@[simp] theorem splitEquiv_inl (hN : k + m = N) (a : Fin k) :
    splitEquiv hN (Sum.inl a) = lowIdx hN a := rfl

@[simp] theorem splitEquiv_inr (hN : k + m = N) (b : Fin m) :
    splitEquiv hN (Sum.inr b) = highIdx hN b := rfl

/-! ### The block form of a submatrix -/

omit [CommRing R] in
/-- A submatrix indexed by a sum type is the assembly of its four blocks. -/
private theorem submatrix_eq_fromBlocks (M : Matrix (Fin N) (Fin N) R)
    (u v : Fin k ⊕ Fin m → Fin N) :
    M.submatrix u v = Matrix.fromBlocks
      (M.submatrix (u ∘ Sum.inl) (v ∘ Sum.inl)) (M.submatrix (u ∘ Sum.inl) (v ∘ Sum.inr))
      (M.submatrix (u ∘ Sum.inr) (v ∘ Sum.inl)) (M.submatrix (u ∘ Sum.inr) (v ∘ Sum.inr)) := by
  ext a b
  cases a <;> cases b <;> rfl

/-- **Jacobi's complementary-minor identity, sign-free form.**  For `A C = 1` and
two bijections `F, G : Fin k ⊕ Fin m ≃ Fin N`, the minor of `C` on the rows and
columns selected by `F` and `G` pairs with the complementary minor of `A`. -/
theorem det_mul_det_inv_submatrix (A C : Matrix (Fin N) (Fin N) R) (hAC : A * C = 1)
    (F G : Fin k ⊕ Fin m ≃ Fin N) :
    (C.submatrix (⇑F ∘ Sum.inl) (⇑G ∘ Sum.inl)).det * (A.submatrix ⇑G ⇑F).det
      = (A.submatrix (⇑G ∘ Sum.inr) (⇑F ∘ Sum.inr)).det := by
  set B := A.submatrix ⇑G ⇑F with hB
  set D := C.submatrix ⇑F ⇑G with hD
  set B₁₁ := A.submatrix (⇑G ∘ Sum.inl) (⇑F ∘ Sum.inl) with hB₁₁
  set B₁₂ := A.submatrix (⇑G ∘ Sum.inl) (⇑F ∘ Sum.inr) with hB₁₂
  set B₂₁ := A.submatrix (⇑G ∘ Sum.inr) (⇑F ∘ Sum.inl) with hB₂₁
  set B₂₂ := A.submatrix (⇑G ∘ Sum.inr) (⇑F ∘ Sum.inr) with hB₂₂
  set D₁₁ := C.submatrix (⇑F ∘ Sum.inl) (⇑G ∘ Sum.inl) with hD₁₁
  set D₂₁ := C.submatrix (⇑F ∘ Sum.inr) (⇑G ∘ Sum.inl) with hD₂₁
  have hBform : B = Matrix.fromBlocks B₁₁ B₁₂ B₂₁ B₂₂ := submatrix_eq_fromBlocks A _ _
  have hBD : B * D = 1 := by
    rw [hB, hD, Matrix.submatrix_mul_equiv A C ⇑G F ⇑G, hAC, Matrix.submatrix_one_equiv]
  -- the two left-hand blocks of `BD = 1`
  have e11 : B₁₁ * D₁₁ + B₁₂ * D₂₁ = 1 := by
    ext a b
    have h := congrFun (congrFun hBD (Sum.inl a)) (Sum.inl b)
    simpa [hB, hD, hB₁₁, hB₁₂, hD₁₁, hD₂₁, Matrix.mul_apply, Fintype.sum_sum_type,
      Matrix.one_apply, Matrix.add_apply] using h
  have e21 : B₂₁ * D₁₁ + B₂₂ * D₂₁ = 0 := by
    ext a b
    have h := congrFun (congrFun hBD (Sum.inr a)) (Sum.inl b)
    simpa [hB, hD, hB₂₁, hB₂₂, hD₁₁, hD₂₁, Matrix.mul_apply, Fintype.sum_sum_type,
      Matrix.one_apply, Matrix.add_apply] using h
  -- the auxiliary matrix
  have hBX : B * Matrix.fromBlocks D₁₁ 0 D₂₁ 1 = Matrix.fromBlocks 1 B₁₂ 0 B₂₂ := by
    rw [hBform, Matrix.fromBlocks_multiply, e11, e21]
    simp
  have hdet := congrArg Matrix.det hBX
  rw [Matrix.det_mul, Matrix.det_fromBlocks_zero₁₂, Matrix.det_fromBlocks_zero₂₁,
    Matrix.det_one, Matrix.det_one, mul_one, one_mul] at hdet
  rw [mul_comm]
  exact hdet

/-! ### The sign -/

/-- Permuting rows and columns of a determinant.  This is `Matrix.det_reindex`
with the two reindexings taken to be `σ.symm` and `ρ.symm`, whose composite sign
splits as the product of the two. -/
theorem det_submatrix_perm (A : Matrix (Fin N) (Fin N) R) (σ ρ : Equiv.Perm (Fin N)) :
    (A.submatrix ⇑σ ⇑ρ).det
      = ((Equiv.Perm.sign σ : ℤ) : R) * ((Equiv.Perm.sign ρ : ℤ) : R) * A.det := by
  rw [show A.submatrix ⇑σ ⇑ρ = A.reindex σ.symm ρ.symm from rfl, Matrix.det_reindex]
  simp [Equiv.Perm.sign_symm, mul_comm]

/-- **Jacobi's complementary-minor identity.**  The minor of `A^{-1}` on the
selected rows and columns, times
`det A` and the checkerboard sign of the two selections, is the complementary
minor of `A`. -/
theorem jacobi_minor (hN : k + m = N) (A C : Matrix (Fin N) (Fin N) R) (hAC : A * C = 1)
    {ρ σ : Equiv.Perm (Fin N)} (hρ : BlockMono k ρ) (hσ : BlockMono k σ) :
    (C.submatrix (fun a : Fin k => ρ (lowIdx hN a)) (fun a : Fin k => σ (lowIdx hN a))).det
        * ((-1 : R) ^ (∑ a : Fin k, ((ρ (lowIdx hN a) : ℕ) + (σ (lowIdx hN a) : ℕ))) * A.det)
      = (A.submatrix (fun b : Fin m => σ (highIdx hN b))
          (fun b : Fin m => ρ (highIdx hN b))).det := by
  have hkey := det_mul_det_inv_submatrix A C hAC
    ((splitEquiv hN).trans ρ) ((splitEquiv hN).trans σ)
  have hconv : (A.submatrix ⇑((splitEquiv hN).trans σ) ⇑((splitEquiv hN).trans ρ)).det
      = (A.submatrix ⇑σ ⇑ρ).det := by
    rw [← Matrix.det_submatrix_equiv_self (splitEquiv hN) (A.submatrix ⇑σ ⇑ρ)]
    rfl
  rw [hconv, det_submatrix_perm A σ ρ] at hkey
  -- the low block is exactly the index set the sign formula sums over
  have hsum : ∀ τ : Equiv.Perm (Fin N),
      (∑ i ∈ univ.filter fun i : Fin N => (i : ℕ) < k, ((τ i : ℕ) + (i : ℕ)))
        = ∑ a : Fin k, ((τ (lowIdx hN a) : ℕ) + (a : ℕ)) := fun τ =>
    sum_filter_lt_eq_sum_lowIdx hN fun i => (τ i : ℕ) + (i : ℕ)
  have hsgn : ((Equiv.Perm.sign σ : ℤ) : R) * ((Equiv.Perm.sign ρ : ℤ) : R)
      = (-1 : R) ^ (∑ a : Fin k, ((ρ (lowIdx hN a) : ℕ) + (σ (lowIdx hN a) : ℕ))) := by
    rw [hρ.sign, hσ.sign, hsum ρ, hsum σ]
    push_cast
    rw [← pow_add, ← Finset.sum_add_distrib]
    have hshift : (∑ a : Fin k,
          (((σ (lowIdx hN a) : ℕ) + (a : ℕ)) + ((ρ (lowIdx hN a) : ℕ) + (a : ℕ))))
        = (∑ a : Fin k, ((ρ (lowIdx hN a) : ℕ) + (σ (lowIdx hN a) : ℕ)))
          + 2 * ∑ a : Fin k, (a : ℕ) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun a _ => by omega
    rw [hshift, pow_add, pow_mul]
    simp
  rw [hsgn] at hkey
  exact hkey

/-! ### The sign-conjugated inverse of a totally nonnegative matrix -/

/-- The checkerboard conjugate `Σ M Σ`, with `Σ = diag(1,-1,1,…)`. -/
def sigmaConj {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => (-1) ^ ((i : ℕ) + (j : ℕ)) * M i j

@[simp] theorem sigmaConj_apply {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    sigmaConj M i j = (-1) ^ ((i : ℕ) + (j : ℕ)) * M i j := rfl

/-- The checkerboard `Σ = diag(1,-1,1,…)` itself. -/
def sigMat (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.diagonal fun i => (-1) ^ (i : ℕ)

theorem sigMat_mul_self (n : ℕ) : sigMat n * sigMat n = 1 := by
  rw [sigMat, Matrix.diagonal_mul_diagonal]
  refine (Matrix.diagonal_eq_diagonal_iff.mpr fun i => ?_).trans Matrix.diagonal_one
  rw [← pow_add, ← two_mul, pow_mul]
  simp

theorem sigmaConj_eq_conj {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) :
    sigmaConj M = sigMat n * M * sigMat n := by
  ext i j
  rw [Matrix.mul_assoc, sigMat, Matrix.diagonal_mul, Matrix.mul_diagonal, sigmaConj_apply,
    pow_add]
  ring

/-- The checkerboard conjugation is multiplicative: `Σ` is an involution. -/
theorem sigmaConj_mul {n : ℕ} (M N : Matrix (Fin n) (Fin n) ℝ) :
    sigmaConj (M * N) = sigmaConj M * sigmaConj N := by
  rw [sigmaConj_eq_conj, sigmaConj_eq_conj, sigmaConj_eq_conj]
  calc sigMat n * (M * N) * sigMat n
      = sigMat n * M * (sigMat n * sigMat n) * (N * sigMat n) := by
        rw [sigMat_mul_self]; simp [Matrix.mul_assoc]
    _ = sigMat n * M * sigMat n * (sigMat n * N * sigMat n) := by
        simp [Matrix.mul_assoc]

theorem sigmaConj_neg {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) :
    sigmaConj (-M) = -sigmaConj M := by
  ext i j; simp [sigmaConj]

/-- The characteristic polynomial is invariant under checkerboard conjugation. -/
theorem charpoly_sigmaConj {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) :
    (sigmaConj M).charpoly = M.charpoly := by
  have hinv : (sigMat n)⁻¹ = sigMat n := Matrix.inv_eq_right_inv (sigMat_mul_self n)
  have h := Matrix.charpoly_units_conj
    (⟨sigMat n, sigMat n, sigMat_mul_self n, sigMat_mul_self n⟩ :
      (Matrix (Fin n) (Fin n) ℝ)ˣ) M
  simpa [hinv, sigmaConj_eq_conj] using h

/-- A minor of the checkerboard conjugate carries the checkerboard sign of its own
row and column selections. -/
theorem det_submatrix_sigmaConj {n r : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (f g : Fin r → Fin n) :
    ((sigmaConj M).submatrix f g).det
      = (-1) ^ (∑ a : Fin r, ((f a : ℕ) + (g a : ℕ))) * (M.submatrix f g).det := by
  have hsub : ((sigmaConj M).submatrix f g)
      = Matrix.of fun a b => (-1 : ℝ) ^ (f a : ℕ)
          * ((Matrix.of fun a b => (-1 : ℝ) ^ (g b : ℕ) * (M.submatrix f g) a b) a b) := by
    ext a b
    simp only [Matrix.submatrix_apply, Matrix.of_apply, sigmaConj_apply, pow_add]
    ring
  rw [hsub, Matrix.det_mul_column, Matrix.det_mul_row, ← Finset.prod_pow_eq_pow_sum]
  simp only [pow_add, Finset.prod_mul_distrib]
  ring

/-- **`Σ A⁻¹ Σ` is totally nonnegative.**  This is Thm. 1.3.3 of [Fallat2011].
Jacobi's identity turns a
minor of `A⁻¹` into a complementary minor of `A` divided by `det A`, and the
checkerboard sign it carries is exactly the one `Σ` removes. -/
theorem minorsNonneg_sigmaConj_inv {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ r, MinorsNonneg r A) (hdet : 0 < A.det) (r : ℕ) :
    MinorsNonneg r (sigmaConj A⁻¹) := by
  intro f g hf hg
  rw [mem_increasingSelections] at hf hg
  have hrn : r ≤ n := by
    have := Fintype.card_le_of_injective f hf.injective
    simpa using this
  obtain ⟨ρ, hρ, hρf⟩ := exists_blockMono hrn hf
  obtain ⟨σ, hσ, hσg⟩ := exists_blockMono hrn hg
  have hN : r + (n - r) = n := by omega
  have hAC : A * A⁻¹ = 1 :=
    Matrix.mul_nonsing_inv A (isUnit_iff_ne_zero.mpr (ne_of_gt hdet))
  have hkey := jacobi_minor hN A A⁻¹ hAC hρ hσ
  -- the low block reproduces the two selections
  have hρf' : ∀ a : Fin r, ρ (lowIdx hN a) = f a := hρf
  have hσg' : ∀ a : Fin r, σ (lowIdx hN a) = g a := hσg
  simp only [hρf', hσg'] at hkey
  -- the high block is an increasing selection, so its minor is nonnegative
  have hrhs : 0 ≤ (A.submatrix (fun b : Fin (n - r) => σ (highIdx hN b))
      (fun b : Fin (n - r) => ρ (highIdx hN b))).det :=
    hA (n - r) _ _ (mem_increasingSelections.mpr (strictMono_comp_highIdx hN hσ))
      (mem_increasingSelections.mpr (strictMono_comp_highIdx hN hρ))
  rw [← hkey] at hrhs
  rw [det_submatrix_sigmaConj]
  by_contra hneg
  push Not at hneg
  nlinarith [hrhs, hneg, hdet]


/-! ### Axiom footprint -/

/-- info: 'Shields.minorsNonneg_sigmaConj_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms minorsNonneg_sigmaConj_inv

end Shields
