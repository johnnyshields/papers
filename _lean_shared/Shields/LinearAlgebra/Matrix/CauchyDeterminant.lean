/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Tactic.LinearCombination

/-!
# Cauchy's determinant formula

For the Cauchy matrix `C_{ij} = (x i + y j)⁻¹`,
\[
  \det C \cdot \prod_{i,j}(x_i+y_j)
    = \prod_{i<j}(x_j-x_i)\prod_{i<j}(y_j-y_i).
\]

Mathlib has the Vandermonde determinant but not this one.  The proof here goes through the
Vandermonde determinant rather than through row reduction, which keeps every step inside
`Matrix.det_mul`, `Matrix.det_diagonal` and polynomial evaluation.

Write `p_j(X) = ∏_{l ≠ j}(X + y_l)`, a polynomial of degree `< n`, and `B` for its coefficient
matrix.  Then

* `vandermonde x * B` has entries `p_j(x_i)`, and multiplying row `i` of the Cauchy matrix by
  `∏_j (x_i + y_j)` produces exactly that matrix;
* `vandermonde (-y) * B` has entries `p_j(-y_i)`, which vanish off the diagonal because the
  factor at `l = i` is `y_i - y_i`, so that product is **diagonal** with entries
  `∏_{l ≠ j}(y_l - y_j)`.

Taking determinants of both gives two equations with the same unknown `det B`, and the ordered
pairs `(l, j)` with `l ≠ j` split into `l < j` and `l > j`, which is what turns
`∏_j ∏_{l≠j}(y_l-y_j)` into `det (vandermonde (-y)) · ∏_{i<j}(y_j-y_i)`.

No hypothesis on `x` or `y` beyond invertibility of the entries: where either family repeats a
value both sides vanish, the matrix having two equal rows or columns.

## Main results

* `Shields.cauchyMat`, `Shields.cauchyPoly`, `Shields.cauchyCoeff` — the objects.
* `Shields.det_cauchyMat_mul_prod` — **Cauchy's determinant formula**.

## Tags

determinant, Cauchy matrix, Vandermonde
-/

open Finset Matrix Polynomial

namespace Shields

variable {n : ℕ} {K : Type*} [Field K]

/-- The Cauchy matrix `C_{ij} = (x i + y j)⁻¹`. -/
def cauchyMat (x y : Fin n → K) : Matrix (Fin n) (Fin n) K :=
  Matrix.of fun i j => (x i + y j)⁻¹

/-- The `j`-th node polynomial `∏_{l ≠ j}(X + y_l)`, of degree `n - 1`. -/
noncomputable def cauchyPoly (y : Fin n → K) (j : Fin n) : Polynomial K :=
  ∏ l ∈ (Finset.univ : Finset (Fin n)).erase j, (Polynomial.X + Polynomial.C (y l))

/-- The coefficient matrix of the node polynomials. -/
noncomputable def cauchyCoeff (y : Fin n → K) : Matrix (Fin n) (Fin n) K :=
  Matrix.of fun d j => (cauchyPoly y j).coeff (d : ℕ)

theorem natDegree_cauchyPoly_lt (y : Fin n → K) (j : Fin n) :
    (cauchyPoly y j).natDegree < n := by
  have hle : (cauchyPoly y j).natDegree
      ≤ ∑ _l ∈ (Finset.univ : Finset (Fin n)).erase j, 1 := by
    refine le_trans (Polynomial.natDegree_prod_le _ _) ?_
    refine Finset.sum_le_sum fun l _ => ?_
    exact le_of_eq (Polynomial.natDegree_X_add_C (y l))
  rw [Finset.sum_const, smul_eq_mul, mul_one] at hle
  have hcard : ((Finset.univ : Finset (Fin n)).erase j).card = n - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ, Fintype.card_fin]
  have hn : 0 < n := Fin.pos j
  omega

/-- Evaluating the node polynomials against a Vandermonde matrix. -/
theorem vandermonde_mul_cauchyCoeff (x y : Fin n → K) :
    (Matrix.vandermonde x) * (cauchyCoeff y)
      = Matrix.of fun i j => (cauchyPoly y j).eval (x i) := by
  ext i j
  rw [Matrix.mul_apply]
  simp only [Matrix.vandermonde_apply, cauchyCoeff, Matrix.of_apply]
  rw [Polynomial.eval_eq_sum_range' (natDegree_cauchyPoly_lt y j) (x i)]
  rw [Fin.sum_univ_eq_sum_range (fun d => x i ^ d * (cauchyPoly y j).coeff d) n]
  exact Finset.sum_congr rfl fun d _ => mul_comm _ _

/-- The node polynomial vanishes at the negatives of the other nodes. -/
theorem eval_cauchyPoly_neg (y : Fin n → K) (i j : Fin n) :
    (cauchyPoly y j).eval (-(y i))
      = if i = j then ∏ l ∈ (Finset.univ : Finset (Fin n)).erase j, (y l - y j) else 0 := by
  have hval : (cauchyPoly y j).eval (-(y i))
      = ∏ l ∈ (Finset.univ : Finset (Fin n)).erase j, (y l - y i) := by
    rw [cauchyPoly, Polynomial.eval_prod]
    exact Finset.prod_congr rfl fun l _ => by simp [sub_eq_neg_add]
  rw [hval]
  by_cases hij : i = j
  · subst hij; simp
  · rw [if_neg hij]
    refine Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hij, Finset.mem_univ i⟩) ?_
    ring

/-- The `-y` Vandermonde times the coefficient matrix is diagonal. -/
theorem vandermonde_neg_mul_cauchyCoeff (y : Fin n → K) :
    (Matrix.vandermonde fun i => -(y i)) * (cauchyCoeff y)
      = Matrix.diagonal fun j => ∏ l ∈ (Finset.univ : Finset (Fin n)).erase j, (y l - y j) := by
  rw [vandermonde_mul_cauchyCoeff]
  ext i j
  rw [Matrix.of_apply, eval_cauchyPoly_neg, Matrix.diagonal_apply]
  by_cases hij : i = j
  · subst hij; simp
  · simp [hij]

/-- The ordered pairs `(l, j)` with `l ≠ j` split into `l < j` and `l > j`. -/
theorem prod_erase_split (f : Fin n → Fin n → K) :
    ∏ j : Fin n, ∏ l ∈ (Finset.univ : Finset (Fin n)).erase j, f l j
      = (∏ i : Fin n, ∏ j ∈ Finset.Ioi i, f i j) * ∏ j : Fin n, ∏ l ∈ Finset.Ioi j, f l j := by
  have hsplit : ∀ j : Fin n, ∏ l ∈ (Finset.univ : Finset (Fin n)).erase j, f l j
      = (∏ l ∈ Finset.Iio j, f l j) * ∏ l ∈ Finset.Ioi j, f l j := by
    intro j
    rw [← Finset.prod_union (by
      rw [Finset.disjoint_left]
      intro a ha hb
      rw [Finset.mem_Iio] at ha
      rw [Finset.mem_Ioi] at hb
      exact absurd ha (not_lt.mpr hb.le))]
    congr 1
    ext a
    simp only [Finset.mem_erase, Finset.mem_univ, and_true, Finset.mem_union, Finset.mem_Iio,
      Finset.mem_Ioi]
    constructor
    · intro h
      rcases lt_or_gt_of_ne h with h' | h'
      · exact Or.inl h'
      · exact Or.inr h'
    · rintro (h | h)
      · exact ne_of_lt h
      · exact (ne_of_lt h).symm
  rw [Finset.prod_congr rfl fun j _ => hsplit j, Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_comm' ?_
  intro j l
  simp

/-- **Cauchy's determinant formula.** -/
theorem det_cauchyMat_mul_prod (x y : Fin n → K) (hxy : ∀ i j, x i + y j ≠ 0) :
    (cauchyMat x y).det * ∏ i : Fin n, ∏ j : Fin n, (x i + y j)
      = (∏ i : Fin n, ∏ j ∈ Finset.Ioi i, (x j - x i))
        * ∏ i : Fin n, ∏ j ∈ Finset.Ioi i, (y j - y i) := by
  -- the row scaling turns the Cauchy matrix into the node-polynomial matrix
  have hrow : Matrix.diagonal (fun i => ∏ j : Fin n, (x i + y j)) * cauchyMat x y
      = Matrix.of fun i j => (cauchyPoly y j).eval (x i) := by
    ext i j
    rw [Matrix.diagonal_mul, cauchyMat, Matrix.of_apply, Matrix.of_apply]
    have hval : (cauchyPoly y j).eval (x i)
        = ∏ l ∈ (Finset.univ : Finset (Fin n)).erase j, (x i + y l) := by
      rw [cauchyPoly, Polynomial.eval_prod]
      exact Finset.prod_congr rfl fun l _ => by simp
    have h0 : x i + y j ≠ 0 := hxy i j
    rw [hval, ← Finset.prod_erase_mul _ _ (Finset.mem_univ j)]
    field_simp
  have hdetrow : (∏ i : Fin n, ∏ j : Fin n, (x i + y j)) * (cauchyMat x y).det
      = (Matrix.of fun i j => (cauchyPoly y j).eval (x i) : Matrix (Fin n) (Fin n) K).det := by
    rw [← hrow, Matrix.det_mul, Matrix.det_diagonal]
  -- the two determinant equations
  have hA : Matrix.det (Matrix.vandermonde x) * Matrix.det (cauchyCoeff y)
      = (Matrix.of fun i j => (cauchyPoly y j).eval (x i) : Matrix (Fin n) (Fin n) K).det := by
    rw [← Matrix.det_mul, vandermonde_mul_cauchyCoeff]
  have hB : Matrix.det (Matrix.vandermonde fun i => -(y i)) * Matrix.det (cauchyCoeff y)
      = ∏ j : Fin n, ∏ l ∈ (Finset.univ : Finset (Fin n)).erase j, (y l - y j) := by
    rw [← Matrix.det_mul, vandermonde_neg_mul_cauchyCoeff, Matrix.det_diagonal]
  -- the two Vandermonde determinants
  have hVy : Matrix.det (Matrix.vandermonde fun i => -(y i))
      = ∏ i : Fin n, ∏ j ∈ Finset.Ioi i, (y i - y j) := by
    rw [Matrix.det_vandermonde]
    exact Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => by ring
  have hVx : Matrix.det (Matrix.vandermonde x)
      = ∏ i : Fin n, ∏ j ∈ Finset.Ioi i, (x j - x i) := Matrix.det_vandermonde x
  -- the pair split
  have hpair : ∏ j : Fin n, ∏ l ∈ (Finset.univ : Finset (Fin n)).erase j, (y l - y j)
      = (∏ i : Fin n, ∏ j ∈ Finset.Ioi i, (y i - y j))
        * ∏ i : Fin n, ∏ j ∈ Finset.Ioi i, (y j - y i) := by
    rw [prod_erase_split (fun l j => y l - y j)]
  rw [hpair, hVy] at hB
  by_cases hVyzero : (∏ i : Fin n, ∏ j ∈ Finset.Ioi i, (y i - y j)) = 0
  · -- two of the `y` agree: both sides vanish
    rw [Finset.prod_eq_zero_iff] at hVyzero
    obtain ⟨i, -, hi⟩ := hVyzero
    rw [Finset.prod_eq_zero_iff] at hi
    obtain ⟨j, hji, hij⟩ := hi
    have hyij : y i = y j := sub_eq_zero.mp hij
    have hne : i ≠ j := ne_of_lt (Finset.mem_Ioi.mp hji)
    have hcol : (cauchyMat x y).det = 0 :=
      Matrix.det_zero_of_column_eq hne fun k => by simp [cauchyMat, hyij]
    have hz : (∏ i : Fin n, ∏ j ∈ Finset.Ioi i, (y j - y i)) = 0 := by
      refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
      exact Finset.prod_eq_zero hji (by rw [← hyij]; ring)
    rw [hcol, hz, zero_mul, mul_zero]
  · have hdetB : Matrix.det (cauchyCoeff y)
        = ∏ i : Fin n, ∏ j ∈ Finset.Ioi i, (y j - y i) := by
      field_simp at hB
      exact hB
    rw [← hdetrow] at hA
    rw [hVx, hdetB] at hA
    linear_combination -hA

end Shields
