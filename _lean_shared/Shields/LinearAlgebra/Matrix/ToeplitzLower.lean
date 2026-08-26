/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Shields.LinearAlgebra.Matrix.TotallyNonneg.Basic

/-!
# Lower-triangular Toeplitz matrices

The **lower-triangular Toeplitz matrix** `T_n(a)` of a coefficient sequence `a : \mathbb{N} \to R`
has entry `a_{i-j}` on and below the diagonal and `0` above it.  Its one structural property is
that it turns Cauchy convolution into matrix multiplication:

\[
  T_n(a)\,T_n(b) = T_n(a \star b),\qquad (a\star b)_n=\sum_{m\le n}a_{n-m}b_m .
\]

The truncation costs nothing, because the convolution for entry `(i,j)` is supported on
`j \le k \le i`, which the `n \times n` window already contains.  So `a \mapsto T_n(a)` is a
monoid homomorphism from the convolution monoid, and a factorization of a sequence into linear
factors becomes a factorization of the matrix into bidiagonal ones.

## Main results

* `Shields.convCoeff`, `Shields.toeplitzLower`
* `Shields.toeplitzLower_mul` — **convolution is matrix multiplication**
* `Shields.toeplitzLower_one`, `Shields.toeplitzLower_rootFactor`
* `Shields.rootProdCoeff`, `Shields.toeplitzLower_rootProd` — the matrix of a product of linear
  factors is the product of their matrices

## Implementation notes

The sequence is indexed by `\mathbb{N}` and the matrix by `Fin n`, so one sequence gives a matrix
at every size and the multiplicativity is stated once rather than per size.  Nothing here needs
`R` beyond a commutative ring.

## References

* A. Böttcher and B. Silbermann, *Introduction to large truncated Toeplitz matrices*, Springer,
  1999, §1.1.

## Tags

toeplitz matrix, lower triangular, convolution, cauchy product
-/

open Finset

namespace Shields

variable {R : Type*} [CommRing R]

/-- Cauchy convolution of coefficient sequences: `(a ⋆ b)_n = ∑_{m≤n} a_{n−m} b_m`,
the coefficients of the product of the two series. -/
def convCoeff (a b : ℕ → R) (n : ℕ) : R :=
  ∑ m ∈ Finset.range (n + 1), a (n - m) * b m

/-- The lower-triangular Toeplitz matrix of a coefficient sequence: entry `(i,j)`
is `a_{i−j}` on and below the diagonal, `0` above it. -/
def toeplitzLower (a : ℕ → R) (n : ℕ) : Matrix (Fin n) (Fin n) R :=
  Matrix.of fun i j => if (j : ℕ) ≤ i then a ((i : ℕ) - j) else 0

@[simp] theorem toeplitzLower_apply (a : ℕ → R) (n : ℕ) (i j : Fin n) :
    toeplitzLower a n i j = if (j : ℕ) ≤ i then a ((i : ℕ) - j) else 0 := rfl

/-- **Toeplitz of a product.**  `T(a) · T(b) = T(a ⋆ b)` exactly, on the finite
truncation.  The convolution for entry `(i,j)` is supported on `j ≤ k ≤ i`, which
the `n×n` window contains, so the truncation costs nothing. -/
theorem toeplitzLower_mul (a b : ℕ → R) (n : ℕ) :
    toeplitzLower a n * toeplitzLower b n = toeplitzLower (convCoeff a b) n := by
  ext i j
  rw [Matrix.mul_apply]
  -- Move to a sum over `range n`, so every index argument happens in `ℕ`.
  have hrange : ∑ k : Fin n, toeplitzLower a n i k * toeplitzLower b n k j
      = ∑ k ∈ Finset.range n,
          (if k ≤ (i : ℕ) then a ((i : ℕ) - k) else 0)
            * (if (j : ℕ) ≤ k then b (k - j) else 0) := by
    rw [Finset.sum_range fun k =>
      (if k ≤ (i : ℕ) then a ((i : ℕ) - k) else 0) * (if (j : ℕ) ≤ k then b (k - j) else 0)]
    exact Finset.sum_congr rfl fun k _ => by simp [toeplitzLower_apply]
  rw [hrange, toeplitzLower_apply]
  by_cases hji : (j : ℕ) ≤ (i : ℕ)
  · rw [if_pos hji, convCoeff]
    -- Cut `range n` down to the support `[j, i]`, then shift `k = j + m`.
    have hsub : Finset.Ico (j : ℕ) ((i : ℕ) + 1) ⊆ Finset.range n := by
      intro k hk
      simp only [Finset.mem_Ico] at hk
      simp only [Finset.mem_range]
      omega
    rw [← Finset.sum_subset hsub ?_]
    · rw [Finset.sum_Ico_eq_sum_range,
        show (i : ℕ) + 1 - (j : ℕ) = (i : ℕ) - (j : ℕ) + 1 from by omega]
      refine Finset.sum_congr rfl fun m hm => ?_
      simp only [Finset.mem_range] at hm
      rw [if_pos (by omega : (j : ℕ) + m ≤ (i : ℕ)),
        if_pos (by omega : (j : ℕ) ≤ (j : ℕ) + m)]
      congr 2 <;> omega
    · intro k _ hk
      simp only [Finset.mem_Ico, not_and_or, not_le, not_lt] at hk
      by_cases h : (j : ℕ) ≤ k
      · rw [if_neg (by omega : ¬ k ≤ (i : ℕ)), zero_mul]
      · rw [if_neg h, mul_zero]
  · rw [if_neg hji]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases h : (j : ℕ) ≤ k
    · rw [if_neg (by omega : ¬ k ≤ (i : ℕ)), zero_mul]
    · rw [if_neg h, mul_zero]

/-- The Toeplitz matrix of the single factor `1 + x t` is the bidiagonal root
factor of `Bidiagonal`: its coefficient sequence is `1, x, 0, 0, …`. -/
theorem toeplitzLower_rootFactor (x : R) (n : ℕ) :
    toeplitzLower (fun m => if m = 0 then 1 else if m = 1 then x else 0) n
      = rootFactor x n := by
  ext i j
  rw [toeplitzLower_apply, rootFactor]
  by_cases hji : (j : ℕ) ≤ (i : ℕ)
  · rw [if_pos hji]
    by_cases h0 : (i : ℕ) - j = 0
    · have : (i : ℕ) = j := by omega
      simp [this]
    · by_cases h1 : (i : ℕ) - j = 1
      · have : (i : ℕ) = (j : ℕ) + 1 := by omega
        have hne : ¬ (i : ℕ) = (j : ℕ) := by omega
        simp [this]
      · have hne : ¬ (i : ℕ) = (j : ℕ) := by omega
        have hne2 : ¬ (i : ℕ) = (j : ℕ) + 1 := by omega
        simp [h0, h1, hne, hne2]
  · have hne : ¬ (i : ℕ) = (j : ℕ) := by omega
    have hne2 : ¬ (i : ℕ) = (j : ℕ) + 1 := by omega
    rw [if_neg hji]
    simp [hne, hne2]

/-- The coefficient sequence of `∏_{y ∈ ys} (1 + y t)`, built by convolving one
root factor at a time. -/
def rootProdCoeff : List R → ℕ → R
  | [], m => if m = 0 then 1 else 0
  | y :: ys, m =>
      convCoeff (fun k => if k = 0 then 1 else if k = 1 then y else 0) (rootProdCoeff ys) m

/-- The Toeplitz matrix of the constant series `1` is the identity. -/
theorem toeplitzLower_one (n : ℕ) :
    toeplitzLower (fun m => if m = 0 then (1 : R) else 0) n = 1 := by
  ext i j
  rw [toeplitzLower_apply, Matrix.one_apply]
  by_cases hji : (j : ℕ) ≤ (i : ℕ)
  · rw [if_pos hji]
    by_cases h : i = j
    · subst h; simp
    · have : ¬ (i : ℕ) - j = 0 := by
        have : (j : ℕ) ≠ i := fun hc => h (Fin.ext hc.symm)
        omega
      simp [this, h]
  · have h : ¬ i = j := fun hc => hji (by rw [hc])
    rw [if_neg hji, if_neg h]

/-- **Toeplitz of a finite Pólya-frequency symbol factors.**  The Toeplitz matrix
of `∏_{y ∈ ys}(1 + y t)` is the product of the bidiagonal root factors of
`Bidiagonal`.  With each factor totally nonnegative and Cauchy–Binet propagating
nonnegativity across a product, this is the finite half of the
Aissen–Schoenberg–Whitney–Edrei input. -/
theorem toeplitzLower_rootProd (ys : List R) (n : ℕ) :
    toeplitzLower (rootProdCoeff ys) n = (ys.map fun y => rootFactor y n).prod := by
  induction ys with
  | nil => simpa [rootProdCoeff] using toeplitzLower_one (R := R) n
  | cons y ys ih =>
      have hstep : rootProdCoeff (y :: ys)
          = convCoeff (fun k => if k = 0 then (1 : R) else if k = 1 then y else 0)
              (rootProdCoeff ys) := rfl
      rw [hstep, ← toeplitzLower_mul, toeplitzLower_rootFactor, ih]
      simp

end Shields
