/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.LinearAlgebra.Vandermonde

/-!
# The exponential Vandermonde determinant

The matrix with entries `\gamma^{k+j-i}/(k+j-i)!` — the finite window of the exponential
coefficient sequence, read as a Toeplitz-like array — has determinant

\[
  \gamma^{\,n(\text{shift})}\prod_{j<n}\frac{j!}{(k+j)!},
\]

a positive multiple of a power of `\gamma`.  In particular it never vanishes for `\gamma>0`.

The proof clears one factorial per row and column, which turns the entries into descending
factorials, and then evaluates the resulting matrix by the standard Vandermonde argument: a
matrix of monic polynomials of strictly increasing degrees evaluated at distinct points has the
Vandermonde determinant, and here the points are `k,k+1,\ldots,k+n-1`, whose Vandermonde product
depends only on the gaps.  `Shields.prod_gaps_eq_prod_factorial` evaluates that product as the
superfactorial `\prod_{j<n} j!`; the closed form below carries the gap product itself.

## Main results

* `Shields.expCoeff` — the coefficient sequence `\gamma^m/m!`
* `Shields.det_monic_eval_eq_pow` — a matrix of monic polynomials of increasing degree evaluated
  at points has the same determinant as the plain power matrix
* `Shields.prod_gaps_eq_prod_factorial` — the Vandermonde product at `0,\ldots,n-1`
* `Shields.det_descFactorial_matrix` — the descending-factorial determinant
* `Shields.expVandermonde` — **the determinant**, in closed form
* `Shields.expVandermonde_one`, `Shields.expVandermonde_two` — the first two sizes

## Implementation notes

The clearing step is stated separately as `Shields.expCoeff_factor`, since that is where the
hypothesis `n \le k+1` is spent: it is what keeps every index nonnegative so that the descending
factorials are the honest ones.

## References

* T. Muir, *A treatise on the theory of determinants*, Dover, 1960, §§175–180.

## Tags

vandermonde, determinant, exponential, descending factorial, totally positive
-/

open Finset Polynomial
open scoped Matrix

namespace Shields

/-- The coefficients of `e^{γt}`: `a_m = γ^m/m!`. -/
noncomputable def expCoeff (γ : ℝ) (m : ℕ) : ℝ := γ ^ m / (Nat.factorial m : ℝ)

/-- **The determinant at `n = 1`.**  The `1×1` minor is `a_k`, and
the closed form reads `γ^k · 0!/k!`. -/
theorem expVandermonde_one (γ : ℝ) (k : ℕ) :
    expCoeff γ k = γ ^ (1 * k) * ((Nat.factorial 0 : ℝ) / (Nat.factorial k : ℝ)) := by
  rw [expCoeff]
  simp [div_eq_mul_inv]

/-- **The determinant at `n = 2`.**  The `2×2` minor is
`a_k² − a_{k+1}a_{k−1}`, and it collapses to `γ^{2k}·(0!·1!)/(k!·(k+1)!)`.

The collapse is where the Vandermonde structure shows: the bracket
`1 − k!·k!/((k+1)!(k−1)!)` is `1 − k/(k+1) = 1/(k+1)`, the single gap of a
two-node Vandermonde. -/
theorem expVandermonde_two (γ : ℝ) (k : ℕ) (hk : 1 ≤ k) :
    expCoeff γ k ^ 2 - expCoeff γ (k + 1) * expCoeff γ (k - 1)
      = γ ^ (2 * k) * (((Nat.factorial 0 * Nat.factorial 1 : ℕ) : ℝ)
          / ((Nat.factorial k * Nat.factorial (k + 1) : ℕ) : ℝ)) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have hfm : (Nat.factorial m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m)
  simp only [expCoeff, Nat.add_sub_cancel, Nat.factorial_succ, Nat.factorial_zero]
  push_cast
  field

/-- **Positivity of the coefficients.**  At `γ > 0` the closed form
is positive, which is the strictness the lemma needs.  Stated at `n = 1`, where
the minor is a single coefficient. -/
theorem expCoeff_pos {γ : ℝ} (hγ : 0 < γ) (k : ℕ) : 0 < expCoeff γ k := by
  rw [expCoeff]
  positivity

/-- **The Vandermonde value at consecutive nodes.**  `∏_{i<j<n}(j − i) = ∏_{j<n} j!`.

This is the `∏_{j=0}^{n-1} j!` the closed form carries: the Vandermonde
determinant at `k, k+1, …, k+n-1` depends only on the gaps, so the `k` drops out
and what survives is the superfactorial. -/
theorem prod_gaps_eq_prod_factorial (n : ℕ) :
    ∏ i ∈ range n, ∏ j ∈ Ioo i n, (j - i) = ∏ j ∈ range n, Nat.factorial j := by
  induction n with
  | zero => simp
  | succ m ih =>
      rw [Finset.prod_range_succ (fun j => Nat.factorial j), ← ih]
      have hfac : Nat.factorial m = ∏ i ∈ range m, (m - i) := by
        rw [Nat.factorial_eq_prod_range_add_one, ← Finset.prod_range_reflect (fun j => j + 1) m]
        refine Finset.prod_congr rfl fun j hj => ?_
        simp only [Finset.mem_range] at hj
        omega
      rw [Finset.prod_range_succ (fun i => ∏ j ∈ Ioo i (m + 1), (j - i)),
        show Finset.Ioo m (m + 1) = (∅ : Finset ℕ) from by ext y; simp,
        Finset.prod_empty, mul_one, hfac, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun i hi => ?_
      simp only [Finset.mem_range] at hi
      rw [show Finset.Ioo i (m + 1) = insert m (Finset.Ioo i m) from by
        rw [Finset.Ioo_insert_right hi, ← Order.succ_eq_add_one, Finset.Ioo_succ_right_eq_Ioc],
        Finset.prod_insert (by simp)]
      ring

/-- **A monic family of degree `i` has the Vandermonde determinant.**  If `p i` is
monic of degree `i`, then `det[p_i(x_j)] = det[x_j^i]`: the coefficient matrix is
lower triangular with unit diagonal, so it contributes a factor `1`.

This is the "clearing factorials" step, in general form. -/
theorem det_monic_eval_eq_pow {R : Type*} [CommRing R] {n : ℕ} (p : Fin n → R[X])
    (hmon : ∀ i, (p i).Monic) (hdeg : ∀ i : Fin n, (p i).natDegree = i) (x : Fin n → R) :
    (Matrix.of fun i j => (p i).eval (x j)).det
      = (Matrix.of fun i j : Fin n => (x j) ^ (i : ℕ)).det := by
  -- Mathlib states this with the polynomial indexed by the column and the node by
  -- the row; both sides here are the transposes of both sides there.
  have h := Matrix.det_eval_matrixOfPolynomials_eq_det_vandermonde x p hdeg hmon
  have hL : (Matrix.of fun i j => (p i).eval (x j))
      = (Matrix.of fun i j : Fin n => (p j).eval (x i))ᵀ := rfl
  have hR : (Matrix.of fun i j : Fin n => (x j) ^ (i : ℕ)) = (Matrix.vandermonde x)ᵀ := rfl
  rw [hL, hR, Matrix.det_transpose, Matrix.det_transpose, ← h]

/-- The entry factorization: `γ^{k+j-i}/(k+j-i)!` splits as a row factor
`γ^{k-i}`, a column factor `γ^j/(k+j)!`, and the descending factorial
`P_i(k+j)`.  This is the "clearing factorials" step made explicit. -/
theorem expCoeff_factor (γ : ℝ) {k n : ℕ} (hk : n ≤ k + 1) (i j : Fin n) :
    expCoeff γ (k + j - i)
      = γ ^ (k - (i : ℕ)) * (γ ^ (j : ℕ) / ((k + j).factorial : ℝ))
        * (((k + j).descFactorial i : ℕ) : ℝ) := by
  have hik : (i : ℕ) ≤ k + (j : ℕ) := by omega
  have hnorm : k + (j : ℕ) - (i : ℕ) = (k - (i : ℕ)) + (j : ℕ) := by omega
  have hfac : (((k - (i : ℕ)) + (j : ℕ)).factorial : ℝ) * ((k + j).descFactorial i : ℝ)
      = ((k + j).factorial : ℝ) := by
    have := Nat.factorial_mul_descFactorial hik
    rw [hnorm] at this
    exact_mod_cast congrArg (Nat.cast : ℕ → ℝ) this
  have hne : (((k - (i : ℕ)) + (j : ℕ)).factorial : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  rw [expCoeff, hnorm, pow_add, div_eq_iff hne]
  field_simp
  linear_combination (γ ^ (k - (i : ℕ)) * γ ^ (j : ℕ)) * hfac.symm

/-- The descending-factorial matrix is the Vandermonde matrix at the nodes
`k, k+1, …, k+n-1`, whose determinant is the superfactorial. -/
theorem det_descFactorial_matrix (k n : ℕ) :
    (Matrix.of fun i j : Fin n => (((k + (j : ℕ)).descFactorial i : ℕ) : ℝ)).det
      = ∏ i : Fin n, ∏ j ∈ Ioi i, (((j : ℕ) : ℝ) - ((i : ℕ) : ℝ)) := by
  have h := det_monic_eval_eq_pow (R := ℝ) (n := n)
    (fun i => descPochhammer ℝ (i : ℕ)) (fun i => monic_descPochhammer ℝ i)
    (fun i => descPochhammer_natDegree ℝ i) (fun j => ((k + (j : ℕ) : ℕ) : ℝ))
  have hstep : (Matrix.of fun i j : Fin n => (((k + (j : ℕ)).descFactorial i : ℕ) : ℝ)).det
      = (Matrix.of fun i j : Fin n => ((k + (j : ℕ) : ℕ) : ℝ) ^ (i : ℕ)).det := by
    rw [← h]; congr 1; ext i j
    simp only [Matrix.of_apply]
    rw [descPochhammer_eval_eq_descFactorial ℝ (k + (j : ℕ)) (i : ℕ)]
  rw [hstep]
  have hv : (Matrix.of fun i j : Fin n => ((k + (j : ℕ) : ℕ) : ℝ) ^ (i : ℕ))
      = (Matrix.vandermonde (fun j : Fin n => ((k + (j : ℕ) : ℕ) : ℝ)))ᵀ := by
    ext i j; simp [Matrix.vandermonde]
  rw [hv, Matrix.det_transpose, Matrix.det_vandermonde]
  refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => ?_
  push_cast
  ring

/-- **The exponential Vandermonde determinant**, general `n`.
\[
  \det[a_{k+j-i}]_{i,j=0}^{n-1}
    = \gamma^{nk}\,\frac{\prod_{i<j<n}(j-i)}{\prod_{j<n}(k+j)!},
\]
the numerator being the gap product `∏_{i<j<n}(j-i)`, which
`Shields.prod_gaps_eq_prod_factorial` evaluates as the superfactorial
`∏_{j<n} j!`.  Requires `n ≤ k+1` so that every index `k+j-i` is genuine rather
than truncated.

At `γ > 0` the right side is positive, which is strict positivity for the
exponential factor. -/
theorem expVandermonde (γ : ℝ) {k n : ℕ} (hk : n ≤ k + 1) :
    (Matrix.of fun i j : Fin n => expCoeff γ (k + j - i)).det
      = (∏ i : Fin n, γ ^ (k - (i : ℕ))) * (∏ j : Fin n, γ ^ (j : ℕ) / ((k + j).factorial : ℝ))
        * ∏ i : Fin n, ∏ j ∈ Ioi i, (((j : ℕ) : ℝ) - ((i : ℕ) : ℝ)) := by
  -- Name the intermediate matrices so the scaling lemmas can unify.
  set D : Matrix (Fin n) (Fin n) ℝ :=
    Matrix.of fun i j => (((k + (j : ℕ)).descFactorial i : ℕ) : ℝ) with hD
  set B : Matrix (Fin n) (Fin n) ℝ :=
    Matrix.of fun i j => γ ^ (j : ℕ) / ((k + j).factorial : ℝ) * D i j with hB
  have hBdet : B.det = (∏ j : Fin n, γ ^ (j : ℕ) / ((k + j).factorial : ℝ)) * D.det :=
    Matrix.det_mul_row _ D
  have hA : (Matrix.of fun i j : Fin n => expCoeff γ (k + j - i))
      = Matrix.of fun i j : Fin n => γ ^ (k - (i : ℕ)) * B i j := by
    ext i j
    rw [Matrix.of_apply, Matrix.of_apply, expCoeff_factor γ hk i j, hB, hD]
    simp only [Matrix.of_apply]
    ring
  rw [hA, Matrix.det_mul_column, hBdet, hD, det_descFactorial_matrix]
  ring


/-! ### Axiom footprint -/

/-- info: 'Shields.prod_gaps_eq_prod_factorial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms prod_gaps_eq_prod_factorial

/-- info: 'Shields.expVandermonde' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms expVandermonde

/-- info: 'Shields.expVandermonde_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms expVandermonde_one

/-- info: 'Shields.expVandermonde_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms expVandermonde_two

end Shields
