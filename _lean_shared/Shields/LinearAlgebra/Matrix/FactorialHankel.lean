/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Common

/-!
# The factorial Hankel determinant

The Hankel matrix of reciprocal factorials, `\bigl[1/(N-s-t)!\bigr]`, has an explicit
determinant: clearing `1/(N-s)!` from each row turns the entries into descending factorials
`(N-s)^{\underline t}`, and a matrix of monic polynomials of increasing degree evaluated at the
distinct points `N-s` is a Vandermonde.  The value is a signed product of factorials, and in
particular it never vanishes as long as every node `N-s` is a genuine difference.

## Main results

* `Shields.factHankelEntry`, `Shields.factHankel`
* `Shields.factHankelEntry_eq_descFactorial_div` — the clearing step
* `Shields.det_factHankel` — **the closed form**
* `Shields.det_factHankel_ne_zero` — and its nonvanishing

## Tags

hankel matrix, determinant, vandermonde, descending factorial
-/

namespace Shields

open Finset Matrix Polynomial
open scoped Nat

/-- The `(s,t)` entry `1/(N-s-t)!` of the factorial Hankel matrix.  The convention
`1/(-j)! = 0` for `j > 0` is carried by the guard `s + t ≤ N`, so the natural subtraction
`N - s - t` is only ever taken where it is the true difference. -/
def factHankelEntry (N s t : ℕ) : ℚ :=
  if s + t ≤ N then (1 : ℚ) / (((N - s - t)! : ℕ) : ℚ) else 0

/-- The factorial Hankel matrix `D_{ϱ,N} = [1/(N-s-t)!]_{s,t=0}^{ϱ-1}`. -/
def factHankel (ϱ N : ℕ) : Matrix (Fin ϱ) (Fin ϱ) ℚ :=
  Matrix.of fun s t => factHankelEntry N (s : ℕ) (t : ℕ)

/-- The entry identity `1/(N-s-t)! = (N-s)^{\underline t}/(N-s)!`, which clears `1/(N-s)!`
from row `s` and turns the entries into descending factorials.  It holds on the degenerate
range `t > N - s` too: the falling factorial vanishes there, matching the convention that
puts `0` in the entry. -/
theorem factHankelEntry_eq_descFactorial_div (N s t : ℕ) (hs : s ≤ N) :
    factHankelEntry N s t = (((N - s).descFactorial t : ℕ) : ℚ) / (((N - s)! : ℕ) : ℚ) := by
  have hne : ∀ k : ℕ, ((k ! : ℕ) : ℚ) ≠ 0 := fun k =>
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  unfold factHankelEntry
  split_ifs with hst
  · have ht : t ≤ N - s := by omega
    rw [div_eq_div_iff (hne _) (hne _), one_mul]
    have h2 : (N - s)! = (N - s).descFactorial t * (N - s - t)! := by
      rw [Nat.mul_comm]
      exact (Nat.factorial_mul_descFactorial ht).symm
    exact_mod_cast h2
  · have hlt : N - s < t := by omega
    rw [Nat.descFactorial_eq_zero_iff_lt.mpr hlt]
    simp

/-- The Vandermonde determinant on the nodes `0, 1, …, ϱ-1` is the superfactorial
`∏_{j<ϱ} j!`. -/
theorem det_vandermonde_natCast (ϱ : ℕ) :
    (Matrix.vandermonde fun s : Fin ϱ => (s : ℚ)).det = ∏ j ∈ range ϱ, ((j ! : ℕ) : ℚ) := by
  cases ϱ with
  | zero => simp
  | succ n =>
    rw [Matrix.det_vandermonde_id_eq_superFactorial, ← Nat.prod_range_succ_factorial n,
      Nat.cast_prod]

/-- The Vandermonde determinant on the nodes `N, N-1, …, N-ϱ+1`.  Reversing the nodes
against `det_vandermonde_natCast` costs one sign per pair `s < s'`, which is the factor
`(-1)^{ϱ(ϱ-1)/2}` of the closed form. -/
theorem det_vandermonde_sub_natCast (ϱ N : ℕ) :
    (Matrix.vandermonde fun s : Fin ϱ => (N : ℚ) - (s : ℚ)).det =
      (-1 : ℚ) ^ (ϱ * (ϱ - 1) / 2) * ∏ j ∈ range ϱ, ((j ! : ℕ) : ℚ) := by
  have key : (Matrix.vandermonde fun s : Fin ϱ => (N : ℚ) - (s : ℚ)) =
      Matrix.of fun s t : Fin ϱ =>
        (-1 : ℚ) ^ (t : ℕ) * (Matrix.vandermonde fun s : Fin ϱ => (s : ℚ) - (N : ℚ)) s t := by
    ext s t
    rw [Matrix.vandermonde_apply, Matrix.of_apply, Matrix.vandermonde_apply,
      ← neg_sub ((s : ℚ)) ((N : ℚ)), neg_pow]
  rw [key, Matrix.det_mul_row, Matrix.det_vandermonde_sub, det_vandermonde_natCast]
  congr 1
  rw [Finset.prod_pow_eq_pow_sum, Fin.sum_univ_eq_sum_range (fun i => i) ϱ, Finset.sum_range_id]

/-- **The closed form of the factorial Hankel determinant.**  Clearing `1/(N-s)!` from each
row leaves a matrix of monic polynomials of increasing degree at the nodes `N-s`, so the
determinant is the reversed Vandermonde divided by those factorials.  The hypothesis
`ϱ ≤ N + 1` is what makes every node `N - s` a genuine difference. -/
theorem det_factHankel (ϱ N : ℕ) (h : ϱ ≤ N + 1) :
    (factHankel ϱ N).det =
      (-1 : ℚ) ^ (ϱ * (ϱ - 1) / 2) * (∏ j ∈ range ϱ, ((j ! : ℕ) : ℚ)) /
        ∏ s ∈ range ϱ, (((N - s)! : ℕ) : ℚ) := by
  have hsN : ∀ s : Fin ϱ, (s : ℕ) ≤ N := by
    intro s
    have := s.isLt
    omega
  have hfac : factHankel ϱ N =
      Matrix.diagonal (fun s : Fin ϱ => (1 : ℚ) / (((N - (s : ℕ))! : ℕ) : ℚ)) *
        Matrix.of (fun s t : Fin ϱ =>
          (descPochhammer ℚ (t : ℕ)).eval (((N - (s : ℕ) : ℕ) : ℚ))) := by
    ext s t
    simp only [factHankel, Matrix.of_apply, Matrix.diagonal_mul,
      factHankelEntry_eq_descFactorial_div N (s : ℕ) (t : ℕ) (hsN s),
      descPochhammer_eval_eq_descFactorial]
    ring
  have hnodes : (fun s : Fin ϱ => ((N - (s : ℕ) : ℕ) : ℚ)) =
      fun s : Fin ϱ => (N : ℚ) - (s : ℚ) := by
    funext s
    rw [Nat.cast_sub (hsN s)]
  have hden : (∏ s ∈ range ϱ, (1 : ℚ) / (((N - s)! : ℕ) : ℚ))
      = 1 / ∏ s ∈ range ϱ, (((N - s)! : ℕ) : ℚ) := by
    simp only [one_div, ← Finset.prod_inv_distrib]
  rw [hfac, Matrix.det_mul, Matrix.det_diagonal,
    ← Matrix.det_eval_matrixOfPolynomials_eq_det_vandermonde
      (fun s : Fin ϱ => ((N - (s : ℕ) : ℕ) : ℚ)) (fun t : Fin ϱ => descPochhammer ℚ (t : ℕ))
      (fun i => descPochhammer_natDegree ℚ (i : ℕ)) (fun i => monic_descPochhammer ℚ (i : ℕ)),
    hnodes, det_vandermonde_sub_natCast,
    Fin.prod_univ_eq_prod_range (fun s => (1 : ℚ) / (((N - s)! : ℕ) : ℚ)) ϱ, hden]
  ring

/-- The factorial Hankel determinant never vanishes on `ϱ ≤ N + 1`: every factor of the
closed form is a signed product of factorials, hence a nonzero rational. -/
theorem det_factHankel_ne_zero (ϱ N : ℕ) (h : ϱ ≤ N + 1) : (factHankel ϱ N).det ≠ 0 := by
  rw [det_factHankel ϱ N h]
  refine div_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num)) ?_) ?_ <;>
    exact Finset.prod_ne_zero_iff.mpr fun j _ =>
      Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)


/-! ### Axiom footprint -/

/-- info: 'Shields.det_factHankel_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms det_factHankel_ne_zero

end Shields
