/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Shields.LinearAlgebra.Matrix.JacobiComplementaryMinor
import Shields.LinearAlgebra.Matrix.ToeplitzLower

/-!
# The reciprocal of a totally nonnegative power series

If a normalized coefficient sequence `a` has a totally nonnegative lower-triangular Toeplitz
matrix, then so does the sequence `c` of coefficients of the reciprocal series taken at `-t`,

\[
  \sum_{m\ge 0} c_m t^m = \Bigl(\sum_{m\ge 0} a_m(-t)^m\Bigr)^{-1}.
\]

The proof is two identities and one theorem.  `T_n(a)` is unipotent lower triangular, so its
determinant is `1` and its inverse is the Toeplitz matrix of the reciprocal sequence `b`, by
multiplicativity of `a \mapsto T_n(a)`.  The checkerboard conjugate of that inverse is the Toeplitz
matrix of `c_m = (-1)^m b_m`, because `i+j` and `i-j` have the same parity.  And the checkerboard
conjugate of the inverse of a matrix with nonnegative minors again has nonnegative minors, which is
`Shields.minorsNonneg_sigmaConj_inv`.

## Main results

* `Shields.det_toeplitzLower` — a lower-triangular Toeplitz determinant is `a_0^n`
* `Shields.inv_toeplitzLower` — the inverse is the Toeplitz matrix of the reciprocal sequence
* `Shields.minorsNonneg_toeplitzLower_altSeq` — the reciprocal sequence is totally nonnegative
* `Shields.coeff_nonneg_of_minorsNonneg` — a `1 \times 1` minor is a coefficient
* `Shields.altSeq_nonneg` — the reciprocal coefficients at `-t` are nonnegative

## Implementation notes

The reciprocal sequence enters as a hypothesis `convCoeff a b = \delta` rather than as a
construction, so a caller that already has an explicit reciprocal — a rational symbol, say — uses
it directly instead of proving it equal to a recursively defined one.  `Shields.recipCoeff` builds
one for any normalized `a`, which is what makes the hypothesis satisfiable.

Truncation costs nothing: the hypothesis is quantified over the size `n`, and the conclusion at
`n` uses only the hypothesis at `n`, so a statement about the infinite Toeplitz matrix is recovered
by letting `n` grow.

## References

* [M. Aissen, I. J. Schoenberg and A. M. Whitney, *On the generating functions of totally positive
  sequences I*, J. Analyze Math. **2** (1952), 93--103][Aissen1952GeneratingFunctions], Lem. 1
* [S. M. Fallat and C. R. Johnson, *Totally Nonnegative Matrices*][Fallat2011], Thm. 1.3.3

## Tags

toeplitz matrix, total positivity, reciprocal power series, checkerboard
-/

open Finset

namespace Shields

/-! ### The determinant and the inverse of a lower-triangular Toeplitz matrix -/

section CommRing

variable {R : Type*} [CommRing R]

/-- The alternating sequence `c_m = (-1)^m b_m`.  Its generating function is that of `b`
evaluated at `-t`. -/
def altSeq (b : ℕ → R) (m : ℕ) : R := (-1) ^ m * b m

@[simp] theorem altSeq_apply (b : ℕ → R) (m : ℕ) : altSeq b m = (-1) ^ m * b m := rfl

@[simp] theorem altSeq_altSeq (b : ℕ → R) : altSeq (altSeq b) = b := by
  funext m
  rw [altSeq_apply, altSeq_apply, ← mul_assoc, ← pow_add, ← two_mul, pow_mul]
  simp

/-- A lower-triangular Toeplitz matrix has constant diagonal `a_0`, so its determinant is
`a_0^n`. -/
theorem det_toeplitzLower (a : ℕ → R) (n : ℕ) : (toeplitzLower a n).det = a 0 ^ n := by
  rw [Matrix.det_of_lowerTriangular _ (fun i j hij => ?_)]
  · simp [toeplitzLower_apply]
  · rw [toeplitzLower_apply, if_neg (by exact_mod_cast Nat.not_le.mpr hij)]

/-- **The inverse of a lower-triangular Toeplitz matrix is the Toeplitz matrix of the reciprocal
sequence.**  `a \mapsto T_n(a)` carries Cauchy convolution to matrix multiplication, so a
convolution inverse is a matrix inverse. -/
theorem inv_toeplitzLower {a b : ℕ → R}
    (hab : convCoeff a b = fun m => if m = 0 then (1 : R) else 0) (n : ℕ) :
    (toeplitzLower a n)⁻¹ = toeplitzLower b n :=
  Matrix.inv_eq_right_inv (by rw [toeplitzLower_mul, hab]; exact toeplitzLower_one n)

end CommRing

/-! ### The reciprocal sequence of a normalized sequence -/

section Recip

variable {R : Type*} [CommRing R]

/-- The coefficients of `1 / \sum_m a_m t^m` for a normalized `a`, built one at a time from the
convolution identity.  The value at `a_0 \ne 1` is not meaningful; `Shields.convCoeff_recipCoeff`
is stated for `a_0 = 1`. -/
def recipCoeff (a : ℕ → R) : ℕ → R
  | 0 => 1
  | m + 1 => -∑ j : Fin (m + 1), a (m + 1 - (j : ℕ)) * recipCoeff a (j : ℕ)

@[simp] theorem recipCoeff_zero (a : ℕ → R) : recipCoeff a 0 = 1 := by rw [recipCoeff]

theorem recipCoeff_succ (a : ℕ → R) (m : ℕ) :
    recipCoeff a (m + 1) = -∑ j ∈ range (m + 1), a (m + 1 - j) * recipCoeff a j := by
  rw [recipCoeff, ← Finset.sum_range fun j => a (m + 1 - j) * recipCoeff a j]

/-- `recipCoeff a` is a convolution inverse of a normalized `a`. -/
theorem convCoeff_recipCoeff {a : ℕ → R} (ha : a 0 = 1) :
    convCoeff a (recipCoeff a) = fun m => if m = 0 then (1 : R) else 0 := by
  funext m
  cases m with
  | zero => simp [convCoeff, ha, recipCoeff_zero]
  | succ m =>
      rw [convCoeff, Finset.sum_range_succ, Nat.sub_self, ha, one_mul, recipCoeff_succ]
      simp

end Recip

/-! ### The reciprocal of a totally nonnegative sequence -/

section Real

/-- The checkerboard conjugate of a lower-triangular Toeplitz matrix is the Toeplitz matrix of
the alternating sequence: `i+j` and `i-j` differ by `2j`. -/
theorem sigmaConj_toeplitzLower (b : ℕ → ℝ) (n : ℕ) :
    sigmaConj (toeplitzLower b n) = toeplitzLower (altSeq b) n := by
  ext i j
  rw [sigmaConj_apply, toeplitzLower_apply, toeplitzLower_apply]
  by_cases h : (j : ℕ) ≤ (i : ℕ)
  · rw [if_pos h, if_pos h, altSeq_apply]
    congr 1
    rw [show (i : ℕ) + (j : ℕ) = ((i : ℕ) - (j : ℕ)) + 2 * (j : ℕ) by omega, pow_add, pow_mul]
    simp
  · rw [if_neg h, if_neg h, mul_zero]

/-- **The reciprocal of a totally nonnegative sequence is totally nonnegative.**  For a normalized
`a` with `T_n(a)` totally nonnegative and `b` its convolution inverse, the Toeplitz matrix of
`c_m = (-1)^m b_m` is totally nonnegative.  This is Lemma 1 of
[Aissen1952GeneratingFunctions]. -/
theorem minorsNonneg_toeplitzLower_altSeq {a b : ℕ → ℝ} (ha : a 0 = 1)
    (hab : convCoeff a b = fun m => if m = 0 then (1 : ℝ) else 0) {n : ℕ}
    (hA : ∀ r, MinorsNonneg r (toeplitzLower a n)) (r : ℕ) :
    MinorsNonneg r (toeplitzLower (altSeq b) n) := by
  have hdet : 0 < (toeplitzLower a n).det := by rw [det_toeplitzLower, ha, one_pow]; norm_num
  have h := minorsNonneg_sigmaConj_inv hA hdet r
  rwa [inv_toeplitzLower hab n, sigmaConj_toeplitzLower] at h

/-- A coefficient of a sequence whose Toeplitz truncations have nonnegative minors is itself
nonnegative: `a_k` sits at the entry `(k,0)` of the truncation of size `k+1`, so it is a
`1 \times 1` minor. -/
theorem coeff_nonneg_of_minorsNonneg {a : ℕ → ℝ}
    (hA : ∀ n, MinorsNonneg 1 (toeplitzLower a n)) (k : ℕ) : 0 ≤ a k := by
  have hmono : ∀ f : Fin 1 → Fin (k + 1), StrictMono f := by
    intro f x y hxy
    exact absurd (Subsingleton.elim x y) (ne_of_lt hxy)
  have h := hA (k + 1) (fun _ => ⟨k, Nat.lt_succ_self k⟩) (fun _ => ⟨0, Nat.succ_pos k⟩)
    (mem_increasingSelections.mpr (hmono _)) (mem_increasingSelections.mpr (hmono _))
  rwa [Matrix.det_fin_one, Matrix.submatrix_apply, toeplitzLower_apply, if_pos (Nat.zero_le k),
    Nat.sub_zero] at h

/-- The coefficients of the reciprocal series at `-t` are nonnegative.  This is the `1 \times 1`
case of `Shields.minorsNonneg_toeplitzLower_altSeq`. -/
theorem altSeq_nonneg {a b : ℕ → ℝ} (ha : a 0 = 1)
    (hab : convCoeff a b = fun m => if m = 0 then (1 : ℝ) else 0)
    (hA : ∀ n r, MinorsNonneg r (toeplitzLower a n)) (k : ℕ) : 0 ≤ altSeq b k :=
  coeff_nonneg_of_minorsNonneg
    (fun n => minorsNonneg_toeplitzLower_altSeq ha hab (hA n) 1) k

end Real


/-! ### Axiom footprint -/

/-- info: 'Shields.altSeq_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms altSeq_nonneg

end Shields
