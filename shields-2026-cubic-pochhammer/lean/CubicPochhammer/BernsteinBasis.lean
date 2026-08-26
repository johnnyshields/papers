/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The Bernstein transform and the two binomial revision identities

Substrate for `shields-2026-cubic-pochhammer.tex`,
`subsec:constant-weight-kernel` «The constant-weight kernel»,
`eq:P-def`–`eq:P-coeff`.

The paper reads the Bernstein coefficients of a polynomial off the projective
substitution `t = ξ/(1+ξ)`, which turns the basis `C(N,j)t^j(1-t)^{N-j}` into the
monomials `ξ^j`.  That substitution is a division; the division-free form of the
same statement is the pair of mutually inverse maps

  `∑_i p_i X^i  ↦  ∑_i p_i ξ^i (1+ξ)^{N-i}`,
  `∑_j q_j ξ^j  ↦  ∑_j q_j X^j (1-X)^{N-j}`,

on polynomials of degree at most `N`, and `bernstein_reconstruction` is the
composite being the identity.  It reduces, after swapping the double sum and
reindexing `j = i+l`, to the binomial theorem `(X + (1-X))^{N-i} = 1`.

`revision_one` and `revision_two` are the two elementary identities the paper's
coefficient extraction `eq:P-coeff` runs on, in the uniform ℕ form

  `(n+1)·C(n,ν)·C(n+1-ν,j-ν)   = C(n+1,j)·C(j,ν)·(n+1-ν)`,
  `(n+1)·C(n,ν)·C(n-ν,j-1-ν)   = C(n+1,j)·C(j,ν)·(j-ν)`,

both assembled from `Nat.choose_mul`, `Nat.choose_mul_succ_eq` and
`Nat.add_one_mul_choose_eq`.

Sorry-free, no project axioms.

## Main statements

* `bernstein_reconstruction` --- the two maps of the division-free projective
  Bernstein transform compose to the identity on polynomials of degree at
  most `N`.
* `revision_one`, `revision_two` --- the two binomial revision identities the
  coefficient extraction `eq:P-coeff` runs on, in the uniform `ℕ` form.

## References

* `shields-2026-cubic-pochhammer.tex`, `subsec:constant-weight-kernel`
  «The constant-weight kernel»: `eq:P-def`, `eq:P-coeff`.
-/

open scoped BigOperators

namespace CubicPochhammer

/-- **Bernstein reconstruction.**  Sending `∑_i p_i X^i` to the `ξ`-coefficients
`c_j = ∑_{i≤j} p_i C(N-i,j-i)` of `∑_i p_i ξ^i(1+ξ)^{N-i}` and then reading those
back in the degree-`N` Bernstein basis returns the polynomial. -/
theorem bernstein_reconstruction (N : ℕ) (p : ℕ → ℝ) (X : ℝ) :
    ∑ j ∈ Finset.range (N + 1),
        (∑ i ∈ Finset.range (N + 1),
          (if i ≤ j then p i * (Nat.choose (N - i) (j - i) : ℝ) else 0))
          * X ^ j * (1 - X) ^ (N - j)
      = ∑ i ∈ Finset.range (N + 1), p i * X ^ i := by
  have hpush : ∀ j ∈ Finset.range (N + 1),
      (∑ i ∈ Finset.range (N + 1),
        (if i ≤ j then p i * (Nat.choose (N - i) (j - i) : ℝ) else 0)) * X ^ j * (1 - X) ^ (N - j)
      = ∑ i ∈ Finset.range (N + 1),
        (if i ≤ j then p i * (Nat.choose (N - i) (j - i) : ℝ) * X ^ j * (1 - X) ^ (N - j)
          else 0) := by
    intro j _
    rw [Finset.sum_mul, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by split_ifs <;> ring
  rw [Finset.sum_congr rfl hpush, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_range] at hi
  rw [← Finset.sum_filter]
  have hfilter : (Finset.range (N + 1)).filter (fun j => i ≤ j) = Finset.Ico i (N + 1) := by
    rw [Finset.range_eq_Ico, Finset.Ico_filter_le, max_eq_right (Nat.zero_le i)]
  rw [hfilter, Finset.sum_Ico_eq_sum_range, show N + 1 - i = (N - i) + 1 from by omega]
  have hterm : ∀ l ∈ Finset.range (N - i + 1),
      p i * (Nat.choose (N - i) (i + l - i) : ℝ) * X ^ (i + l) * (1 - X) ^ (N - (i + l))
        = p i * X ^ i * (X ^ l * (1 - X) ^ ((N - i) - l) * (Nat.choose (N - i) l : ℝ)) := by
    intro l hl
    rw [Finset.mem_range] at hl
    rw [show i + l - i = l from by omega, show N - (i + l) = (N - i) - l from by omega, pow_add]
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, ← add_pow]
  simp

/-- **First revision identity**: `(n+1)C(n,ν)C(n+1-ν,j-ν) = C(n+1,j)C(j,ν)(n+1-ν)`. -/
theorem revision_one (n : ℕ) {j ν : ℕ} (hνj : ν ≤ j) :
    (n + 1) * (Nat.choose n ν * Nat.choose (n + 1 - ν) (j - ν))
      = Nat.choose (n + 1) j * Nat.choose j ν * (n + 1 - ν) := by
  have hrev : Nat.choose n ν * (n + 1) = Nat.choose (n + 1) ν * (n + 1 - ν) :=
    Nat.choose_mul_succ_eq n ν
  have hsplit : Nat.choose (n + 1) j * Nat.choose j ν
      = Nat.choose (n + 1) ν * Nat.choose (n + 1 - ν) (j - ν) := Nat.choose_mul hνj
  calc (n + 1) * (Nat.choose n ν * Nat.choose (n + 1 - ν) (j - ν))
      = Nat.choose n ν * (n + 1) * Nat.choose (n + 1 - ν) (j - ν) := by ring
    _ = Nat.choose (n + 1) ν * (n + 1 - ν) * Nat.choose (n + 1 - ν) (j - ν) := by rw [hrev]
    _ = Nat.choose (n + 1) ν * Nat.choose (n + 1 - ν) (j - ν) * (n + 1 - ν) := by ring
    _ = Nat.choose (n + 1) j * Nat.choose j ν * (n + 1 - ν) := by rw [hsplit]

/-- **Second revision identity**: `(n+1)C(n,ν)C(n-ν,j-1-ν) = C(n+1,j)C(j,ν)(j-ν)`.
Both sides are multiplied by `j` and the factor canceled.

The hypothesis is `ν ≤ j - 1`, not `ν ≤ j`, and the difference is load-bearing.
Mathematically the identity holds at `ν = j` too, both sides vanishing — the left
through `C(n-j,-1) = 0`.  But `j - 1 - ν` here is a `ℕ` subtraction, so at `ν = j`
it truncates to `0` and `Nat.choose (n-ν) 0 = 1`, leaving the left side at
`(n+1)C(n,j)` against a right side of `0`.  The statement with `ν ≤ j` is
therefore false: `n = 4, j = 2, ν = 2` gives `30 = 0`.  Consumers sum over
`ν < j` and pick the `ν = j` term up afterwards, over `ℝ`, where the factor
`(j : ℝ) - (ν : ℝ)` is a real subtraction and genuinely vanishes. -/
theorem revision_two (n : ℕ) {j ν : ℕ} (hj : 1 ≤ j) (hνj : ν ≤ j - 1) :
    (n + 1) * (Nat.choose n ν * Nat.choose (n - ν) (j - 1 - ν))
      = Nat.choose (n + 1) j * Nat.choose j ν * (j - ν) := by
  refine Nat.eq_of_mul_eq_mul_right hj ?_
  have hchain : Nat.choose n (j - 1) * Nat.choose (j - 1) ν
      = Nat.choose n ν * Nat.choose (n - ν) (j - 1 - ν) := Nat.choose_mul hνj
  have hscale : (n + 1) * Nat.choose n (j - 1)
      = Nat.choose (n + 1) (j - 1 + 1) * (j - 1 + 1) := Nat.add_one_mul_choose_eq n (j - 1)
  have hshift : Nat.choose (j - 1) ν * (j - 1 + 1)
      = Nat.choose (j - 1 + 1) ν * (j - 1 + 1 - ν) := Nat.choose_mul_succ_eq (j - 1) ν
  rw [show j - 1 + 1 = j from by omega] at hscale hshift
  calc (n + 1) * (Nat.choose n ν * Nat.choose (n - ν) (j - 1 - ν)) * j
      = (n + 1) * (Nat.choose n (j - 1) * Nat.choose (j - 1) ν) * j := by rw [hchain]
    _ = ((n + 1) * Nat.choose n (j - 1)) * (Nat.choose (j - 1) ν * j) := by ring
    _ = (Nat.choose (n + 1) j * j) * (Nat.choose j ν * (j - ν)) := by rw [hscale, hshift]
    _ = Nat.choose (n + 1) j * Nat.choose j ν * (j - ν) * j := by ring

end CubicPochhammer
