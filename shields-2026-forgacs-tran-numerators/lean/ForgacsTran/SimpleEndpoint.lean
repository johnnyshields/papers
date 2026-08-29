/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib
import ForgacsTran.DominanceFT

/-!
# The simple lower endpoint, `ρ = 1`

`thm:weighted-dominance` covers a simple smallest zero of `Q` -- its proof reads
"a fixed circle contains the principal pair when the smallest zero is *simple*
and the full `ρ`-root endpoint cluster when it has multiplicity `ρ > 1`".  The
Lean was narrower.  This module records why the narrowing was not removable by
relaxing a binder, and what it took to remove it.

## The binder cannot be relaxed

`clusterAlpha x₁ ρ j = -x₁ω_j/sin(π/ρ)` divides by `sin(π/ρ)`, which is `0` at
`ρ = 1`.  So `clusterAlpha x₁ 1 j` is not a degenerate case of the formula but
the division convention's `0` (`Cluster.clusterAlpha_one_eq_zero`), and
`Cluster.clusterAlpha_ne_zero` is false there rather than merely unproven.
Relaxing `2 ≤ ρ` to `1 ≤ ρ` would give a theorem about that junk value.

## What the multiplicity hypothesis was really doing

`hρ` was consumed at the **principal** cluster index `jp₀`, which exists whatever
`n₀` is -- not only at the nonprincipal indices that vanish with the cluster.
Three further hypotheses did the same: `hcB₀`, `hcQ₀`, `hBp₀` and `hEp₀` all
speak about `jp₀`.  All four, and `hρ`, are consumed only inside
`hratio₀`'s `∀ i : Fin n₀`, so all five are now conditioned on `0 < n₀`, in the
shape the upper endpoint's `hn₁r : 0 < n₁ → 2 ≤ r` already had.  That is
`weighted_dominance_of_branch_any_multiplicity`;
`weighted_dominance_of_branch` is its `ρ ≥ 2` specialization, so the composition
layer is unchanged.

## Why conditioning `hρ` alone was not enough

`hEp₀` asks for `∂_tD(γ(δ))/δ^{ρ-1} → c_Q·α_p^{ρ-1}` with `c_Q ≠ 0`.  The
exponent is really `k - 1` for the denominator multiplicity `k = max{ρ,2}` of
`lem:amplitude-divisor`, and `ρ - 1 = k - 1` exactly when `ρ ≥ 2`.  At `ρ = 1`
the endpoint is a collision of the principal pair, so `k = 2`, `∂_tD` vanishes
there to order `1`, and `hEp₀` with exponent `0` and `c_Q ≠ 0` is **false**.
`derivative_eval_eq_zero_of_two_le_rootMultiplicity` is the half of that which is
a fact about polynomials; `scripts/check_simple_endpoint.py` measures the other
half at two `ρ = 1` pencils, where `|∂_tD(γ(θ))|/θ` converges to a nonzero
constant.

That script also records the geometric reason the cluster machinery cannot
describe this endpoint at all: at `ρ = 1` the collision point is **not a zero of
`Q`**, while `clusterAlpha` expands about `x₁`, the smallest zero.

## Main statements

* `not_clusterAlpha_ne_zero_one` — `Cluster.clusterAlpha_ne_zero` is false at
  `ρ = 1`, where the direction is the division convention's junk value.
* `derivative_eval_eq_zero_of_two_le_rootMultiplicity` — at a collision the
  denominator's derivative vanishes, which is what `hEp₀` denies at `ρ = 1`.
* `hEp_false_of_rho_one` — at `ρ = 1` the exponent `ρ - 1` is `0`, so `hEp₀`
  asks for the limit `c_Q ≠ 0`, while the collision forces `∂_tD → 0`.

## Tags

simple endpoint, multiplicity, endpoint cluster, weighted dominance
-/

namespace ForgacsTran

open Polynomial

/-! ### The cluster directions degenerate at `ρ = 1` -/

/-- **`Cluster.clusterAlpha_ne_zero` is false at `ρ = 1`, not merely unproven** —
the binder `2 ≤ ρ` on its consumers is therefore not relaxable. -/
theorem not_clusterAlpha_ne_zero_one (x₁ : ℝ) (j : ℕ) :
    ¬ clusterAlpha x₁ 1 j ≠ 0 := by
  rw [not_not]
  exact clusterAlpha_one_eq_zero x₁ j

/-! ### A collision kills the denominator's derivative -/

/-- At a root of multiplicity at least two the derivative vanishes.  At the
`ρ = 1` lower endpoint the principal pair collides, so `k = 2` and this applies
-- which is exactly what `hEp₀`'s nonzero limit denies. -/
theorem derivative_eval_eq_zero_of_two_le_rootMultiplicity {P : Polynomial ℂ}
    (hP : P ≠ 0) {a : ℂ} (h : 2 ≤ P.rootMultiplicity a) :
    (derivative P).eval a = 0 :=
  ((Polynomial.one_lt_rootMultiplicity_iff_isRoot hP).1 h).2

/-- **`hEp₀` is false at `ρ = 1`.**  Its limit is `c_Q·α_p^{ρ-1}`, which at
`ρ = 1` is `c_Q·0^0 = c_Q`; so it asserts that `∂_tD` along the branch tends to
something nonzero.  At a collision of the principal pair the limit is `0`.

The continuity of `∂_tD` along the branch is taken as a hypothesis: it is not a
binder of `weighted_dominance_of_branch`, and the point here is the
contradiction, not the continuity. -/
theorem hEp_false_of_rho_one {Q : Polynomial ℂ} {r : ℕ} {z τ : ℝ → ℝ}
    {te₀ cQ₀ : ℂ} {x₁ : ℝ} {jp₀ : ℕ}
    (hP₀ : ftDen Q r ((z 0 : ℝ) : ℂ) ≠ 0)
    (hγ0₀ : ftPrincipal τ 0 = te₀)
    (hk₀ : 2 ≤ (ftDen Q r ((z 0 : ℝ) : ℂ)).rootMultiplicity te₀)
    (hcont : Filter.Tendsto
      (fun δ : ℝ => (derivative (ftDen Q r ((z δ : ℝ) : ℂ))).eval (ftPrincipal τ δ))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds ((derivative (ftDen Q r ((z 0 : ℝ) : ℂ))).eval (ftPrincipal τ 0))))
    (hcQ₀ : cQ₀ ≠ 0)
    (hEp₀ : Filter.Tendsto
      (fun δ : ℝ => (derivative (ftDen Q r ((z δ : ℝ) : ℂ))).eval (ftPrincipal τ δ)
        / ((δ : ℝ) : ℂ) ^ (((1 : ℕ) - 1 : ℕ) : ℤ))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (cQ₀ * clusterAlpha x₁ 1 jp₀ ^ ((1 : ℕ) - 1)))) :
    False := by
  have hzero : (derivative (ftDen Q r ((z 0 : ℝ) : ℂ))).eval (ftPrincipal τ 0) = 0 := by
    rw [hγ0₀]
    exact derivative_eval_eq_zero_of_two_le_rootMultiplicity hP₀ hk₀
  have hEp' : Filter.Tendsto
      (fun δ : ℝ => (derivative (ftDen Q r ((z δ : ℝ) : ℂ))).eval (ftPrincipal τ δ))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds cQ₀) := by
    simpa using hEp₀
  rw [hzero] at hcont
  exact hcQ₀ (tendsto_nhds_unique hEp' hcont)

end ForgacsTran
