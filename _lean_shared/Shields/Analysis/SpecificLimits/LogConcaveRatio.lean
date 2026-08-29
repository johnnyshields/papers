/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Algebra.BigOperators.Field

/-!
# The ratio limit of a positive log-concave sequence, and the recursions it satisfies

A sequence `c : ℕ → ℝ` that is positive and log-concave has a nonincreasing ratio sequence
`k ↦ c (k + 1) / c k`, which is bounded below by zero and therefore converges.  The limit `L`
is not an accident of the sequence: if `c` also satisfies a linear recursion of order `n`, then
dividing the recursion by `c k` and passing to the limit shows `L` is a root of the recursion's
characteristic polynomial.

This is the real-variable substitute for Pringsheim's theorem in the situation where the
generating function is rational.  Pringsheim locates a singularity of a nonnegative power series
at its radius of convergence, and a pole of a rational generating function is a root of the
denominator; the argument here reaches the same root with no complex analysis, using log-concavity
in place of the radius of convergence.  Log-concavity is what buys the *monotonicity* of the ratio,
and it is a hypothesis one gets for free wherever the coefficient sequence carries a total
nonnegativity assumption, since `c k * c (k + 2) ≤ c (k + 1) ^ 2` is a `2 × 2` minor.

Strict positivity is not a convenience of the proof, and it is the hypothesis carrying the
weight: `1, 1, 0, 0, 1, 1, 0, 0, …` is nonnegative, satisfies
`c (k + 3) = c (k + 2) - c (k + 1) + c k`, and *is* log-concave, every one of its
`c k * c (k + 2) ≤ c (k + 1) ^ 2` holding because one factor on the left vanishes.  Its ratios
alternate between `1` and `0` and never settle, and its characteristic polynomial
`z³ - z² + z - 1 = (z - 1) (z² + 1)` carries a nonreal pair.  Log-concavity alone therefore does
not give the conclusion; it gives monotonicity of the ratio only where the ratio is defined.

## Main results

* `Shields.antitone_ratio_of_logConcave` — the ratio sequence of a positive log-concave sequence
  is antitone.
* `Shields.exists_tendsto_ratio_of_logConcave` — hence it converges, to a nonnegative limit.
* `Shields.tendsto_ratio_pow` — the `j`-step ratio `c (k + j) / c k` converges to `L ^ j`,
  by telescoping the one-step ratio.
* `Shields.pow_eq_sum_of_tendsto_ratio` — the limit of the one-step ratio of a positive sequence
  satisfying `c (k + n) = ∑ i < n, a i * c (k + i)` is a root of `z ^ n - ∑ i < n, a i * z ^ i`.
  No sign hypothesis is needed here; only the existence of the ratio limit.
* `Shields.exists_nonneg_root_of_logConcave_rec` — the two combined: a positive log-concave
  solution of a linear recursion forces that recursion's characteristic polynomial to have a
  nonnegative real root.

## Implementation notes

`pow_eq_sum_of_tendsto_ratio` needs no lower bound on `L`.  When `L = 0` the identity reads
`0 = a 0` for `n ≥ 1`, which is genuinely what the hypotheses give: every `c (k + i) / c k` with
`i ≥ 1` is a product of `i` factors each tending to zero, so the constant term of the recursion
has to vanish for the divided recursion to survive in the limit.

## References

* [Pringsheim, *Über Functionen, welche in gewissen Punkten endliche Differentialquotienten
  besitzen*][Pringsheim1894] for the classical singularity statement this replaces.

## Papers depending on this file

* `zero-reconstruction-edrei` — the reciprocal of a totally nonnegative Toeplitz symbol.

## Tags

log-concave, ratio limit, linear recurrence, Pringsheim
-/

namespace Shields

open Filter Topology

variable {c : ℕ → ℝ}

/-- The ratio sequence of a positive log-concave sequence is antitone: log-concavity
`c k * c (k + 2) ≤ c (k + 1) ^ 2` is exactly `c (k + 2) / c (k + 1) ≤ c (k + 1) / c k`
after clearing the positive denominators. -/
theorem antitone_ratio_of_logConcave (hpos : ∀ k, 0 < c k)
    (hlc : ∀ k, c k * c (k + 2) ≤ c (k + 1) * c (k + 1)) :
    Antitone fun k => c (k + 1) / c k := by
  refine antitone_nat_of_succ_le fun k => ?_
  rw [div_le_div_iff₀ (hpos (k + 1)) (hpos k), mul_comm]
  exact hlc k

/-- A positive log-concave sequence has a convergent ratio sequence, with a nonnegative limit.
The ratio is antitone by `antitone_ratio_of_logConcave` and bounded below by zero. -/
theorem exists_tendsto_ratio_of_logConcave (hpos : ∀ k, 0 < c k)
    (hlc : ∀ k, c k * c (k + 2) ≤ c (k + 1) * c (k + 1)) :
    ∃ L : ℝ, 0 ≤ L ∧ Tendsto (fun k => c (k + 1) / c k) atTop (𝓝 L) := by
  have hratio : ∀ k, 0 ≤ c (k + 1) / c k := fun k =>
    le_of_lt (div_pos (hpos (k + 1)) (hpos k))
  have hbdd : BddBelow (Set.range fun k => c (k + 1) / c k) := by
    refine ⟨0, ?_⟩
    rintro x ⟨k, rfl⟩
    exact hratio k
  exact ⟨⨅ k, c (k + 1) / c k, le_ciInf hratio,
    tendsto_atTop_ciInf (antitone_ratio_of_logConcave hpos hlc) hbdd⟩

/-- The `j`-step ratio converges to the `j`-th power of the one-step limit.  The step
`c (k + j + 1) / c k = (c (k + j + 1) / c (k + j)) * (c (k + j) / c k)` telescopes, and the
first factor is the one-step ratio composed with a shift. -/
theorem tendsto_ratio_pow {L : ℝ} (hpos : ∀ k, 0 < c k)
    (hL : Tendsto (fun k => c (k + 1) / c k) atTop (𝓝 L)) (j : ℕ) :
    Tendsto (fun k => c (k + j) / c k) atTop (𝓝 (L ^ j)) := by
  induction j with
  | zero =>
      simp only [Nat.add_zero, pow_zero]
      exact Tendsto.congr (fun k => (div_self (ne_of_gt (hpos k))).symm) tendsto_const_nhds
  | succ j ih =>
      have hshift : Tendsto (fun k => c (k + j + 1) / c (k + j)) atTop (𝓝 L) :=
        hL.comp (tendsto_add_atTop_nat j)
      have hmul := ih.mul hshift
      rw [pow_succ]
      refine hmul.congr fun k => ?_
      have hk : c (k + j) ≠ 0 := ne_of_gt (hpos (k + j))
      field_simp
      rw [Nat.add_assoc]

/-- **The ratio limit is a root of the characteristic polynomial.**  If a positive sequence
satisfies `c (k + n) = ∑ i < n, a i * c (k + i)` and its one-step ratio tends to `L`, then
`L ^ n = ∑ i < n, a i * L ^ i`.  Divide the recursion by `c k` and pass to the limit. -/
theorem pow_eq_sum_of_tendsto_ratio {L : ℝ} {n : ℕ} {a : ℕ → ℝ} (hpos : ∀ k, 0 < c k)
    (hL : Tendsto (fun k => c (k + 1) / c k) atTop (𝓝 L))
    (hrec : ∀ k, c (k + n) = ∑ i ∈ Finset.range n, a i * c (k + i)) :
    L ^ n = ∑ i ∈ Finset.range n, a i * L ^ i := by
  have hnum : Tendsto (fun k => c (k + n) / c k) atTop (𝓝 (L ^ n)) :=
    tendsto_ratio_pow hpos hL n
  have hsum : Tendsto (fun k => ∑ i ∈ Finset.range n, a i * (c (k + i) / c k)) atTop
      (𝓝 (∑ i ∈ Finset.range n, a i * L ^ i)) :=
    tendsto_finsetSum _ fun i _ => (tendsto_ratio_pow hpos hL i).const_mul (a i)
  refine tendsto_nhds_unique hnum (hsum.congr fun k => ?_)
  rw [hrec k, Finset.sum_div]
  exact Finset.sum_congr rfl fun i _ => (mul_div_assoc _ _ _).symm

/-- **A positive log-concave solution of a linear recursion forces a nonnegative real root.**
This is the conclusion Pringsheim's theorem supplies in the classical argument: a coefficient
sequence with enough positivity cannot be generated by a recursion all of whose characteristic
roots are nonreal or negative. -/
theorem exists_nonneg_root_of_logConcave_rec {n : ℕ} {a : ℕ → ℝ} (hpos : ∀ k, 0 < c k)
    (hlc : ∀ k, c k * c (k + 2) ≤ c (k + 1) * c (k + 1))
    (hrec : ∀ k, c (k + n) = ∑ i ∈ Finset.range n, a i * c (k + i)) :
    ∃ L : ℝ, 0 ≤ L ∧ L ^ n = ∑ i ∈ Finset.range n, a i * L ^ i := by
  obtain ⟨L, hL0, hL⟩ := exists_tendsto_ratio_of_logConcave hpos hlc
  exact ⟨L, hL0, pow_eq_sum_of_tendsto_ratio hpos hL hrec⟩


/-! ### Axiom footprint -/

/-- info: 'Shields.exists_nonneg_root_of_logConcave_rec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_nonneg_root_of_logConcave_rec

end Shields
