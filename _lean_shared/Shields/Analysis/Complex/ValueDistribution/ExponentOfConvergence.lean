/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib.Analysis.Complex.ValueDistribution.LogCounting.Basic

/-!
# The exponent of convergence of a divisor

The exponent of convergence of a sequence of points `zₙ` is the infimum of the exponents `p` for
which `∑ ‖zₙ‖ ^ (-p)` converges.  Here the sequence is presented as a function `D` with locally
finite support, counting each point with its multiplicity, so that the series is the unordered sum
`∑ z, D z * ‖z‖ ^ (-p)` over the whole space.  The term at `z = 0` contributes nothing for `p ≠ 0`,
since `‖0‖ ^ (-p) = 0` there.

## Main results

* `Shields.expConvergence` — the exponent of convergence of a function with locally finite support.
* `Shields.logCounting_le_const_mul_rpow` — if the series converges at `p > 0`, the logarithmic
  counting function of `D` is bounded by a constant multiple of `r ^ p`.
* `Shields.summable_rpow_of_summable_zero` — convergence at the exponent `0` forces finite support,
  hence convergence at every exponent.

## Tags

exponent of convergence, counting function, Nevanlinna theory
-/

open Filter Function Metric Real Set
open scoped ENNReal NNReal

namespace Shields

variable {E : Type*} [NormedAddCommGroup E]

/--
The exponent of convergence of a function `D` with locally finite support: the infimum of the
nonnegative exponents `p` for which `∑ z, D z * ‖z‖ ^ (-p)` converges.  The infimum of the empty
set is `⊤`.
-/
noncomputable def expConvergence (D : locallyFinsupp E ℤ) : ℝ≥0∞ :=
  ⨅ p ∈ {p : NNReal | Summable fun z : E ↦ (D z : ℝ) * ‖z‖ ^ (-(p : ℝ))}, (p : ℝ≥0∞)

/--
The exponent of convergence is at most any exponent at which the series converges.
-/
theorem expConvergence_le {D : locallyFinsupp E ℤ} {p : NNReal}
    (h : Summable fun z : E ↦ (D z : ℝ) * ‖z‖ ^ (-(p : ℝ))) :
    expConvergence D ≤ p :=
  iInf₂_le p h

/--
Nonnegativity of the summands defining the exponent of convergence.
-/
theorem summand_nonneg {D : locallyFinsupp E ℤ} (hD : 0 ≤ D) (p : ℝ) (z : E) :
    0 ≤ (D z : ℝ) * ‖z‖ ^ (-p) := by
  have hDz : (0 : ℤ) ≤ D z := by simpa using (locallyFinsuppWithin.le_def.1 hD) z
  have : (0 : ℝ) ≤ (D z : ℝ) := by exact_mod_cast hDz
  positivity

/--
For `r ≥ 1` and `p > 0`, the logarithm is bounded by `r ^ p / p`.
-/
theorem log_le_rpow_div {p r : ℝ} (hp : 0 < p) (hr : 1 ≤ r) : log r ≤ r ^ p / p := by
  have hr0 : (0 : ℝ) < r := lt_of_lt_of_le zero_lt_one hr
  have h1 : log (r ^ p) ≤ r ^ p - 1 := Real.log_le_sub_one_of_pos (by positivity)
  rw [Real.log_rpow hr0] at h1
  rw [le_div_iff₀ hp]
  nlinarith

/--
If the series `∑ z, D z * ‖z‖ ^ (-p)` converges for some `p > 0`, then the logarithmic counting
function of the nonnegative divisor `D` grows at most like `r ^ p`.
-/
theorem logCounting_le_const_mul_rpow [ProperSpace E] {D : locallyFinsupp E ℤ} (hD : 0 ≤ D)
    {p : ℝ} (hp : 0 < p)
    (hsum : Summable fun z : E ↦ (D z : ℝ) * ‖z‖ ^ (-p)) {r : ℝ} (hr : 1 ≤ r) :
    D.logCounting r ≤ ((∑' z : E, (D z : ℝ) * ‖z‖ ^ (-p)) + (D 0 : ℝ)) / p * r ^ p := by
  have hr0 : (0 : ℝ) < r := lt_of_lt_of_le zero_lt_one hr
  have hD0 : (0 : ℝ) ≤ (D 0 : ℝ) := by
    have : (0 : ℤ) ≤ D 0 := by simpa using (locallyFinsuppWithin.le_def.1 hD) 0
    exact_mod_cast this
  -- Termwise bound `log (r / ‖z‖) ≤ r ^ p / p * ‖z‖ ^ (-p)`, valid also at the excluded points.
  have key : ∀ z : E, ((D.toClosedBall r) z : ℝ) * log (r * ‖z‖⁻¹)
      ≤ r ^ p / p * ((D z : ℝ) * ‖z‖ ^ (-p)) := by
    intro z
    have hnn := summand_nonneg hD p z
    have hcoef : (0 : ℝ) ≤ r ^ p / p := by positivity
    rcases eq_or_ne z 0 with rfl | hz
    · have h0 : (0 : ℝ) ^ (-p) = 0 := Real.zero_rpow (neg_ne_zero.2 hp.ne')
      simp [h0]
    have hznorm : (0 : ℝ) < ‖z‖ := norm_pos_iff.2 hz
    have hDz : (0 : ℝ) ≤ (D z : ℝ) := by
      have : (0 : ℤ) ≤ D z := by simpa using (locallyFinsuppWithin.le_def.1 hD) z
      exact_mod_cast this
    by_cases hmem : z ∈ closedBall (0 : E) |r|
    · rw [locallyFinsuppWithin.toClosedBall_eval_within D hmem]
      have h2 : (r * ‖z‖⁻¹) ^ p = r ^ p * ‖z‖ ^ (-p) := by
        rw [Real.mul_rpow hr0.le (inv_nonneg.2 (norm_nonneg z)), Real.inv_rpow (norm_nonneg z),
          Real.rpow_neg (norm_nonneg z)]
      have h1 : log ((r * ‖z‖⁻¹) ^ p) ≤ (r * ‖z‖⁻¹) ^ p - 1 :=
        Real.log_le_sub_one_of_pos (by positivity)
      rw [Real.log_rpow (by positivity), h2] at h1
      have hlog : log (r * ‖z‖⁻¹) ≤ r ^ p / p * ‖z‖ ^ (-p) := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hp]
        nlinarith
      calc ((D z : ℝ)) * log (r * ‖z‖⁻¹) ≤ (D z : ℝ) * (r ^ p / p * ‖z‖ ^ (-p)) :=
            mul_le_mul_of_nonneg_left hlog hDz
        _ = r ^ p / p * ((D z : ℝ) * ‖z‖ ^ (-p)) := by ring
    · have : (D.toClosedBall r) z = 0 := by
        by_contra hne
        exact hmem (locallyFinsuppWithin.toClosedBall_support_subset_closedBall D hne)
      rw [this]
      simpa using mul_nonneg hcoef hnn
  -- The sum over the closed ball is finite, and is bounded by the total sum.
  have hfinsupp :
      (Function.support fun z : E ↦ ((D.toClosedBall r) z : ℝ) * log (r * ‖z‖⁻¹)).Finite := by
    refine Set.Finite.subset ((D.toClosedBall r).finiteSupport (isCompact_closedBall 0 |r|)) ?_
    intro z hz
    simp only [Function.mem_support, ne_eq] at hz ⊢
    intro hcon
    rw [hcon] at hz
    simp at hz
  have hsum1 : ∑ᶠ z : E, ((D.toClosedBall r) z : ℝ) * log (r * ‖z‖⁻¹)
      ≤ r ^ p / p * ∑' z : E, (D z : ℝ) * ‖z‖ ^ (-p) := by
    rw [finsum_eq_sum_of_support_subset _ (s := hfinsupp.toFinset) (by simp)]
    calc ∑ z ∈ hfinsupp.toFinset, ((D.toClosedBall r) z : ℝ) * log (r * ‖z‖⁻¹)
        ≤ ∑ z ∈ hfinsupp.toFinset, r ^ p / p * ((D z : ℝ) * ‖z‖ ^ (-p)) :=
          Finset.sum_le_sum fun z _ ↦ key z
      _ = r ^ p / p * ∑ z ∈ hfinsupp.toFinset, ((D z : ℝ) * ‖z‖ ^ (-p)) := by
          rw [Finset.mul_sum]
      _ ≤ r ^ p / p * ∑' z : E, (D z : ℝ) * ‖z‖ ^ (-p) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact Summable.sum_le_tsum _ (fun z _ ↦ summand_nonneg hD p z) hsum
  have hsum2 : (D 0 : ℝ) * log r ≤ (D 0 : ℝ) * (r ^ p / p) :=
    mul_le_mul_of_nonneg_left (log_le_rpow_div hp hr) hD0
  have hunfold : D.logCounting r
      = (∑ᶠ z : E, ((D.toClosedBall r) z : ℝ) * log (r * ‖z‖⁻¹)) + (D 0 : ℝ) * log r := by
    simp only [locallyFinsuppWithin.logCounting, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  rw [hunfold, add_div, add_mul]
  have e1 : (∑' z : E, (D z : ℝ) * ‖z‖ ^ (-p)) / p * r ^ p
      = r ^ p / p * ∑' z : E, (D z : ℝ) * ‖z‖ ^ (-p) := by ring
  have e2 : (D 0 : ℝ) / p * r ^ p = (D 0 : ℝ) * (r ^ p / p) := by ring
  rw [e1, e2]
  exact add_le_add hsum1 hsum2

/--
A nonnegative function with locally finite support whose series converges at the exponent `0` has
finite support, hence its series converges at every exponent.
-/
theorem summable_rpow_of_summable_zero {D : locallyFinsupp E ℤ} (hD : 0 ≤ D)
    (h : Summable fun z : E ↦ (D z : ℝ) * ‖z‖ ^ (-(0 : ℝ))) (p : ℝ) :
    Summable fun z : E ↦ (D z : ℝ) * ‖z‖ ^ (-p) := by
  have h' : Summable fun z : E ↦ (D z : ℝ) := by simpa using h
  have hev : (fun z : E ↦ (D z : ℝ)) ⁻¹' (Metric.ball (0 : ℝ) 1) ∈ Filter.cofinite :=
    h'.tendsto_cofinite_zero (Metric.ball_mem_nhds 0 one_pos)
  have hcofin : ((fun z : E ↦ (D z : ℝ)) ⁻¹' (Metric.ball (0 : ℝ) 1))ᶜ.Finite :=
    Filter.mem_cofinite.1 hev
  refine summable_of_hasFiniteSupport (Set.Finite.subset hcofin ?_)
  intro z hz
  simp only [Function.mem_support, ne_eq, mul_eq_zero, not_or] at hz
  have hDz : (0 : ℤ) ≤ D z := by simpa using (locallyFinsuppWithin.le_def.1 hD) z
  have hne : D z ≠ 0 := by
    intro hcon
    exact hz.1 (by exact_mod_cast congrArg (Int.cast : ℤ → ℝ) hcon)
  have h1 : (1 : ℝ) ≤ (D z : ℝ) := by
    have : (1 : ℤ) ≤ D z := by omega
    exact_mod_cast this
  simp only [Set.mem_compl_iff, Set.mem_preimage, Metric.mem_ball, Real.dist_eq, sub_zero, not_lt]
  rw [abs_of_nonneg (by linarith)]
  exact h1

end Shields
