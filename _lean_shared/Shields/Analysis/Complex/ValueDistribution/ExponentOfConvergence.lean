/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib.Analysis.Complex.ValueDistribution.LogCounting.Basic
import Mathlib.Topology.LocallyFinsupp

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
* `Shields.locallyFinsuppWithin_apply_intCast_nonneg` — a nonnegative function with locally finite
  support takes values whose image in an ordered ring is nonnegative.

## Tags

exponent of convergence, counting function, Nevanlinna theory
-/

open Filter Function Metric Real Set
open scoped ENNReal NNReal

namespace Shields

/--
A nonnegative integer-valued function with locally finite support takes values whose image in an
ordered ring is nonnegative.  The order on `Function.locallyFinsuppWithin U ℤ` is the pointwise
one, so this is the cast of that; the cast is where a real-valued estimate consumes the fact.
-/
theorem locallyFinsuppWithin_apply_intCast_nonneg {X : Type*} [TopologicalSpace X] {U : Set X}
    {R : Type*} [Ring R] [PartialOrder R] [IsOrderedRing R]
    {D : Function.locallyFinsuppWithin U ℤ} (hD : 0 ≤ D) (x : X) :
    (0 : R) ≤ (D x : R) :=
  Int.cast_nonneg (hD x)

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
  have : (0 : ℝ) ≤ (D z : ℝ) := locallyFinsuppWithin_apply_intCast_nonneg hD z
  positivity

/--
**The termwise Jensen bound.**  A point of the divisor contributes to `logCounting r` at most
`r ^ p / p` times what it contributes to `∑ z, D z * ‖z‖ ^ (-p)`.

The points outside the ball of radius `r` are carried as well, contributing nothing on the left,
so the bound may be summed over the whole space rather than over the ball.
-/
theorem logTerm_le_rpow_div_mul_summand {D : locallyFinsupp E ℤ} (hD : 0 ≤ D)
    {p : ℝ} (hp : 0 < p) {r : ℝ} (hr : 0 < r) (z : E) :
    ((D.toClosedBall r) z : ℝ) * log (r * ‖z‖⁻¹)
      ≤ r ^ p / p * ((D z : ℝ) * ‖z‖ ^ (-p)) := by
  have hnn := summand_nonneg hD p z
  have hcoef : (0 : ℝ) ≤ r ^ p / p := by positivity
  rcases eq_or_ne z 0 with rfl | hz
  · simp [Real.zero_rpow (neg_ne_zero.2 hp.ne')]
  have hznorm : (0 : ℝ) < ‖z‖ := norm_pos_iff.2 hz
  have hDz : (0 : ℝ) ≤ (D z : ℝ) := locallyFinsuppWithin_apply_intCast_nonneg hD z
  by_cases hmem : z ∈ closedBall (0 : E) |r|
  · rw [locallyFinsuppWithin.toClosedBall_eval_within D hmem]
    have hzr : ‖z‖ ≤ r := by
      have := mem_closedBall_zero_iff.1 hmem
      rwa [abs_of_pos hr] at this
    have h2 : (r * ‖z‖⁻¹) ^ p = r ^ p * ‖z‖ ^ (-p) := by
      rw [Real.mul_rpow hr.le (inv_nonneg.2 (norm_nonneg z)), Real.inv_rpow (norm_nonneg z),
        Real.rpow_neg (norm_nonneg z)]
    have hlog : log (r * ‖z‖⁻¹) ≤ r ^ p / p * ‖z‖ ^ (-p) := by
      have hge : (1 : ℝ) ≤ r * ‖z‖⁻¹ := by
        rw [← div_eq_mul_inv]; exact (one_le_div hznorm).2 hzr
      have h1 := Real.log_le_rpow_div (zero_le_one.trans hge) hp
      rw [h2] at h1
      calc log (r * ‖z‖⁻¹) ≤ r ^ p * ‖z‖ ^ (-p) / p := h1
        _ = r ^ p / p * ‖z‖ ^ (-p) := by ring
    calc ((D z : ℝ)) * log (r * ‖z‖⁻¹) ≤ (D z : ℝ) * (r ^ p / p * ‖z‖ ^ (-p)) :=
          mul_le_mul_of_nonneg_left hlog hDz
      _ = r ^ p / p * ((D z : ℝ) * ‖z‖ ^ (-p)) := by ring
  · rw [show (D.toClosedBall r) z = 0 from by
      by_contra hne
      exact hmem (locallyFinsuppWithin.toClosedBall_support_subset_closedBall D hne)]
    simpa using mul_nonneg hcoef hnn

/--
If the series `∑ z, D z * ‖z‖ ^ (-p)` converges for some `p > 0`, then the logarithmic counting
function of the nonnegative divisor `D` grows at most like `r ^ p`.
-/
theorem logCounting_le_const_mul_rpow [ProperSpace E] {D : locallyFinsupp E ℤ} (hD : 0 ≤ D)
    {p : ℝ} (hp : 0 < p)
    (hsum : Summable fun z : E ↦ (D z : ℝ) * ‖z‖ ^ (-p)) {r : ℝ} (hr : 1 ≤ r) :
    D.logCounting r ≤ ((∑' z : E, (D z : ℝ) * ‖z‖ ^ (-p)) + (D 0 : ℝ)) / p * r ^ p := by
  have hr0 : (0 : ℝ) < r := lt_of_lt_of_le zero_lt_one hr
  have hD0 : (0 : ℝ) ≤ (D 0 : ℝ) := locallyFinsuppWithin_apply_intCast_nonneg hD 0
  have key := logTerm_le_rpow_div_mul_summand hD hp hr0
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
    mul_le_mul_of_nonneg_left (Real.log_le_rpow_div (zero_le_one.trans hr) hp) hD0
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
**A summable real family that is at least `1` wherever it is nonzero has finite support.**

Summability sends the family to `0` along the cofinite filter, so all but finitely many values lie
in the ball of radius `1` about `0`; the lower bound leaves those values no room to be nonzero.
-/
theorem finite_support_of_summable_of_forall_one_le {α : Type*} {f : α → ℝ} (hsum : Summable f)
    (h1 : ∀ a, f a ≠ 0 → 1 ≤ f a) :
    (Function.support f).Finite := by
  have hcofin : (f ⁻¹' Metric.ball (0 : ℝ) 1)ᶜ.Finite :=
    Filter.mem_cofinite.1 (hsum.tendsto_cofinite_zero (Metric.ball_mem_nhds 0 one_pos))
  refine hcofin.subset fun a ha ↦ ?_
  have hfa := h1 a ha
  simp only [Set.mem_compl_iff, Set.mem_preimage, Metric.mem_ball, Real.dist_eq, sub_zero, not_lt]
  rw [abs_of_nonneg (by linarith)]
  exact hfa

/--
A nonnegative function with locally finite support whose series converges at the exponent `0` has
finite support, hence its series converges at every exponent.
-/
theorem summable_rpow_of_summable_zero {D : locallyFinsupp E ℤ} (hD : 0 ≤ D)
    (h : Summable fun z : E ↦ (D z : ℝ) * ‖z‖ ^ (-(0 : ℝ))) (p : ℝ) :
    Summable fun z : E ↦ (D z : ℝ) * ‖z‖ ^ (-p) := by
  have h' : Summable fun z : E ↦ (D z : ℝ) := by simpa using h
  have h1 : ∀ z : E, (D z : ℝ) ≠ 0 → 1 ≤ (D z : ℝ) := fun z hz ↦ by
    have hDz : (0 : ℤ) ≤ D z := hD z
    have hne : D z ≠ 0 := fun hcon ↦ hz (by exact_mod_cast congrArg (Int.cast : ℤ → ℝ) hcon)
    exact_mod_cast (by omega : (1 : ℤ) ≤ D z)
  refine summable_of_hasFiniteSupport
    ((finite_support_of_summable_of_forall_one_le h' h1).subset fun z hz ↦ ?_)
  simp only [Function.mem_support, ne_eq, mul_eq_zero, not_or] at hz ⊢
  exact hz.1


/-! ### Axiom footprint -/

/-- info: 'Shields.expConvergence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms expConvergence

/-- info: 'Shields.logCounting_le_const_mul_rpow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms logCounting_le_const_mul_rpow

/-- info: 'Shields.summable_rpow_of_summable_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms summable_rpow_of_summable_zero

end Shields
