/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.Complex.RemovableSingularity

/-!
# Newton's interpolation form with an analytic remainder

An analytic function splits, at any finite list of nodes, into its Newton interpolating
polynomial plus the node product times an analytic remainder:

\[ f(z) = \sum_{j<k} d_j \prod_{i<j}(z - a_i) + \Bigl(\prod_{i<k}(z - a_i)\Bigr) q(z), \]

with `q` analytic on the same open set.  **No hypothesis separates the nodes**: they may
coincide in any pattern, in which case the interpolation is Hermite's rather than Lagrange's
and the coefficients are the confluent divided differences.  That is the point of building the
identity from `dslope`, which is the divided difference with the coincident case filled in:
`(b - a) • dslope f a b = f b - f a` holds for every `a` and `b`, with no side condition.

## Main results

* `Shields.exists_newton_form`: the decomposition.
* `Shields.exists_newton_form_div`: its division form, `f/∏(z - a_i)` as a proper rational part
  plus an analytic one — the principal-part decomposition at a cluster of poles.

## Implementation notes

The induction peels the **last** node off the remainder rather than the first off `f`, which
keeps the products indexed by `Finset.range j` throughout and needs no reindexing.  Analyticity
of `dslope f a` on an open set containing `a` is `Complex.differentiableOn_dslope`.

## Tags

Newton interpolation, Hermite interpolation, divided difference, dslope, analytic, principal part
-/

open Set

namespace Shields

/-- **Newton's form with an analytic remainder.**  At nodes `a 0, …, a (k-1)` lying in an open
set `U` on which `f` is analytic, `f` is its Newton interpolating polynomial plus the node
product times an analytic remainder.  Repeated nodes are allowed and need no separate
treatment. -/
theorem exists_newton_form {U : Set ℂ} (hU : IsOpen U) (a : ℕ → ℂ) (ha : ∀ i, a i ∈ U) :
    ∀ (k : ℕ) {f : ℂ → ℂ}, AnalyticOnNhd ℂ f U →
      ∃ (d : ℕ → ℂ) (q : ℂ → ℂ), AnalyticOnNhd ℂ q U ∧
        ∀ z, f z = (∑ j ∈ Finset.range k, d j * ∏ i ∈ Finset.range j, (z - a i))
          + (∏ i ∈ Finset.range k, (z - a i)) * q z := by
  intro k
  induction k with
  | zero => intro f hf; exact ⟨fun _ => 0, f, hf, fun z => by simp⟩
  | succ k ih =>
    intro f hf; obtain ⟨d, q, hq, hrep⟩ := ih hf
    -- peel the last node off the remainder
    have hdq := ((Complex.differentiableOn_dslope (hU.mem_nhds (ha k))).mpr
      hq.differentiableOn).analyticOnNhd hU
    refine ⟨Function.update d k (q (a k)), dslope q (a k), hdq, fun z => ?_⟩
    have hsplit : q z = q (a k) + (z - a k) * dslope q (a k) z := by
      rw [← smul_eq_mul, sub_smul_dslope]; ring
    have hsum : ∑ j ∈ Finset.range (k + 1),
          Function.update d k (q (a k)) j * ∏ i ∈ Finset.range j, (z - a i)
        = (∑ j ∈ Finset.range k, d j * ∏ i ∈ Finset.range j, (z - a i))
          + q (a k) * ∏ i ∈ Finset.range k, (z - a i) := by
      rw [Finset.sum_range_succ, Function.update_self]
      congr 1
      exact Finset.sum_congr rfl fun j hj => by
        rw [Function.update_of_ne (Finset.mem_range.1 hj).ne]
    rw [hsum, Finset.prod_range_succ, hrep z, hsplit]; ring

/-- **The principal-part decomposition at a cluster.**  Dividing the Newton form by the node
product writes `f/∏(z - a_i)` as a sum of proper rational terms — the `j`-th carrying the
factors from `j` on — plus an analytic function.  Repeated nodes are allowed, so this is the
decomposition at a pole of any multiplicity pattern. -/
theorem exists_newton_form_div {U : Set ℂ} (hU : IsOpen U) (a : ℕ → ℂ) (ha : ∀ i, a i ∈ U)
    (k : ℕ) {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f U) :
    ∃ (d : ℕ → ℂ) (q : ℂ → ℂ), AnalyticOnNhd ℂ q U ∧
      ∀ z, (∀ i ∈ Finset.range k, z ≠ a i) →
        f z / ∏ i ∈ Finset.range k, (z - a i)
          = (∑ j ∈ Finset.range k, d j / ∏ i ∈ Finset.Ico j k, (z - a i)) + q z := by
  obtain ⟨d, q, hq, hrep⟩ := exists_newton_form hU a ha k hf
  refine ⟨d, q, hq, fun z hz => ?_⟩
  have hne : ∀ j ≤ k, (∏ i ∈ Finset.range j, (z - a i)) ≠ 0 := by
    intro j hj
    refine Finset.prod_ne_zero_iff.mpr fun i hi => sub_ne_zero.mpr ?_
    exact hz i (Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hi) hj))
  have hprodk : (∏ i ∈ Finset.range k, (z - a i)) ≠ 0 := hne k le_rfl
  rw [hrep z, add_div]
  congr 1
  · rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjk : j ≤ k := (Finset.mem_range.mp hj).le
    have hsplit : (∏ i ∈ Finset.range k, (z - a i))
        = (∏ i ∈ Finset.range j, (z - a i)) * ∏ i ∈ Finset.Ico j k, (z - a i) := by
      rw [← Finset.prod_range_mul_prod_Ico _ hjk]
    rw [hsplit]
    have hj0 : (∏ i ∈ Finset.range j, (z - a i)) ≠ 0 := hne j hjk
    field_simp
  · field_simp


/-! ### Axiom footprint -/

/-- info: 'Shields.exists_newton_form_div' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_newton_form_div

end Shields
