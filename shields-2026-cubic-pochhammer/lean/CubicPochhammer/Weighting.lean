/-
# One-sign-change weighting principle

Formalizes `shields-2026-cubic-pochhammer.tex`, §3 «Two monotonicity
lemmas» (`sec:monotonicity-lemmas`), `lem:weighting`:

  a nondecreasing nonnegative weight sequence carries a finite sum through a
  single sign change.  If `0 ≤ w₀ ≤ ⋯ ≤ w_{n-1}`, the reals `A₀,…,A_{n-1}` are
  nonpositive up to an index `q` and nonnegative after it, and `∑ Aₖ ≥ 0`, then
  `∑ wₖ Aₖ ≥ 0`.

This is the transfer principle that carries the constant-weight positivity
certificate of §4 to the log-concave–weighted kernel (`thm:kernel`).

Sorry-free, no project axioms.
-/
import Mathlib.Tactic

open scoped BigOperators

namespace CubicPochhammer

/-- **One-sign-change weighting** (`lem:weighting`).  With `w` nondecreasing and
nonnegative on `range n`, `A` nonpositive on `{k ≤ q}` and nonnegative on
`{q < k < n}`, and `∑ Aₖ ≥ 0`, the weighted sum `∑ wₖ Aₖ` is nonnegative.

The proof compares against the pivot weight `c = w q`: the surplus
`∑ (wₖ - c) Aₖ` is termwise nonnegative (both factors share a sign on each side
of `q`), and `c · ∑ Aₖ ≥ 0`. -/
theorem sum_weighted_nonneg (w A : ℕ → ℝ) (n : ℕ)
    (hw_mono : ∀ i j, i ≤ j → j < n → w i ≤ w j)
    (hw_nonneg : ∀ k, k < n → 0 ≤ w k)
    (q : ℕ) (hq : q < n)
    (hle : ∀ k, k ≤ q → A k ≤ 0)
    (hge : ∀ k, q < k → k < n → 0 ≤ A k)
    (hsum : 0 ≤ ∑ k ∈ Finset.range n, A k) :
    0 ≤ ∑ k ∈ Finset.range n, w k * A k := by
  set c := w q with hc
  have hcnn : 0 ≤ c := hw_nonneg q hq
  have key : ∑ k ∈ Finset.range n, w k * A k
      = (∑ k ∈ Finset.range n, (w k - c) * A k)
        + c * ∑ k ∈ Finset.range n, A k := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun k _ => by ring)
  rw [key]
  refine add_nonneg (Finset.sum_nonneg ?_) (mul_nonneg hcnn hsum)
  intro k hk
  rw [Finset.mem_range] at hk
  rcases le_or_gt k q with hkq | hkq
  · exact mul_nonneg_of_nonpos_of_nonpos (by linarith [hw_mono k q hkq hq]) (hle k hkq)
  · exact mul_nonneg (by linarith [hw_mono q k hkq.le hk]) (hge k hkq hk)

/-- Strict variant.  Under the hypotheses of `sum_weighted_nonneg`, if in
addition the pivot weight `c = w q` is positive, then the weighted sum inherits
strictness from `∑ Aₖ > 0`. -/
theorem sum_weighted_pos_of_pivot_pos (w A : ℕ → ℝ) (n : ℕ)
    (hw_mono : ∀ i j, i ≤ j → j < n → w i ≤ w j)
    (_hw_nonneg : ∀ k, k < n → 0 ≤ w k)
    (q : ℕ) (hq : q < n)
    (hle : ∀ k, k ≤ q → A k ≤ 0)
    (hge : ∀ k, q < k → k < n → 0 ≤ A k)
    (hpivot : 0 < w q)
    (hsum : 0 < ∑ k ∈ Finset.range n, A k) :
    0 < ∑ k ∈ Finset.range n, w k * A k := by
  set c := w q with hc
  have key : ∑ k ∈ Finset.range n, w k * A k
      = (∑ k ∈ Finset.range n, (w k - c) * A k)
        + c * ∑ k ∈ Finset.range n, A k := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun k _ => by ring)
  rw [key]
  refine add_pos_of_nonneg_of_pos (Finset.sum_nonneg ?_) (mul_pos hpivot hsum)
  intro k hk
  rw [Finset.mem_range] at hk
  rcases le_or_gt k q with hkq | hkq
  · exact mul_nonneg_of_nonpos_of_nonpos (by linarith [hw_mono k q hkq hq]) (hle k hkq)
  · exact mul_nonneg (by linarith [hw_mono q k hkq.le hk]) (hge k hkq hk)

end CubicPochhammer
