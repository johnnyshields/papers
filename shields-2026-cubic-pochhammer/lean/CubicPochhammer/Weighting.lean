/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# The weighting principle: summation by parts, the cone, and one sign change

Formalizes `shields-2026-cubic-pochhammer.tex`,
`subsec:insertion-monotone-weights` «Insertion of monotone weights» (inside
`sec:kernel`), `lem:weighting`, in the three parts the paper states it in.

The summation-by-parts identity `eq:abel-weight`,

  `∑_{k=1}^L w_k A_k = ∑_{σ=1}^L (w_σ - w_{σ-1}) T_σ`,   `T_σ = ∑_{k≥σ} A_k`,

with `w_0 = 0`, is `sum_weighted_abel`.  The cone equivalence it identifies —
`∑ w_k A_k ≥ 0` for every nondecreasing nonnegative weight sequence exactly when
every tail `T_σ` is nonnegative — is `sum_weighted_nonneg_iff_tails`; the
backward direction is the identity plus nonnegative increments, and the forward
direction is the witness `w_k = 1_{k≥σ}`, which recovers `T_σ` itself.

The one-sign-change specialization is what `thm:kernel` consumes: if
`A₀,…,A_{n-1}` are nonpositive up to an index `q` and nonnegative after it, and
`∑ Aₖ ≥ 0`, then `∑ wₖ Aₖ ≥ 0` for nondecreasing nonnegative `w`.  Its strict
conclusion appears in the two forms the paper's proof splits into —
`sum_weighted_pos_of_pivot_pos` for a positive pivot weight, and
`sum_weighted_pos` for the statement as the paper gives it, which assumes
nothing about the pivot.  The specialized statements are indexed from `0` over
`Finset.range n`, matching the block index of `Blocks.lean`; the identity and the
cone are indexed from `1` over `Finset.Icc 1 L`, matching the paper.

Sorry-free, no project axioms.

## Main statements

* `sum_weighted_abel` --- the summation-by-parts identity `eq:abel-weight`.
* `sum_weighted_nonneg_iff_tails` --- the cone equivalence: `∑ w_k A_k ≥ 0` for
  every nondecreasing nonnegative weight sequence exactly when every tail is
  nonnegative.
* `sum_weighted_nonneg` --- the one-sign-change specialization `thm:kernel`
  consumes.
* `sum_weighted_pos_of_pivot_pos`, `sum_weighted_pos` --- its two strict forms,
  with and without an assumption on the pivot weight.
* `sum_weighted_eq_pairs` --- the pairing identity `eq:B-def` for an arbitrary
  term family: a symmetrically weighted sum over `Icc 1 (m-1)` collapses onto
  the paired blocks, the partner dropped at the center.
* `sign_change_of_stepDown` --- `lem:block-sign` for an abstract sequence:
  downward propagation of nonpositivity plus a positive last entry gives at most
  one sign change, and it is the hypothesis `sum_weighted_nonneg` wants.

## References

* `shields-2026-cubic-pochhammer.tex`, `subsec:insertion-monotone-weights`
  «Insertion of monotone weights», inside `sec:kernel`: `lem:weighting`,
  `eq:abel-weight`.
-/

open scoped BigOperators

namespace CubicPochhammer

/-! ### Summation by parts and the cone (`eq:abel-weight`) -/

/-- The tail `Icc σ L` is the part of `Icc 1 L` from `σ` on.  Mathlib carries this
for `Ico` (`Finset.Ico_filter_le_of_left_le`) but not for `Icc`. -/
private theorem Icc_filter_le_left {L σ : ℕ} (hσ : 1 ≤ σ) :
    (Finset.Icc 1 L).filter (fun k => σ ≤ k) = Finset.Icc σ L := by
  ext k
  simp only [Finset.mem_filter, Finset.mem_Icc]
  omega

/-- The telescoping the identity runs on: with `w_0 = 0`,
`∑_{σ=1}^k (w_σ - w_{σ-1}) = w_k`. -/
private theorem sum_incr_telescope (w : ℕ → ℝ) (k : ℕ) (hw0 : w 0 = 0) :
    ∑ σ ∈ Finset.Icc 1 k, (w σ - w (σ - 1)) = w k := by
  have hIco : Finset.Icc 1 k = Finset.Ico 1 (k + 1) := rfl
  rw [hIco, Finset.sum_Ico_eq_sum_range]
  have hshift : ∀ i ∈ Finset.range (k + 1 - 1),
      w (1 + i) - w (1 + i - 1) = w (i + 1) - w i := by
    intro i _
    rw [show 1 + i = i + 1 from by omega, show i + 1 - 1 = i from by omega]
  rw [Finset.sum_congr rfl hshift, show k + 1 - 1 = k from by omega,
    Finset.sum_range_sub w k, hw0, sub_zero]

/-- **`eq:abel-weight`**: with `w_0 = 0` and `T_σ = ∑_{k=σ}^L A_k`,
`∑_{k=1}^L w_k A_k = ∑_{σ=1}^L (w_σ - w_{σ-1}) T_σ`.  Swapping the double sum
over `1 ≤ σ ≤ k ≤ L` leaves the telescoping `∑_{σ≤k}(w_σ - w_{σ-1}) = w_k`. -/
theorem sum_weighted_abel (w A : ℕ → ℝ) (L : ℕ) (hw0 : w 0 = 0) :
    ∑ k ∈ Finset.Icc 1 L, w k * A k
      = ∑ σ ∈ Finset.Icc 1 L, (w σ - w (σ - 1)) * ∑ k ∈ Finset.Icc σ L, A k := by
  have hR : ∀ σ ∈ Finset.Icc 1 L,
      (w σ - w (σ - 1)) * ∑ k ∈ Finset.Icc σ L, A k
        = ∑ k ∈ Finset.Icc 1 L, (if σ ≤ k then (w σ - w (σ - 1)) * A k else 0) := by
    intro σ hσ
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hσ
    rw [Finset.mul_sum, ← Finset.sum_filter]
    congr 1
    exact (Icc_filter_le_left h1).symm
  rw [Finset.sum_congr rfl hR, Finset.sum_comm]
  refine Finset.sum_congr rfl fun k hk => ?_
  obtain ⟨hk1, hk2⟩ := Finset.mem_Icc.mp hk
  rw [← Finset.sum_filter]
  have hf : (Finset.Icc 1 L).filter (fun σ => σ ≤ k) = Finset.Icc 1 k := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_Icc]
    omega
  rw [hf, ← Finset.sum_mul, sum_incr_telescope w k hw0]

/-- **The cone equivalence of `lem:weighting`**: `∑ w_k A_k ≥ 0` for every
nondecreasing weight sequence starting at `w_0 = 0` exactly when every tail
`T_σ` is nonnegative.  Backward, the increments in `eq:abel-weight` are
nonnegative; forward, the witness `w_k = 1_{k≥σ}` is such a sequence and its
weighted sum is `T_σ`. -/
theorem sum_weighted_nonneg_iff_tails (A : ℕ → ℝ) (L : ℕ) :
    (∀ w : ℕ → ℝ, w 0 = 0 → (∀ i j, i ≤ j → j ≤ L → w i ≤ w j) →
        0 ≤ ∑ k ∈ Finset.Icc 1 L, w k * A k)
      ↔ ∀ σ, 1 ≤ σ → σ ≤ L → 0 ≤ ∑ k ∈ Finset.Icc σ L, A k := by
  constructor
  · intro h σ hσ1 hσL
    have hind := h (fun k => if σ ≤ k then 1 else 0) (by dsimp only; rw [if_neg (by omega)])
      (fun i j hij _ => by
        dsimp only
        by_cases hi : σ ≤ i
        · rw [if_pos hi, if_pos (by omega)]
        · rw [if_neg hi]; split_ifs <;> norm_num)
    have hval : ∑ k ∈ Finset.Icc 1 L, (if σ ≤ k then (1 : ℝ) else 0) * A k
        = ∑ k ∈ Finset.Icc σ L, A k := by
      have hterms : ∀ k ∈ Finset.Icc 1 L,
          (if σ ≤ k then (1 : ℝ) else 0) * A k = if σ ≤ k then A k else 0 := by
        intro k _; split_ifs <;> ring
      rw [Finset.sum_congr rfl hterms, ← Finset.sum_filter]
      congr 1
      exact Icc_filter_le_left hσ1
    rwa [hval] at hind
  · intro hT w hw0 hmono
    rw [sum_weighted_abel w A L hw0]
    refine Finset.sum_nonneg fun σ hσ => ?_
    obtain ⟨hterms, h2⟩ := Finset.mem_Icc.mp hσ
    exact mul_nonneg (by linarith [hmono (σ - 1) σ (by omega) h2]) (hT σ hterms h2)

/-- The strict half of the cone: if every tail is positive and the weight
sequence is not identically zero — equivalently `w_L > 0`, since `w` is
nondecreasing from `w_0 = 0` — then the weighted sum is positive.  The
increments sum to `w_L > 0`, so one of them is positive. -/
theorem sum_weighted_pos_of_tails_pos (w A : ℕ → ℝ) (L : ℕ) (hw0 : w 0 = 0)
    (hmono : ∀ i j, i ≤ j → j ≤ L → w i ≤ w j)
    (hT : ∀ σ, 1 ≤ σ → σ ≤ L → 0 < ∑ k ∈ Finset.Icc σ L, A k)
    (hwL : 0 < w L) :
    0 < ∑ k ∈ Finset.Icc 1 L, w k * A k := by
  rw [sum_weighted_abel w A L hw0]
  have hincr := sum_incr_telescope w L hw0
  obtain ⟨σ, hσ, hσpos⟩ : ∃ σ ∈ Finset.Icc 1 L, 0 < w σ - w (σ - 1) := by
    by_contra hc
    have hnp : ∀ σ ∈ Finset.Icc 1 L, w σ - w (σ - 1) ≤ 0 := fun σ hσ =>
      not_lt.mp (fun hlt => hc ⟨σ, hσ, hlt⟩)
    have hle := Finset.sum_nonpos hnp
    rw [hincr] at hle
    linarith
  obtain ⟨hσ1, hσL⟩ := Finset.mem_Icc.mp hσ
  refine Finset.sum_pos' (fun τ hτ => ?_) ⟨σ, hσ, ?_⟩
  · obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hτ
    exact mul_nonneg (by linarith [hmono (τ - 1) τ (by omega) h2]) (hT τ h1 h2).le
  · exact mul_pos hσpos (hT σ hσ1 hσL)

/-! ### The one-sign-change specialization -/

/-- The decomposition every clause of `lem:weighting` runs on: comparing against
a constant `c`, the weighted sum splits into the surplus `∑ (wₖ - c) Aₖ` and
`c · ∑ Aₖ`. -/
private theorem sum_weighted_decomp (w A : ℕ → ℝ) (n : ℕ) (c : ℝ) :
    ∑ k ∈ Finset.range n, w k * A k
      = (∑ k ∈ Finset.range n, (w k - c) * A k) + c * ∑ k ∈ Finset.range n, A k := by
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun k _ => by ring

/-- The surplus is termwise nonnegative at the pivot weight `c = w q`: below `q`
both factors are nonpositive, above it both are nonnegative.  Neither branch uses
the sign of `w` itself. -/
private theorem surplus_nonneg (w A : ℕ → ℝ) (n : ℕ)
    (hw_mono : ∀ i j, i ≤ j → j < n → w i ≤ w j)
    (q : ℕ) (hq : q < n)
    (hle : ∀ k, k ≤ q → A k ≤ 0)
    (hge : ∀ k, q < k → k < n → 0 ≤ A k) :
    0 ≤ ∑ k ∈ Finset.range n, (w k - w q) * A k := by
  refine Finset.sum_nonneg fun k hk => ?_
  rw [Finset.mem_range] at hk
  rcases le_or_gt k q with hkq | hkq
  · exact mul_nonneg_of_nonpos_of_nonpos (by linarith [hw_mono k q hkq hq]) (hle k hkq)
  · exact mul_nonneg (by linarith [hw_mono q k hkq.le hk]) (hge k hkq hk)

/-- **One-sign-change weighting** (`lem:weighting`).  With `w` nondecreasing and
nonnegative on `range n`, `A` nonpositive on `{k ≤ q}` and nonnegative on
`{q < k < n}`, and `∑ Aₖ ≥ 0`, the weighted sum `∑ wₖ Aₖ` is nonnegative.

The surplus `∑ (wₖ - w q) Aₖ` is termwise nonnegative and `w q · ∑ Aₖ ≥ 0`. -/
theorem sum_weighted_nonneg (w A : ℕ → ℝ) (n : ℕ)
    (hw_mono : ∀ i j, i ≤ j → j < n → w i ≤ w j)
    (hw_nonneg : ∀ k, k < n → 0 ≤ w k)
    (q : ℕ) (hq : q < n)
    (hle : ∀ k, k ≤ q → A k ≤ 0)
    (hge : ∀ k, q < k → k < n → 0 ≤ A k)
    (hsum : 0 ≤ ∑ k ∈ Finset.range n, A k) :
    0 ≤ ∑ k ∈ Finset.range n, w k * A k := by
  rw [sum_weighted_decomp w A n (w q)]
  exact add_nonneg (surplus_nonneg w A n hw_mono q hq hle hge)
    (mul_nonneg (hw_nonneg q hq) hsum)

/-- Strict variant.  Under the hypotheses of `sum_weighted_nonneg`, if in
addition the pivot weight `w q` is positive, then the weighted sum inherits
strictness from `∑ Aₖ > 0`.  Nonnegativity of `w` is not used: the surplus is
termwise nonnegative whatever the sign of `w`. -/
theorem sum_weighted_pos_of_pivot_pos (w A : ℕ → ℝ) (n : ℕ)
    (hw_mono : ∀ i j, i ≤ j → j < n → w i ≤ w j)
    (q : ℕ) (hq : q < n)
    (hle : ∀ k, k ≤ q → A k ≤ 0)
    (hge : ∀ k, q < k → k < n → 0 ≤ A k)
    (hpivot : 0 < w q)
    (hsum : 0 < ∑ k ∈ Finset.range n, A k) :
    0 < ∑ k ∈ Finset.range n, w k * A k := by
  rw [sum_weighted_decomp w A n (w q)]
  exact add_pos_of_nonneg_of_pos (surplus_nonneg w A n hw_mono q hq hle hge)
    (mul_pos hpivot hsum)

/-- **Strict one-sign-change weighting**, as `lem:weighting` states it: no
hypothesis on the pivot weight.  With `∑ Aₖ > 0` and the final pair
`w_{n-1}, A_{n-1}` both positive, the weighted sum is positive.

This proof splits on the pivot `w q`.  When `w q > 0` this is
`sum_weighted_pos_of_pivot_pos`.  When `w q = 0`, monotonicity forces `wₖ = 0`
for every `k ≤ q`, so the weighted sum is carried entirely by the indices above
`q`, where every term is nonnegative and the last is strictly positive. -/
theorem sum_weighted_pos (w A : ℕ → ℝ) (n : ℕ)
    (hw_mono : ∀ i j, i ≤ j → j < n → w i ≤ w j)
    (hw_nonneg : ∀ k, k < n → 0 ≤ w k)
    (q : ℕ) (hq : q < n)
    (hle : ∀ k, k ≤ q → A k ≤ 0)
    (hge : ∀ k, q < k → k < n → 0 ≤ A k)
    (hsum : 0 < ∑ k ∈ Finset.range n, A k)
    (hw_last : 0 < w (n - 1)) (hA_last : 0 < A (n - 1)) :
    0 < ∑ k ∈ Finset.range n, w k * A k := by
  rcases (hw_nonneg q hq).lt_or_eq with hc | hc
  · exact sum_weighted_pos_of_pivot_pos w A n hw_mono q hq hle hge hc hsum
  · -- `w q = 0`: every weight at or below the pivot vanishes
    have hlast : q < n - 1 := by
      by_contra h
      exact absurd (hle (n - 1) (by omega)) (by linarith)
    refine Finset.sum_pos' (fun k hk => ?_) ⟨n - 1, Finset.mem_range.mpr (by omega), ?_⟩
    · have hk' : k < n := Finset.mem_range.mp hk
      rcases le_or_gt k q with hkq | hkq
      · have : w k = 0 := le_antisymm (by linarith [hw_mono k q hkq hq]) (hw_nonneg k hk')
        rw [this, zero_mul]
      · exact mul_nonneg (hw_nonneg k hk') (hge k hkq hk')
    · exact mul_pos hw_last hA_last

/-! ### The pairing `k ↔ m-k`

The reindexing `sec:kernel` runs before any weight is inserted.  It is stated
here for an arbitrary term family, because `eq:B-def` is used at two
multiplicities and the pairing is the same both times.
-/

private theorem sum_shift (g : ℕ → ℝ) (m : ℕ) :
    ∑ k ∈ Finset.range (m / 2), g (k + 1) = ∑ k ∈ Finset.Icc 1 (m / 2), g k := by
  have hIco : Finset.Icc 1 (m / 2) = Finset.Ico 1 (m / 2 + 1) := rfl
  rw [hIco, Finset.sum_Ico_eq_sum_range, show m / 2 + 1 - 1 = m / 2 from by omega]
  exact Finset.sum_congr rfl fun k _ => by rw [Nat.add_comm]

private theorem sum_high_reindex (g : ℕ → ℝ) {m : ℕ} (hm : 2 ≤ m) :
    ∑ r ∈ Finset.Icc (m / 2 + 1) (m - 1), g r
      = ∑ k ∈ Finset.Icc 1 (m - 1 - m / 2), g (m - k) := by
  refine (Finset.sum_nbij' (fun r => m - r) (fun k => m - k) ?_ ?_ ?_ ?_ ?_).symm
  · intro a ha
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp ha
    simp only [Finset.mem_Icc]; omega
  · intro a ha
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp ha
    simp only [Finset.mem_Icc]; omega
  · intro a ha
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp ha
    dsimp only; omega
  · intro a ha
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp ha
    dsimp only; omega
  · intro a ha
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp ha
    rfl

/-- The sum over `Icc 1 (m-1)` split at the center: the low half, plus the high
half reindexed by `r ↦ m-r`.  The symmetry of `w` is spent exactly here, in
rewriting `w (m-k)` back to `w k` on the reindexed half. -/
private theorem sum_split_halves (w A : ℕ → ℝ) {m : ℕ} (hm : 2 ≤ m)
    (hsym : ∀ r, 1 ≤ r → r ≤ m - 1 → w r = w (m - r)) :
    ∑ r ∈ Finset.Icc 1 (m - 1), w r * A r
      = (∑ k ∈ Finset.Icc 1 (m / 2), w k * A k)
        + ∑ k ∈ Finset.Icc 1 (m - 1 - m / 2), w k * A (m - k) := by
  have hsplit : Finset.Icc 1 (m - 1)
      = Finset.Icc 1 (m / 2) ∪ Finset.Icc (m / 2 + 1) (m - 1) := by
    ext x; simp only [Finset.mem_union, Finset.mem_Icc]; omega
  have hdisj : Disjoint (Finset.Icc 1 (m / 2)) (Finset.Icc (m / 2 + 1) (m - 1)) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    obtain ⟨_, h2⟩ := Finset.mem_Icc.mp ha
    obtain ⟨h3, _⟩ := Finset.mem_Icc.mp hb
    omega
  rw [hsplit, Finset.sum_union hdisj, sum_high_reindex (fun r => w r * A r) hm]
  refine congrArg _ (Finset.sum_congr rfl fun k hk => ?_)
  obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hk
  rw [← hsym k h1 (by omega)]

/-- The block side of the pairing, split into its two terms.  The guard
`k = m-k` deletes exactly the center index, which is what makes the partner sum
run over `Icc 1 (m-1-m/2)` rather than over the whole low half. -/
private theorem sum_pairs_split (w A : ℕ → ℝ) (m : ℕ) :
    ∑ k ∈ Finset.range (m / 2),
        w (k + 1) * (A (k + 1) + (if k + 1 = m - (k + 1) then 0 else A (m - (k + 1))))
      = (∑ k ∈ Finset.Icc 1 (m / 2), w k * A k)
        + ∑ k ∈ Finset.Icc 1 (m - 1 - m / 2), w k * A (m - k) := by
  rw [sum_shift (fun k => w k * (A k + (if k = m - k then 0 else A (m - k)))) m]
  have hexp : ∀ k ∈ Finset.Icc 1 (m / 2),
      w k * (A k + (if k = m - k then 0 else A (m - k)))
        = w k * A k + w k * (if k = m - k then 0 else A (m - k)) := by
    intro k _; ring
  rw [Finset.sum_congr rfl hexp, Finset.sum_add_distrib]
  refine congrArg _ ?_
  have hsub : Finset.Icc 1 (m - 1 - m / 2) ⊆ Finset.Icc 1 (m / 2) := by
    intro x hx
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hx
    exact Finset.mem_Icc.mpr ⟨h1, by omega⟩
  have hzero : ∀ x ∈ Finset.Icc 1 (m / 2), x ∉ Finset.Icc 1 (m - 1 - m / 2) →
      w x * (if x = m - x then 0 else A (m - x)) = 0 := by
    intro x hx hnx
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hx
    have hcen : x = m - x := by
      by_contra hne
      exact hnx (Finset.mem_Icc.mpr ⟨h1, by omega⟩)
    rw [if_pos hcen, mul_zero]
  rw [← Finset.sum_subset hsub hzero]
  refine Finset.sum_congr rfl fun k hk => ?_
  obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hk
  rw [if_neg (by omega : ¬ (k = m - k))]

/-- **The pairing identity `eq:B-def`, for an arbitrary term family.**  For
weights symmetric under `k ↔ m-k`, the weighted sum over `Icc 1 (m-1)` collapses
onto the paired blocks; at the center the partner is dropped.

Nothing here sees the multiplicity: the pairing needs only that the index set is
`Icc 1 (m-1)` and that `w` is symmetric under `k ↔ m-k`.  `Blocks` instantiates
it at `r = 3` and `Multiplicity/OrderTwo` at `r = 2`. -/
theorem sum_weighted_eq_pairs (w A : ℕ → ℝ) {m : ℕ} (hm : 2 ≤ m)
    (hsym : ∀ r, 1 ≤ r → r ≤ m - 1 → w r = w (m - r)) :
    ∑ r ∈ Finset.Icc 1 (m - 1), w r * A r
      = ∑ k ∈ Finset.range (m / 2),
          w (k + 1) * (A (k + 1) + (if k + 1 = m - (k + 1) then 0 else A (m - (k + 1)))) :=
  (sum_split_halves w A hm hsym).trans (sum_pairs_split w A m).symm

/-! ### The single sign change -/

/-- **Downward closure.**  Nonpositivity that steps down one index at a time
propagates from any nonpositive entry to every entry below it.  The induction
runs on the distance below `q`, which is what keeps the step hypothesis's
`j + 2 ≤ L` in range. -/
private theorem nonpos_below_of_stepDown {B : ℕ → ℝ} {L q : ℕ}
    (hdown : ∀ j, j + 2 ≤ L → B (j + 1) ≤ 0 → B j ≤ 0) (hq : q + 1 < L) (hqnp : B q ≤ 0) :
    ∀ k, k ≤ q → B k ≤ 0 := by
  have hbelow : ∀ j, j ≤ q → B (q - j) ≤ 0 := by
    intro j
    induction j with
    | zero => intro _; simpa using hqnp
    | succ i ih =>
      intro hi
      have hprev := ih (by omega)
      rw [show q - i = (q - (i + 1)) + 1 by omega] at hprev
      exact hdown (q - (i + 1)) (by omega) hprev
  intro k hk
  have hres := hbelow (q - k) (by omega)
  rwa [show q - (q - k) = k by omega] at hres

/-- **`lem:block-sign` in the form `lem:weighting` consumes, for an abstract
sequence.**  If nonpositivity propagates downward and the last entry is
positive, the sequence is nonpositive up to some index and nonnegative after
it, or nonnegative throughout. -/
theorem sign_change_of_stepDown {B : ℕ → ℝ} {L : ℕ}
    (hdown : ∀ j, j + 2 ≤ L → B (j + 1) ≤ 0 → B j ≤ 0) (hL : 1 ≤ L)
    (htop : 0 < B (L - 1)) :
    (∃ q, q + 1 < L ∧ (∀ k, k ≤ q → B k ≤ 0) ∧ (∀ k, q < k → k < L → 0 ≤ B k))
      ∨ (∀ k, k < L → 0 ≤ B k) := by
  set S := (Finset.range L).filter (fun k => B k ≤ 0) with hS
  rcases S.eq_empty_or_nonempty with hemp | hne
  · right
    intro k hk
    by_contra! hneg
    have hmem : k ∈ S := by
      simp only [hS, Finset.mem_filter, Finset.mem_range]
      exact ⟨hk, hneg.le⟩
    rw [hemp] at hmem
    simp at hmem
  · left
    obtain ⟨hqlt, hqnp⟩ : S.max' hne < L ∧ B (S.max' hne) ≤ 0 := by
      have := S.max'_mem hne
      simp only [hS, Finset.mem_filter, Finset.mem_range] at this
      exact this
    have hqtop : S.max' hne + 1 < L := by
      rcases lt_or_eq_of_le (show S.max' hne + 1 ≤ L by omega) with h' | h'
      · exact h'
      · exact absurd hqnp (not_le.mpr (by rw [show S.max' hne = L - 1 from by omega]; exact htop))
    refine ⟨S.max' hne, hqtop, ?_, ?_⟩
    · exact nonpos_below_of_stepDown hdown hqtop hqnp
    · intro k hkq hkm
      by_contra! hneg
      have hmem : k ∈ S := by
        simp only [hS, Finset.mem_filter, Finset.mem_range]
        exact ⟨hkm, hneg.le⟩
      exact absurd (S.le_max' k hmem) (by omega)

end CubicPochhammer
