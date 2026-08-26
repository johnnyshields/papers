/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import ForgacsTran.FTBranchAngle

/-!
# Existence and uniqueness of the Forgács–Tran branch

`Forgacs2017RationalDenominator` Lemma 2 in full: for positive `τ₁, …, τₙ` and a
target angle sum `S`, there is exactly one pair `(τ, (θ₁, …, θₙ))` with
`θ < θ_k < π`, `∑ θ_k = S` and the common ratio `τ_k sin θ_k / sin (θ_k - θ) = τ`.

## Main statements

* `exists_unique_ftTau` — the scalar equation `∑_k θ_k(τ) = S` has one root.
* `exists_unique_ftAngleSystem` — the whole system, clauses (i)–(iii).
* `exists_unique_ftAngleSystem_pencil` — the same with `S = rθ + lπ`,
  `θ ∈ (0, π/r)`.
* `ftAngleSum_range_of_eq_sub_one` — the range condition holds at `l = n - 1`,
  the index the paper uses.
* `not_exists_ftAngleSystem_of_le` — and it is necessary: at `(n, r, l) = (2, 2, 0)`
  clauses (i) and (ii) of Lemma 2 contradict each other outright.

## Implementation notes

**Differs from the paper's route.**  Two departures, both forced.  The tuple is
built from the closed form of `FTBranchAngle` rather than from the complex
implicit function theorem, so existence reduces to the intermediate value
theorem applied to a strictly decreasing scalar function.  And the range
condition `nθ < S` is carried as a hypothesis: Lemma 2 is stated there for every
`0 ≤ l < n`, but clause (i) forces `∑ θ_k > nθ` while clause (ii) sets
`∑ θ_k = rθ + lπ`, so the two are incompatible whenever `rθ + lπ ≤ nθ` —
`(n, r, l) = (2, 2, 0)` is the smallest instance.  The condition holds for every
`θ ∈ (0, π/r)` at `l = n - 1`, which is the only index the paper's later sections
use (their Remark 4 and Remark 6).

Sorry-free.

## References

Formalizes `Forgacs2017RationalDenominator` Lemmas 2--5, the branch
`thm:FT-geometry` imports.

## Tags

existence, uniqueness, Forgacs-Tran branch, angle system
-/

namespace ForgacsTran

open Real Set Filter Topology

/-- The scalar equation behind clause (ii) of `Forgacs2017RationalDenominator`
Lemma 2 has exactly one positive root, because `τ ↦ ∑_k θ_k(τ)` decreases
strictly from `nπ` to `nθ`. -/
theorem exists_unique_ftTau {n : ℕ} {a : Fin n → ℝ} (hn : 0 < n) (ha : ∀ k, 0 < a k)
    {θ S : ℝ} (hθ : θ ∈ Ioo 0 π) (hlo : (n : ℝ) * θ < S) (hhi : S < (n : ℝ) * π) :
    ∃! τ : ℝ, 0 < τ ∧ ftAngleSum a τ θ = S := by
  obtain ⟨τ₀, hτ₀S, hτ₀⟩ : ∃ τ₀ : ℝ, S < ftAngleSum a τ₀ θ ∧ τ₀ ∈ Ioi (0 : ℝ) :=
    (((tendsto_ftAngleSum_nhdsGT_zero ha hθ).eventually
      (eventually_gt_nhds hhi)).and self_mem_nhdsWithin).exists
  obtain ⟨τ₁, hτ₁S, hτ₁⟩ : ∃ τ₁ : ℝ, ftAngleSum a τ₁ θ < S ∧ τ₀ < τ₁ :=
    (((tendsto_ftAngleSum_atTop a hθ).eventually
      (eventually_lt_nhds hlo)).and (eventually_gt_atTop τ₀)).exists
  have hτ₀' : 0 < τ₀ := hτ₀
  have hcont : ContinuousOn (fun τ : ℝ => ftAngleSum a τ θ) (Icc τ₀ τ₁) :=
    (continuousOn_ftAngleSum a hθ).mono fun x hx => lt_of_lt_of_le hτ₀' hx.1
  obtain ⟨τ, hτmem, hτval0⟩ :=
    intermediate_value_Icc' hτ₁.le hcont ⟨hτ₁S.le, hτ₀S.le⟩
  have hτval : ftAngleSum a τ θ = S := hτval0
  refine ⟨τ, ⟨lt_of_lt_of_le hτ₀' hτmem.1, hτval⟩, ?_⟩
  rintro τ' ⟨hτ'pos, hτ'val⟩
  rcases lt_trichotomy τ' τ with h | h | h
  · have := ftAngleSum_lt (a := a) hn ha hθ hτ'pos h
    rw [hτ'val, hτval] at this; exact absurd this (lt_irrefl S)
  · exact h
  · have := ftAngleSum_lt (a := a) hn ha hθ (lt_of_lt_of_le hτ₀' hτmem.1) h
    rw [hτ'val, hτval] at this; exact absurd this (lt_irrefl S)

/-- **`Forgacs2017RationalDenominator` Lemma 2.**  Clauses (i), (ii), (iii) —
`θ_k > θ`, the prescribed angle sum, and the common ratio `τ` — determine the
pair `(τ, θ_•)` uniquely.  Clause (iii) appears cleared of denominators;
`ftAngle_ratio` restores their (10). -/
theorem exists_unique_ftAngleSystem {n : ℕ} {a : Fin n → ℝ} (hn : 0 < n) (ha : ∀ k, 0 < a k)
    {θ S : ℝ} (hθ : θ ∈ Ioo 0 π) (hlo : (n : ℝ) * θ < S) (hhi : S < (n : ℝ) * π) :
    ∃! p : ℝ × (Fin n → ℝ),
      0 < p.1 ∧ (∀ k, p.2 k ∈ Ioo θ π) ∧ (∑ k, p.2 k) = S ∧
        (∀ k, a k * Real.sin (p.2 k) = p.1 * Real.sin (p.2 k - θ)) := by
  obtain ⟨τ, ⟨hτpos, hτval⟩, huniq⟩ := exists_unique_ftTau hn ha hθ hlo hhi
  refine ⟨(τ, fun k => ftAngle (a k) τ θ), ⟨hτpos, fun k => ftAngle_mem_Ioo (ha k) hτpos hθ,
    hτval, fun k => ftAngle_spec (ne_of_gt hτpos) hθ⟩, ?_⟩
  rintro ⟨σ, φ⟩ ⟨hσpos, hφmem, hφsum, hφratio⟩
  have hφ : ∀ k, φ k = ftAngle (a k) σ θ := fun k =>
    ftAngle_unique hσpos hθ (hφmem k) (hφratio k)
  have hσ : σ = τ := huniq σ ⟨hσpos, by
    simpa [ftAngleSum, ← hφ] using hφsum⟩
  subst hσ
  simp only [Prod.mk.injEq, true_and]
  exact funext hφ

/-- The range condition is not decorative: clause (i) of
`Forgacs2017RationalDenominator` Lemma 2 already forces `∑ θ_k > nθ`, so no
system exists when the prescribed sum is at most `nθ`. -/
theorem not_exists_ftAngleSystem_of_le {n : ℕ} (hn : 0 < n) {θ S : ℝ}
    (hS : S ≤ (n : ℝ) * θ) :
    ¬ ∃ φ : Fin n → ℝ, (∀ k, θ < φ k) ∧ (∑ k, φ k) = S := by
  rintro ⟨φ, hφ, hsum⟩
  have hne : (Finset.univ : Finset (Fin n)).Nonempty :=
    Finset.univ_nonempty_iff.2 (Fin.pos_iff_nonempty.1 hn)
  have : (∑ _k : Fin n, θ) < ∑ k, φ k :=
    Finset.sum_lt_sum_of_nonempty hne fun k _ => hφ k
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hsum] at this
  linarith

/-- The smallest instance: at `n = r = 2`, `l = 0` the two clauses are
incompatible for every `θ`. -/
theorem not_exists_ftAngleSystem_two_two_zero {θ : ℝ} :
    ¬ ∃ φ : Fin 2 → ℝ, (∀ k, θ < φ k) ∧ (∑ k, φ k) = 2 * θ + (0 : ℕ) * π :=
  not_exists_ftAngleSystem_of_le (by norm_num) (by push_cast; linarith)

/-- At `l = n - 1` the range condition holds throughout `(0, π/r)`, excluding only
the degenerate `n = r = 1`.  This is the index `Forgacs2017RationalDenominator`
Remark 4 selects and Remark 6 abbreviates. -/
theorem ftAngleSum_range_of_eq_sub_one {n r : ℕ} (hn : 0 < n) (hr : 1 ≤ r)
    (hnr : 2 ≤ n ∨ 2 ≤ r) {θ : ℝ} (hθ0 : 0 < θ) (hθr : θ < π / r) :
    (n : ℝ) * θ < r * θ + ((n - 1 : ℕ) : ℝ) * π := by
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hpi := pi_pos
  have hn1 : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub hn, Nat.cast_one]
  rw [hn1]
  rcases Nat.lt_or_ge n 2 with hn2 | hn2
  · -- `n = 1`, so the sum condition reads `θ < rθ` and needs `r ≥ 2`
    have hne : n = 1 := by omega
    have hr2 : (2 : ℝ) ≤ r := by exact_mod_cast hnr.resolve_left (by omega)
    subst hne
    push_cast
    nlinarith
  · -- `n ≥ 2`, so `(n-1)π > 0` covers the case `n ≤ r` outright
    have hnge : (2 : ℝ) ≤ n := by exact_mod_cast hn2
    rcases le_or_gt (n : ℝ) r with h | h
    · nlinarith
    · have hstep : ((n : ℝ) - r) * θ < ((n : ℝ) - r) * (π / r) :=
        mul_lt_mul_of_pos_left hθr (by linarith)
      have hkey : (0 : ℝ) ≤ π * ((n : ℝ) * ((r : ℝ) - 1)) :=
        mul_nonneg hpi.le (mul_nonneg (by positivity) (by linarith))
      have hbound : ((n : ℝ) - r) * (π / r) ≤ ((n : ℝ) - 1) * π := by
        have hre : ((n : ℝ) - r) * (π / r) = ((n : ℝ) - r) * π / r := by ring
        rw [hre, div_le_iff₀ hr0]
        nlinarith [hkey]
      linarith

/-- **`Forgacs2017RationalDenominator` Lemma 2, as the paper states it**, with the
angle sum `rθ + lπ` and `θ` in the viewing arc `(0, π/r)`.  The range hypothesis
`hrange` is discharged at `l = n - 1` by `ftAngleSum_range_of_eq_sub_one`. -/
theorem exists_unique_ftAngleSystem_pencil {n r l : ℕ} {a : Fin n → ℝ} (hn : 0 < n)
    (ha : ∀ k, 0 < a k) (hr : 1 ≤ r) (hl : l < n) {θ : ℝ} (hθ0 : 0 < θ) (hθr : θ < π / r)
    (hrange : (n : ℝ) * θ < r * θ + l * π) :
    ∃! p : ℝ × (Fin n → ℝ),
      0 < p.1 ∧ (∀ k, p.2 k ∈ Ioo θ π) ∧ (∑ k, p.2 k) = r * θ + l * π ∧
        (∀ k, a k * Real.sin (p.2 k) = p.1 * Real.sin (p.2 k - θ)) := by
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  have hrθ : (r : ℝ) * θ < π := by rw [lt_div_iff₀ hr0] at hθr; linarith [hθr]
  have hθπ : θ < π := by
    have : (1 : ℝ) ≤ r := by exact_mod_cast hr
    nlinarith [hθ0]
  refine exists_unique_ftAngleSystem hn ha ⟨hθ0, hθπ⟩ hrange ?_
  have hln : (l : ℝ) ≤ (n : ℝ) - 1 := by
    have : (l : ℝ) + 1 ≤ n := by exact_mod_cast hl
    linarith
  nlinarith [pi_pos]

end ForgacsTran
