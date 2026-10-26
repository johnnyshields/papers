import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Int.Star
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Common
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Zify
import SkewGluing.Tactics

/-!
# The chart score and the arithmetic of source-minimal fibers

Formalizes `shields-2026-skew-gluing.tex`, «Source-minimal fibers» (`eq:chart-score`,
`thm:source-minimal-domination`, `cor:least-root-period`, `eq:nonminimal-fiber`).

The score of a proper chart of period `p` and width `w = N mod p` at a diagram of span `N` is
`(N mod p, p + N mod p)` in the lexicographic order, so it is a function of `p` alone.  This file
proves the arithmetic steps of the paper:

* a score minimizer exists over any nonempty set of admissible periods (`exists_score_min`);
* a proper divisor has strictly smaller score (`score_lt_of_dvd`), and so does the gcd of two
  nondividing periods (`score_gcd_lt_left`, `score_gcd_lt_right`);
* the least period of a set that is closed under folding and has no coprime pair divides every
  period, and least-period is the same as score-minimal (`least_period_dvd`,
  `isScoreMinimal_iff_eq_least`);
* the span-`27` and span-`7` numerical claims of the two worked examples.

The geometric inputs (that a divisor or a gcd chart exists, that coprime periods force line
inners) are hypotheses on the set of periods: they are `lem:gluing-small`,
`prop:gluing-ordinary-fold`, `prop:gluing-mixed-fold` and `lem:gluing-lines`, proved elsewhere.

Sorry-free.
-/

namespace SkewGluing

/-- `eq:chart-score`: the score `(N mod p, p + N mod p)` of a proper chart of period `p` at a
diagram of span `N`, in the lexicographic order.  The first coordinate is the overlap width and
the second the inner span. -/
def score (N p : ℕ) : ℕ ×ₗ ℕ := toLex (N % p, p + N % p)

theorem score_lt_iff {N p q : ℕ} :
    score N p < score N q ↔
      N % p < N % q ∨ (N % p = N % q ∧ p + N % p < q + N % q) := by
  simp [score, Prod.Lex.toLex_lt_toLex]

/-- The decomposition `N = r p + w` with `r ≥ 2` and `0 ≤ w < p` of the span of a proper chart
has width `w = N mod p` and outer span `r = N / p`, so the score of `eq:chart-score` depends on
`p` alone. -/
theorem width_eq_mod_of_span {N p r w : ℕ} (hw : w < p) (hN : N = r * p + w) :
    w = N % p ∧ r = N / p := by
  have hp : 0 < p := by omega
  subst hN
  constructor
  · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hw]
  · rw [Nat.add_comm, Nat.add_mul_div_right _ _ hp, Nat.div_eq_of_lt hw]; simp

/-- The admissible periods `2 ≤ p ≤ N / 2` are exactly those `p ≥ 2` for which `N = r p + w`
with `r ≥ 2` and `0 ≤ w < p`. -/
theorem exists_span_decomposition_iff {N p : ℕ} (hp : 2 ≤ p) :
    (∃ r w : ℕ, 2 ≤ r ∧ w < p ∧ N = r * p + w) ↔ p ≤ N / 2 := by
  constructor
  · rintro ⟨r, w, hr, hw, rfl⟩
    have : 2 * p ≤ r * p + w := by nlinarith
    omega
  · intro h
    refine ⟨N / p, N % p, ?_, Nat.mod_lt _ (by omega), ?_⟩
    · rw [Nat.le_div_iff_mul_le (by omega)]; omega
    · rw [Nat.mul_comm]; exact (Nat.div_add_mod N p).symm

/-- **Existence of a score minimizer** (`eq:chart-score`): over any nonempty set of periods in
the finite range `2 ≤ p ≤ N / 2` there is a period of least score. -/
theorem exists_score_min (N : ℕ) {S : Set ℕ} (hS : S ⊆ Set.Icc 2 (N / 2)) (hne : S.Nonempty) :
    ∃ p ∈ S, ∀ q ∈ S, score N p ≤ score N q :=
  Set.exists_min_image S (score N) ((Set.finite_Icc 2 (N / 2)).subset hS) hne

/-- For `q ∣ p`, `N mod q = (N mod p) mod q`. -/
theorem mod_eq_mod_mod_of_dvd {N p q : ℕ} (h : q ∣ p) : N % q = (N % p) % q :=
  (Nat.mod_mod_of_dvd N h).symm

/-- `thm:source-minimal-domination`, the step "`q ∣ p`, `q < p`": the width does not increase,
and at equal width the inner span decreases, so the score of `q` is strictly smaller. -/
theorem score_lt_of_dvd {N p q : ℕ} (hdvd : q ∣ p) (hlt : q < p) : score N q < score N p := by
  have hle : N % q ≤ N % p := by
    rw [mod_eq_mod_mod_of_dvd hdvd]; exact Nat.mod_le _ _
  rw [score_lt_iff]
  rcases hle.lt_or_eq with h | h
  · exact Or.inl h
  · exact Or.inr ⟨h, by omega⟩

/-- The width of the gcd chart is `(N mod p) mod g`. -/
theorem mod_gcd_eq_mod_mod {N p q : ℕ} : N % Nat.gcd p q = (N % p) % Nat.gcd p q :=
  mod_eq_mod_mod_of_dvd (Nat.gcd_dvd_left p q)

/-- `thm:source-minimal-domination`, the step "neither divides": the gcd of two nondividing
periods has strictly smaller score than the first.  (The paper assumes `g > 1`; this is only
needed to have a chart at `g`, not for the inequality.) -/
theorem score_gcd_lt_left {N p q : ℕ} (hp : 0 < p) (hnd : ¬ p ∣ q) :
    score N (Nat.gcd p q) < score N p := by
  refine score_lt_of_dvd (Nat.gcd_dvd_left p q) ?_
  refine lt_of_le_of_ne (Nat.le_of_dvd hp (Nat.gcd_dvd_left p q)) ?_
  intro h
  exact hnd (h ▸ Nat.gcd_dvd_right p q)

/-- The gcd of two nondividing periods has strictly smaller score than the second. -/
theorem score_gcd_lt_right {N p q : ℕ} (hq : 0 < q) (hnd : ¬ q ∣ p) :
    score N (Nat.gcd p q) < score N q := by
  rw [Nat.gcd_comm]
  exact score_gcd_lt_left hq hnd

/-- `S` is score-minimal at `p` for the span `N`: `p` belongs to `S` and no period of `S` has a
smaller score. -/
def IsScoreMinimal (N : ℕ) (S : Set ℕ) (p : ℕ) : Prop :=
  p ∈ S ∧ ∀ q ∈ S, score N p ≤ score N q

/-- The comparison table of `thm:source-minimal-domination`, abstractly.  Let `S` be the set of
proper periods at a diagram of span `N`, and `p` the period of a source-minimal chart.  Suppose
that a gcd of nondividing periods with `gcd > 1` is again a period of `S` (the fold
constructions) and that no period of `S` is coprime to `p` except those divisible by it (no line
inner).  Then `p` divides every period of `S`.

This is the arithmetic content of the last sentence of `cor:least-root-period`: the period of a
source-minimal chart with a nonline inner divides every proper period.  The hypothesis `hfold`
is the conclusion of `lem:gluing-small`, `prop:gluing-ordinary-fold`,
`prop:gluing-mixed-fold`; `hcop` is `lem:gluing-lines`. -/
theorem dvd_of_isScoreMinimal {N : ℕ} {S : Set ℕ} (hS : ∀ q ∈ S, 2 ≤ q) {p : ℕ}
    (hmin : IsScoreMinimal N S p)
    (hfold : ∀ q ∈ S, ¬ p ∣ q → ¬ q ∣ p → 1 < Nat.gcd p q → Nat.gcd p q ∈ S)
    (hcop : ∀ q ∈ S, ¬ p ∣ q → Nat.gcd p q ≠ 1) :
    ∀ q ∈ S, p ∣ q := by
  intro q hq
  by_contra hpq
  have hp2 := hS p hmin.1
  have hq2 := hS q hq
  by_cases hqp : q ∣ p
  · -- a smaller divisor chart
    have hlt : q < p := lt_of_le_of_ne (Nat.le_of_dvd (by omega) hqp) (fun h => hpq (h ▸ dvd_rfl))
    exact absurd (hmin.2 q hq) (not_le.mpr (score_lt_of_dvd hqp hlt))
  · -- a proper gcd chart
    have hg1 : 1 < Nat.gcd p q := by
      have h0 : Nat.gcd p q ≠ 0 := by
        intro h; have := Nat.gcd_eq_zero_iff.mp h; omega
      have := hcop q hq hpq
      omega
    have hgS := hfold q hq hpq hqp hg1
    exact absurd (hmin.2 _ hgS) (not_le.mpr (score_gcd_lt_left (by omega) hpq))

/-- `cor:least-root-period`, least period divides every period.  Let `S` be the set of proper
periods and `p₀ ∈ S` its least element.  If a gcd of nondividing periods with `gcd > 1` is again
in `S` and no two periods of `S` are coprime, then `p₀` divides every period of `S`. -/
theorem least_period_dvd {S : Set ℕ} (hS : ∀ q ∈ S, 2 ≤ q) {p₀ : ℕ} (hp₀ : p₀ ∈ S)
    (hleast : ∀ q ∈ S, p₀ ≤ q)
    (hfold : ∀ p ∈ S, ∀ q ∈ S, ¬ p ∣ q → ¬ q ∣ p → 1 < Nat.gcd p q → Nat.gcd p q ∈ S)
    (hcop : ∀ p ∈ S, ∀ q ∈ S, Nat.gcd p q ≠ 1) :
    ∀ q ∈ S, p₀ ∣ q := by
  intro q hq
  by_contra hpq
  have hp2 := hS p₀ hp₀
  have hq2 := hS q hq
  by_cases hqp : q ∣ p₀
  · have hlt : q < p₀ :=
      lt_of_le_of_ne (Nat.le_of_dvd (by omega) hqp) (fun h => hpq (h ▸ dvd_rfl))
    exact absurd (hleast q hq) (not_le.mpr hlt)
  · have hg1 : 1 < Nat.gcd p₀ q := by
      have h0 : Nat.gcd p₀ q ≠ 0 := by
        intro h; have := Nat.gcd_eq_zero_iff.mp h; omega
      have := hcop p₀ hp₀ q hq
      omega
    have hgS := hfold p₀ hp₀ q hq hpq hqp hg1
    have hgle := hleast _ hgS
    have hgd : Nat.gcd p₀ q ≤ p₀ := Nat.le_of_dvd (by omega) (Nat.gcd_dvd_left _ _)
    have : Nat.gcd p₀ q = p₀ := le_antisymm hgd hgle
    exact hpq (this ▸ Nat.gcd_dvd_right p₀ q)

/-- `cor:least-root-period`, widths.  If `p₀ ∣ q`, the width `N mod q` of the period-`q` chart
is `b p₀ + w₀` with `w₀ = N mod p₀`, for some `b ≥ 0`. -/
theorem width_eq_mul_add_of_dvd {N p₀ q : ℕ} (h : p₀ ∣ q) :
    ∃ b : ℕ, N % q = b * p₀ + N % p₀ := by
  have e : N % p₀ = (N % q) % p₀ := mod_eq_mod_mod_of_dvd h
  refine ⟨(N % q) / p₀, ?_⟩
  rw [e]
  exact (Nat.div_add_mod' _ _).symm

/-- `cor:least-root-period`, least period is score-minimal.  If every period of `S` is a
multiple of its least element `p₀`, then a period has least score exactly when it is `p₀`. -/
theorem isScoreMinimal_iff_eq_least {N : ℕ} {S : Set ℕ} {p₀ : ℕ} (hp₀ : p₀ ∈ S)
    (hleast : ∀ q ∈ S, p₀ ≤ q) (hmult : ∀ q ∈ S, p₀ ∣ q) {p : ℕ} :
    IsScoreMinimal N S p ↔ p = p₀ := by
  constructor
  · rintro ⟨hp, hmin⟩
    by_contra hne
    have hlt : p₀ < p := lt_of_le_of_ne (hleast p hp) (Ne.symm hne)
    exact absurd (hmin p₀ hp₀) (not_le.mpr (score_lt_of_dvd (hmult p hp) hlt))
  · rintro rfl
    refine ⟨hp₀, fun q hq => ?_⟩
    by_cases hqp : q = p
    · rw [hqp]
    · exact (score_lt_of_dvd (hmult q hq) (lt_of_le_of_ne (hleast q hq) (Ne.symm hqp))).le

/-- `cor:least-root-period`, a larger period has strictly larger score: if `p₀ ∣ q` and
`p₀ < q` then `score N p₀ < score N q`. -/
theorem score_lt_of_least_dvd {N p₀ q : ℕ} (h : p₀ ∣ q) (hlt : p₀ < q) :
    score N p₀ < score N q :=
  score_lt_of_dvd h hlt

/-! ### The row example: periods two and three at span seven -/

/-- The row example after `cor:least-root-period`: `(7) = (3) ∘ (3) = (2) ∘ (4)` has periods two
and three, both with width one; the least proper period two does not divide three.  The set of
admissible periods `2 ≤ p ≤ 7 / 2` at span seven is `{2, 3}`. -/
theorem row_example :
    7 = 3 * 2 + 1 ∧ 7 = 2 * 3 + 1 ∧ 7 % 2 = 1 ∧ 7 % 3 = 1 ∧ ¬ 2 ∣ 3 ∧
      Set.Icc 2 (7 / 2) = {2, 3} ∧ score 7 2 = toLex (1, 3) ∧ score 7 3 = toLex (1, 4) := by
  refine ⟨rfl, rfl, rfl, rfl, by decide, ?_, rfl, rfl⟩
  ext p
  simp only [Set.mem_Icc, Set.mem_insert_iff, Set.mem_singleton_iff]
  omega

/-! ### The nonminimal-fiber example: span twenty-seven -/

/-- The fine chart of the nonminimal-fiber example, of period two at span `27`, has score
`(1, 3)`; the coarse chart of period eight has score `(3, 11)`. -/
theorem nonminimal_fiber_scores :
    score 27 2 = toLex (1, 3) ∧ score 27 8 = toLex (3, 11) := ⟨rfl, rfl⟩

/-- A proper empty-overlap period at span `27` is a period `p ≥ 2` with `27 = r p` and outer
span `r ≥ 2`; the only ones are `3` and `9`. -/
theorem span_27_empty_overlap_periods (p : ℕ) :
    (2 ≤ p ∧ ∃ r, 2 ≤ r ∧ 27 = r * p) ↔ p = 3 ∨ p = 9 := by
  constructor
  · rintro ⟨hp, r, hr, h⟩
    have hp27 : p ∣ 27 := ⟨r, by rw [h, Nat.mul_comm]⟩
    have hle : p ≤ 27 := Nat.le_of_dvd (by norm_num) hp27
    have hr27 : r ≤ 27 := by nlinarith
    interval_cases p <;> interval_cases r <;> omega
  · rintro (rfl | rfl)
    · exact ⟨by norm_num, 9, by norm_num, by norm_num⟩
    · exact ⟨by norm_num, 3, by norm_num, by norm_num⟩

/-- Both empty-overlap periods at span `27` are coprime to the period two of the supplied mixed
chart, so `lem:gluing-lines` excludes them. -/
theorem span_27_empty_overlap_periods_coprime_two (p : ℕ) (hp : p = 3 ∨ p = 9) :
    Nat.Coprime p 2 := by
  rcases hp with rfl | rfl <;> decide

/-- At span `27`, a period `p` in the admissible range `2 ≤ p ≤ 13` with score below the fine
score `(1, 3)` of period two has width zero, so it is `3` or `9`.  Hence a score below `(1, 3)`
would need width zero. -/
theorem span_27_score_below_fine (p : ℕ) (hp : p ∈ Set.Icc 2 (27 / 2)) :
    score 27 p < score 27 2 ↔ p = 3 ∨ p = 9 := by
  obtain ⟨h2, h13⟩ := hp
  have h13' : p ≤ 13 := by omega
  interval_cases p <;> simp [score, Prod.Lex.toLex_lt_toLex]

end SkewGluing
