/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
-- TODO-COPIED: skew-ribbon-coarsenings/lean/SkewRibbonCoarsenings/LogarithmicCutoff.lean
import SkewRibbonCoarsenings.ArithmeticBound

/-!
# The weight-only upper bound for the arithmetic budget

Formalizes `shields-2026-ribbon-coarsenings.tex`, section `sec:depth`
(`prop:logarithmic-cutoff`, `eq:even-threshold`, `eq:odd-threshold`).

`uBound n` is the right-hand side `U(n)` of `eq:frontier`.  We prove `B(n) ≤ U(n)` for `n ≥ 2`,
`6 ^ B(n) ≤ 9 n ^ 2`, `B(n) ≤ 2 log₆ n + log₆ 9` for `n ≥ 1`, and that the additive constant
`log₆ 9` cannot be lowered uniformly.  Sorry-free.
-/

open scoped ArithmeticFunction.Omega

namespace SkewRibbonCoarsenings

/-- The right-hand side `U(n)` of `eq:frontier`: `0` for `n = 1`, `2` for `2 ≤ n ≤ 4`, `3` for
`5 ≤ n ≤ 11`, and for `n ≥ 12` the value `2j + 4 + 𝟙[n ≥ 30 · 6^j]` where `j` is determined by
`12 · 6^j ≤ n < 72 · 6^j`, i.e. `j = ⌊log₆ ⌊n/12⌋⌋`. -/
def uBound (n : ℕ) : ℕ :=
  if n = 1 then 0 else if n ≤ 4 then 2 else if n < 12 then 3 else
    2 * Nat.log 6 (n / 12) + 4 + (if 30 * 6 ^ Nat.log 6 (n / 12) ≤ n then 1 else 0)

/-- `eq:frontier` for `n ≥ 12`: with `12 · 6^j ≤ n < 72 · 6^j` one has
`U(n) = 2j + 4 + 𝟙[n ≥ 30 · 6^j]`. -/
lemma uBound_of_bracket {n j : ℕ} (h1 : 12 * 6 ^ j ≤ n) (h2 : n < 72 * 6 ^ j) :
    uBound n = 2 * j + 4 + (if 30 * 6 ^ j ≤ n then 1 else 0) := by
  have hpos : 0 < 6 ^ j := by positivity
  have hlog : Nat.log 6 (n / 12) = j := by
    apply Nat.log_eq_of_pow_le_of_lt_pow
    · rw [Nat.le_div_iff_mul_le (by norm_num)]; omega
    · rw [Nat.div_lt_iff_lt_mul (by norm_num), pow_succ]; omega
  have hn1 : n ≠ 1 := by
    have : 12 ≤ 12 * 6 ^ j := by nlinarith
    omega
  have hn12 : ¬ n < 12 := by
    have : 12 ≤ 12 * 6 ^ j := by nlinarith
    omega
  unfold uBound
  rw [if_neg hn1, if_neg (by omega), if_neg hn12, hlog]

/-- `eq:frontier`: the first cases of `U`. -/
lemma uBound_small :
    uBound 1 = 0 ∧ (∀ n, 2 ≤ n → n ≤ 4 → uBound n = 2) ∧
      (∀ n, 5 ≤ n → n ≤ 11 → uBound n = 3) := by
  refine ⟨by simp [uBound], fun n h2 h4 => ?_, fun n h5 h11 => ?_⟩
  · unfold uBound
    rw [if_neg (by omega)]
    exact if_pos h4
  · unfold uBound
    rw [if_neg (by omega), if_neg (by omega)]
    exact if_pos (by omega)

/-! ### Products of lists without adjacent twos -/

private lemma six_le_mul {x y : ℕ} (hx : 2 ≤ x) (hy : 2 ≤ y) (h : ¬ (x = 2 ∧ y = 2)) :
    6 ≤ x * y := by
  by_cases hx2 : x = 2
  · subst hx2
    have : 3 ≤ y := by omega
    omega
  · have : 3 ≤ x := by omega
    nlinarith

private lemma six_pow_le_prod : ∀ l : List ℕ, (∀ x ∈ l, 2 ≤ x) →
    l.IsChain (fun a b => ¬ (a = 2 ∧ b = 2)) → 6 ^ (l.length / 2) ≤ l.prod
  | [], _, _ => by simp
  | [x], h, _ => by
    have := h x (by simp)
    simp only [List.length_singleton, List.prod_singleton]
    norm_num
    omega
  | x :: y :: t, h, hc => by
    have hx := h x (by simp)
    have hy := h y (by simp)
    rw [List.isChain_cons_cons] at hc
    have ih := six_pow_le_prod t (fun z hz => h z (by simp [hz])) hc.2.tail
    have hxy := six_le_mul hx hy hc.1
    have hlen : (x :: y :: t).length / 2 = t.length / 2 + 1 := by
      simp only [List.length_cons]; omega
    rw [hlen, pow_succ, List.prod_cons, List.prod_cons, ← mul_assoc]
    calc 6 ^ (t.length / 2) * 6 ≤ t.prod * (x * y) := Nat.mul_le_mul ih hxy
      _ = x * y * t.prod := by ring

/-- The two thresholds `eq:even-threshold` and `eq:odd-threshold` for a divisor candidate:
with `L = T_e(d/e)`, either `L = 2j` and `n ≥ 12 · 6^j`, or `L = 2j + 1` and `n ≥ 30 · 6^j`. -/
lemma candidate_threshold {n e d : ℕ} (hn : n ≠ 0) (hed : e ∣ d) (hdn : d ∣ n) (he : 4 ≤ e)
    (h3 : 3 ≤ n / d) :
    ∃ j, (arithT e (d / e) = 2 * j ∧ 12 * 6 ^ j ≤ n) ∨
      (arithT e (d / e) = 2 * j + 1 ∧ 30 * 6 ^ j ≤ n) := by
  have hd0 : d ≠ 0 := ne_zero_of_dvd_ne_zero hn hdn
  have hde : 0 < d / e :=
    Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hd0) hed) (by omega)
  obtain ⟨l, ⟨h2, hdvd, hc, hhead⟩, hlen⟩ := exists_ratioList_length_eq (e := e) (D := d / e) hde.ne'
  have hP : l.prod ≤ d / e := Nat.le_of_dvd hde hdvd
  have hfac : n = (n / d) * (e * (d / e)) := by
    rw [Nat.mul_div_cancel' hed, Nat.div_mul_cancel hdn]
  have hn3 : 3 * (e * l.prod) ≤ n := by
    calc 3 * (e * l.prod) ≤ (n / d) * (e * (d / e)) :=
          Nat.mul_le_mul h3 (Nat.mul_le_mul_left e hP)
      _ = n := hfac.symm
  rw [← hlen]
  rcases Nat.even_or_odd' l.length with ⟨j, hj | hj⟩
  · refine ⟨j, Or.inl ⟨hj, ?_⟩⟩
    have h6 := six_pow_le_prod l h2 hc
    rw [hj, Nat.mul_div_cancel_left _ (by norm_num)] at h6
    have h4 : 4 * 6 ^ j ≤ e * l.prod := Nat.mul_le_mul he h6
    omega
  · refine ⟨j, Or.inr ⟨hj, ?_⟩⟩
    cases l with
    | nil => simp at hj
    | cons x t =>
      have hx := h2 x (by simp)
      have ht := six_pow_le_prod t (fun z hz => h2 z (by simp [hz])) hc.tail
      have htl : t.length = 2 * j := by simp at hj; omega
      rw [htl, Nat.mul_div_cancel_left _ (by norm_num)] at ht
      have hxe : 30 ≤ 3 * (e * x) := by
        by_cases he4 : e = 4
        · subst he4
          have : x ≠ 2 := by
            intro hx2
            exact hhead rfl (by simp [hx2])
          omega
        · have : 5 * 2 ≤ e * x := Nat.mul_le_mul (by omega) hx
          omega
      rw [List.prod_cons] at hn3
      calc 30 * 6 ^ j ≤ 3 * (e * x) * 6 ^ j := Nat.mul_le_mul_right _ hxe
        _ = 3 * (e * (x * 6 ^ j)) := by ring
        _ ≤ 3 * (e * (x * t.prod)) := by
          exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ ht))
        _ ≤ n := hn3

/-- Every divisor candidate is at most `U(n)`. -/
lemma candidate_le_uBound {n e d : ℕ} (hn : n ≠ 0) (hed : e ∣ d) (hdn : d ∣ n) (he : 4 ≤ e)
    (h3 : 3 ≤ n / d) : 4 + arithT e (d / e) ≤ uBound n := by
  obtain ⟨j, hj⟩ := candidate_threshold hn hed hdn he h3
  have hpos : 0 < 6 ^ j := by positivity
  have hn12 : 12 ≤ n := by
    rcases hj with ⟨_, h⟩ | ⟨_, h⟩ <;> nlinarith
  have hjn : j ≤ Nat.log 6 (n / 12) := by
    apply Nat.le_log_of_pow_le (by norm_num)
    rw [Nat.le_div_iff_mul_le (by norm_num)]
    rcases hj with ⟨_, h⟩ | ⟨_, h⟩ <;> omega
  unfold uBound
  simp only [show n ≠ 1 by omega, show ¬ n ≤ 4 by omega, show ¬ n < 12 by omega, if_false]
  rcases hj with ⟨hL, _⟩ | ⟨hL, h30⟩
  · rw [hL]; omega
  · rw [hL]
    by_cases hJ : j + 1 ≤ Nat.log 6 (n / 12)
    · omega
    · have : Nat.log 6 (n / 12) = j := by omega
      rw [this, if_pos h30]
      omega

/-- `prop:logarithmic-cutoff`: `B(n) ≤ U(n)` for `n ≥ 2`. -/
theorem arithBound_le_uBound {n : ℕ} (hn : 2 ≤ n) : arithBound n ≤ uBound n := by
  by_cases h4 : n ≤ 4
  · rw [arithBound_of_two_le_le_four hn h4, uBound_small.2.1 n hn h4]
  · by_cases h12 : n < 12
    · rw [uBound_small.2.2 n (by omega) (by omega)]
      refine arithBound_le_of_cands (by omega) le_rfl ?_
      intro e d h1 h2 he h5
      exfalso
      have hd : e ≤ d := Nat.le_of_dvd (Nat.pos_of_ne_zero
        (ne_zero_of_dvd_ne_zero (by omega) h2)) h1
      have : n / d * d ≤ n := Nat.div_mul_le_self n d
      nlinarith
    · refine arithBound_le_of_cands (by omega) ?_ ?_
      · unfold uBound
        simp only [show n ≠ 1 by omega, show ¬ n ≤ 4 by omega, show ¬ n < 12 by omega, if_false]
        omega
      · intro e d h1 h2 he h5
        exact candidate_le_uBound (by omega) h1 h2 he h5

/-! ### The logarithmic estimate -/

/-- Every divisor candidate satisfies `6 ^ (4 + T_e(d/e)) ≤ 9 n²`. -/
lemma candidate_pow_le {n e d : ℕ} (hn : n ≠ 0) (hed : e ∣ d) (hdn : d ∣ n) (he : 4 ≤ e)
    (h3 : 3 ≤ n / d) : 6 ^ (4 + arithT e (d / e)) ≤ 9 * n ^ 2 := by
  obtain ⟨j, hj⟩ := candidate_threshold hn hed hdn he h3
  have hs : 6 ^ (2 * j) = (6 ^ j) ^ 2 := by rw [pow_mul']
  rcases hj with ⟨hL, h⟩ | ⟨hL, h⟩
  · rw [hL, pow_add, hs]
    have := Nat.pow_le_pow_left h 2
    nlinarith
  · rw [hL, show 4 + (2 * j + 1) = 2 * j + 5 by ring, pow_add, hs]
    have := Nat.pow_le_pow_left h 2
    nlinarith

/-- `prop:logarithmic-cutoff`: `6 ^ B(n) ≤ 9 n²` for every `n ≥ 1`. -/
theorem six_pow_arithBound_le {n : ℕ} (hn : 1 ≤ n) : 6 ^ arithBound n ≤ 9 * n ^ 2 := by
  by_cases h1 : n = 1
  · subst h1; simp [arithBound_one]
  by_cases h4 : n ≤ 4
  · rw [arithBound_of_two_le_le_four (by omega) h4]
    have h2n : 2 ≤ n := by omega
    have : 4 ≤ n ^ 2 := by nlinarith
    omega
  · rw [arithBound_of_five_le (by omega)]
    refine le_trans (Nat.pow_le_pow_right (by norm_num) (min_le_right _ _)) ?_
    obtain ⟨x, hx, hxe⟩ := Finset.exists_mem_eq_sup (insert 3 (arithCandidates n))
      ⟨3, Finset.mem_insert_self _ _⟩ id
    unfold arithBoundMax
    rw [hxe]
    simp only [id]
    rcases Finset.mem_insert.1 hx with rfl | hx
    · nlinarith
    · obtain ⟨_, e, d, h1, h2, he, h5, rfl⟩ := mem_arithCandidates.1 hx
      exact candidate_pow_le (by omega) h1 h2 he h5

/-- `prop:logarithmic-cutoff`: `B(n) ≤ 2 log₆ n + log₆ 9` for every `n ≥ 1`. -/
theorem arithBound_le_logb {n : ℕ} (hn : 1 ≤ n) :
    (arithBound n : ℝ) ≤ 2 * Real.logb 6 n + Real.logb 6 9 := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hpow : (6 : ℝ) ^ (arithBound n : ℝ) ≤ 9 * (n : ℝ) ^ 2 := by
    rw [Real.rpow_natCast]
    exact_mod_cast six_pow_arithBound_le hn
  have h := (Real.le_logb_iff_rpow_le (by norm_num : (1 : ℝ) < 6) (by positivity)).2 hpow
  rw [Real.logb_mul (by norm_num) (by positivity), Real.logb_pow] at h
  push_cast at h
  linarith

/-- `prop:logarithmic-cutoff`, equality at `n = 2`: `B(2) = 2 log₆ 2 + log₆ 9`. -/
theorem arithBound_two_eq_logb : (arithBound 2 : ℝ) = 2 * Real.logb 6 2 + Real.logb 6 9 := by
  rw [arithBound_of_two_le_le_four le_rfl (by norm_num)]
  have : (2 : ℝ) * Real.logb 6 2 + Real.logb 6 9 = Real.logb 6 (2 ^ 2 * 9) := by
    rw [Real.logb_mul (by norm_num) (by norm_num), Real.logb_pow]
    push_cast; ring
  rw [this, show ((2 : ℝ) ^ 2 * 9) = 6 ^ 2 by norm_num, Real.logb_pow, Real.logb_self_eq_one
    (by norm_num)]
  norm_num

/-- `prop:logarithmic-cutoff`: the additive constant cannot be decreased uniformly over all
positive weights: if `B(n) ≤ 2 log₆ n + c` for every `n ≥ 1` then `log₆ 9 ≤ c`. -/
theorem logb_const_optimal {c : ℝ}
    (h : ∀ n : ℕ, 1 ≤ n → (arithBound n : ℝ) ≤ 2 * Real.logb 6 n + c) :
    Real.logb 6 9 ≤ c := by
  have := h 2 (by norm_num)
  rw [arithBound_two_eq_logb] at this
  push_cast at this
  linarith

end SkewRibbonCoarsenings
