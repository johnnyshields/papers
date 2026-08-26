/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Darroch's theorem: the mode of a Poisson binomial

Darroch's theorem places the mode of a finite sum of independent Bernoulli variables at the mean
whenever that mean is an integer.  This file proves its heart — the **tie inequality** — from three
structural facts about the distribution and nothing else.

## The tie inequality

Write `a` for the mass function of `X = \sum_{i\in s}B_i` with `B_i \sim \mathrm{Bernoulli}(p_i)`,
and `b_i` for the mass function of `X` with `B_i` removed.  Three facts relate them:

* the **Bernoulli recursion** `a_j = (1-p_i)b_{i,j} + p_ib_{i,j-1}`, one for each `i`;
* the two **double-counting identities** `(k+1)a_{k+1} = \sum_i p_ib_{i,k}` and
  `(N-k)a_k = \sum_i(1-p_i)b_{i,k}`, from counting the pairs `(T,i)` with `|T| = k+1`, `i\in T` and
  with `|T| = k`, `i\notin T`;
* **log-concavity** of each `b_i`.

Given a *tie* `a_k = a_{k+1} > 0`, `Shields.tie_mean_bounds` concludes `k \le \sum_ip_i \le k+1`.

## Why the tie is the whole content

The mechanism is short.  Subtracting the recursion at `j = k` from the recursion at `j = k+1` and
using the tie gives, for each `i`,

    (1-p_i)\bigl(b_{i,k}-b_{i,k+1}\bigr) = p_i\bigl(b_{i,k}-b_{i,k-1}\bigr) ,

so the two differences carry the same sign.  Were both negative, `b_{i,k}` would be a strict local
minimum of a nonnegative log-concave sequence, which `b_{i,k-1}b_{i,k+1} \le b_{i,k}^2` forbids.
Hence `b_{i,k} \ge b_{i,k-1}` for every `i` — `Shields.nonneg_of_tie` — and the two double-counting
identities turn that single sign into the two bounds, because
`b_{i,k}-a_k = p_i(b_{i,k}-b_{i,k-1})` exactly.

## From the tie to Darroch

The tie is constructible: tilting by `t` multiplies `a_j` by `t^j` and renormalizes
(`Shields.pbPmf_tilt`), and tilting a Poisson binomial gives another one, with
`p_i \mapsto p_it/(1-p_i+p_it)`.  So if `a_{M+1} > a_M > 0` at an integer mean `M`, tilt by
`t = a_M/a_{M+1} < 1`: the tilted law ties at `(M,M+1)`, so its mean is at least `M`.  But no
parameter increases under a tilt by `t < 1`, so the tilted mean is at most `M` — and equality forces
the tilt to be the identity, hence `t = 1`.  That contradiction is `Shields.pbPmf_succ_le`; the
mirror `p_i \mapsto 1-p_i`, which reverses the mass function, gives the step to the left, and
`IsPF2` spreads both steps to every index.

## Main results

* `Shields.IsPF2`, `Shields.IsPF2.bernConv` — Pólya frequency of order two, closed under convolution
  with a two-point law; `Shields.pbPmf_isPF2` is the consequence for the Poisson binomial.
* `Shields.nonneg_of_tie` — the sign of the leave-one-out difference.
* `Shields.tie_mean_bounds` — the tie inequality, `k \le \sum_ip_i \le k+1`.
* `Shields.pbPmf`, `Shields.pbPmf_rec`, `Shields.pbPmf_countUp`, `Shields.pbPmf_countDown` — the
  mass function and the three structural facts.
* `Shields.pbPmf_le_of_mean_eq` — **Darroch's theorem**.

## Implementation notes

The mass functions are indexed by `ℤ`, so the recursion's `j-1` is honest subtraction and no `k = 0`
case appears anywhere.  The mass function is defined through the generating polynomial, which makes
the recursion a coefficient identity for a linear factor and the upward double-counting identity the
product rule — `Polynomial.derivative_prod_finset` — rather than a bijection between set families.
The downward identity then follows from the upward one and the recursion, so no second count is
needed.

`IsPF2` carries the full `2\times2` minor condition rather than plain log-concavity because that is
what is closed under the Bernoulli convolution: the cross term of the expansion is
`f_if_{j-1}-f_{i-2}f_{j+1}`, a two-step shift that log-concavity alone does not bound.

Mathlib carries no Poisson binomial mode result, and no Pólya frequency or ultra-log-concavity API,
at the pinned revision.

## Tags

Poisson binomial, mode, Darroch, log-concave, Pólya frequency
-/

namespace Shields

variable {ι : Type*} {s : Finset ι} {p : ι → ℝ} {a : ℤ → ℝ} {b : ι → ℤ → ℝ} {k : ℤ}

/-- **A nonnegative log-concave sequence has no strict local minimum.** -/
theorem not_lt_of_logConcave {f : ℤ → ℝ} {j : ℤ} (hnn : ∀ n, 0 ≤ f n)
    (hlc : f (j - 1) * f (j + 1) ≤ f j * f j) :
    ¬(f j < f (j - 1) ∧ f j < f (j + 1)) := by
  rintro ⟨h1, h2⟩
  have hj := hnn j
  have hpos : 0 < f (j + 1) := lt_of_le_of_lt hj h2
  have hstep : f j * f j < f (j - 1) * f (j + 1) := by
    have hA : f j * f (j + 1) < f (j - 1) * f (j + 1) :=
      mul_lt_mul_of_pos_right h1 hpos
    have hB : f j * f j ≤ f j * f (j + 1) := mul_le_mul_of_nonneg_left h2.le hj
    linarith
  linarith

/-- **The sign of the leave-one-out difference at a tie.**

The tie forces `(1-p_i)(b_{i,k}-b_{i,k+1}) = p_i(b_{i,k}-b_{i,k-1})`, so a negative difference would
make `b_{i,k}` a strict local minimum. -/
theorem nonneg_of_tie (hp0 : ∀ i ∈ s, 0 ≤ p i) (hp1 : ∀ i ∈ s, p i ≤ 1)
    (hbnn : ∀ i ∈ s, ∀ j, 0 ≤ b i j)
    (hrec : ∀ i ∈ s, ∀ j, a j = (1 - p i) * b i j + p i * b i (j - 1))
    (hlc : ∀ i ∈ s, ∀ j, b i (j - 1) * b i (j + 1) ≤ b i j * b i j)
    (htie : a k = a (k + 1)) :
    ∀ i ∈ s, 0 ≤ p i * (b i k - b i (k - 1)) := by
  intro i hi
  have hp0i := hp0 i hi
  have hp1i := hp1 i hi
  -- the tie identity
  have hid : (1 - p i) * (b i k - b i (k + 1)) = p i * (b i k - b i (k - 1)) := by
    have h1 := hrec i hi k
    have h2 := hrec i hi (k + 1)
    have h3 : k + 1 - 1 = k := by simp
    rw [h3] at h2
    rw [h1, h2] at htie
    linarith
  rcases eq_or_lt_of_le hp0i with hz | hzpos
  · rw [← hz]; simp
  rcases eq_or_lt_of_le hp1i with ho | holt
  · -- `p i = 1`: the recursion collapses and the difference is exactly `a (k+1) - a k = 0`
    rw [ho]
    have h1 := hrec i hi k
    have h2 := hrec i hi (k + 1)
    have h3 : k + 1 - 1 = k := by simp
    rw [h3] at h2
    rw [ho] at h1 h2
    simp only [sub_self, zero_mul, zero_add, one_mul] at h1 h2
    rw [h1, h2] at htie
    simp only [one_mul]
    linarith
  · -- `0 < p i < 1`: log-concavity of `b i` forbids a strict local minimum
    by_contra hcon
    rw [not_le] at hcon
    have hq : 0 < 1 - p i := by linarith
    have hD : b i k - b i (k - 1) < 0 := by
      rcases le_or_gt 0 (b i k - b i (k - 1)) with h | h
      · exact absurd (mul_nonneg hp0i h) (not_le.2 hcon)
      · exact h
    have hE : b i k - b i (k + 1) < 0 := by
      have h1 : (1 - p i) * (b i k - b i (k + 1)) < 0 := by
        rw [hid]
        exact mul_neg_of_pos_of_neg hzpos hD
      rcases le_or_gt 0 (b i k - b i (k + 1)) with h | h
      · exact absurd (mul_nonneg hq.le h) (not_le.2 h1)
      · exact h
    exact not_lt_of_logConcave (fun n => hbnn i hi n) (hlc i hi k) ⟨by linarith, by linarith⟩

/-- **The upward half of the tie inequality**: `\sum_ip_i \le k+1`. -/
theorem sum_le_of_tie (hp0 : ∀ i ∈ s, 0 ≤ p i) (hp1 : ∀ i ∈ s, p i ≤ 1)
    (hbnn : ∀ i ∈ s, ∀ j, 0 ≤ b i j)
    (hrec : ∀ i ∈ s, ∀ j, a j = (1 - p i) * b i j + p i * b i (j - 1))
    (hlc : ∀ i ∈ s, ∀ j, b i (j - 1) * b i (j + 1) ≤ b i j * b i j)
    (hcountUp : ((k : ℝ) + 1) * a (k + 1) = ∑ i ∈ s, p i * b i k)
    (htie : a k = a (k + 1)) (hpos : 0 < a k) :
    ∑ i ∈ s, p i ≤ (k : ℝ) + 1 := by
  have hsign := nonneg_of_tie hp0 hp1 hbnn hrec hlc htie
  -- `b i k - a (k+1) = p i * (b i k - b i (k-1))`, exactly
  have hshift : ∀ i ∈ s, p i * b i k - p i * a (k + 1) = p i * (p i * (b i k - b i (k - 1))) := by
    intro i hi
    have h1 := hrec i hi k
    rw [← htie, h1]
    ring
  have hsum : ((k : ℝ) + 1) * a (k + 1) - (∑ i ∈ s, p i) * a (k + 1)
      = ∑ i ∈ s, p i * (p i * (b i k - b i (k - 1))) := by
    rw [hcountUp, Finset.sum_mul, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i hi => by
      have := hshift i hi
      linarith [this]
  have hnn : 0 ≤ ∑ i ∈ s, p i * (p i * (b i k - b i (k - 1))) :=
    Finset.sum_nonneg fun i hi => mul_nonneg (hp0 i hi) (hsign i hi)
  have hposk : 0 < a (k + 1) := by rw [← htie]; exact hpos
  nlinarith [hsum, hnn, hposk]

/-- **The downward half of the tie inequality**: `k \le \sum_ip_i`.

The same sign, read through the other double-counting identity — the mirror of the first under
`X \mapsto N-X`, `p_i \mapsto 1-p_i`. -/
theorem le_sum_of_tie (hp0 : ∀ i ∈ s, 0 ≤ p i) (hp1 : ∀ i ∈ s, p i ≤ 1)
    (hbnn : ∀ i ∈ s, ∀ j, 0 ≤ b i j)
    (hrec : ∀ i ∈ s, ∀ j, a j = (1 - p i) * b i j + p i * b i (j - 1))
    (hlc : ∀ i ∈ s, ∀ j, b i (j - 1) * b i (j + 1) ≤ b i j * b i j)
    (hcountDown : ((s.card : ℝ) - k) * a k = ∑ i ∈ s, (1 - p i) * b i k)
    (htie : a k = a (k + 1)) (hpos : 0 < a k) :
    (k : ℝ) ≤ ∑ i ∈ s, p i := by
  have hsign := nonneg_of_tie hp0 hp1 hbnn hrec hlc htie
  have hshift : ∀ i ∈ s,
      (1 - p i) * b i k - (1 - p i) * a k
        = (1 - p i) * (p i * (b i k - b i (k - 1))) := by
    intro i hi
    have h1 := hrec i hi k
    rw [h1]
    ring
  have hsum : ((s.card : ℝ) - k) * a k - (∑ i ∈ s, (1 - p i)) * a k
      = ∑ i ∈ s, (1 - p i) * (p i * (b i k - b i (k - 1))) := by
    rw [hcountDown, Finset.sum_mul, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i hi => by
      have := hshift i hi
      linarith [this]
  have hnn : 0 ≤ ∑ i ∈ s, (1 - p i) * (p i * (b i k - b i (k - 1))) :=
    Finset.sum_nonneg fun i hi => mul_nonneg (by linarith [hp1 i hi]) (hsign i hi)
  have hcard : ∑ i ∈ s, (1 - p i) = (s.card : ℝ) - ∑ i ∈ s, p i := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [hcard] at hsum
  nlinarith [hsum, hnn, hpos]

/-- **The tie inequality.**  A tie at `k` puts the mean in `[k, k+1]`. -/
theorem tie_mean_bounds (hp0 : ∀ i ∈ s, 0 ≤ p i) (hp1 : ∀ i ∈ s, p i ≤ 1)
    (hbnn : ∀ i ∈ s, ∀ j, 0 ≤ b i j)
    (hrec : ∀ i ∈ s, ∀ j, a j = (1 - p i) * b i j + p i * b i (j - 1))
    (hlc : ∀ i ∈ s, ∀ j, b i (j - 1) * b i (j + 1) ≤ b i j * b i j)
    (hcountUp : ((k : ℝ) + 1) * a (k + 1) = ∑ i ∈ s, p i * b i k)
    (hcountDown : ((s.card : ℝ) - k) * a k = ∑ i ∈ s, (1 - p i) * b i k)
    (htie : a k = a (k + 1)) (hpos : 0 < a k) :
    (k : ℝ) ≤ ∑ i ∈ s, p i ∧ ∑ i ∈ s, p i ≤ (k : ℝ) + 1 :=
  ⟨le_sum_of_tie hp0 hp1 hbnn hrec hlc hcountDown htie hpos,
    sum_le_of_tie hp0 hp1 hbnn hrec hlc hcountUp htie hpos⟩

/-! ### Pólya frequency sequences of order two -/

/-- A nonnegative sequence is `IsPF2` when every `2\times2` minor of its Toeplitz matrix is
nonnegative.  Taking `i = j` gives ordinary log-concavity; the general form is what makes the class
closed under convolution with a two-point law. -/
def IsPF2 (f : ℤ → ℝ) : Prop := ∀ i j : ℤ, i ≤ j → f (i - 1) * f (j + 1) ≤ f i * f j

/-- Log-concavity is the diagonal case. -/
theorem IsPF2.logConcave {f : ℤ → ℝ} (hf : IsPF2 f) (j : ℤ) :
    f (j - 1) * f (j + 1) ≤ f j * f j := hf j j le_rfl

/-- The point mass at `0` is `IsPF2`. -/
theorem isPF2_deltaZero : IsPF2 (fun j : ℤ => if j = 0 then (1 : ℝ) else 0) := by
  intro i j hij
  have hnn : ∀ n : ℤ, (0 : ℝ) ≤ if n = 0 then (1 : ℝ) else 0 := by
    intro n; split <;> norm_num
  by_cases h1 : i - 1 = 0
  · have hj : j + 1 ≠ 0 := by omega
    simp only [hj, if_false, mul_zero]
    exact mul_nonneg (hnn i) (hnn j)
  · simp only [h1, if_false, zero_mul]
    exact mul_nonneg (hnn i) (hnn j)

/-- **`IsPF2` is closed under convolution with a two-point law.**

The difference of the two products is `c^2T_1+d^2T_2+cdT_3` with `T_1`, `T_2` instances of `IsPF2`
one step apart and `T_3` the composite of two more, which is where the general minor form is used
and plain log-concavity would not suffice. -/
theorem IsPF2.bernConv {f : ℤ → ℝ} (hf : IsPF2 f) {c d : ℝ} (hc : 0 ≤ c) (hd : 0 ≤ d) :
    IsPF2 (fun j => c * f j + d * f (j - 1)) := by
  intro i j hij
  have h1 : f (i - 1) * f (j + 1) ≤ f i * f j := hf i j hij
  have h2 : f (i - 2) * f j ≤ f (i - 1) * f (j - 1) := by
    have h := hf (i - 1) (j - 1) (by omega)
    rw [show i - 1 - 1 = i - 2 by ring, show j - 1 + 1 = j by ring] at h
    exact h
  have h3 : f (i - 2) * f (j + 1) ≤ f (i - 1) * f j := by
    have h := hf (i - 1) j (by omega)
    rw [show i - 1 - 1 = i - 2 by ring] at h
    exact h
  have h4 : f (i - 1) * f j ≤ f i * f (j - 1) := by
    rcases eq_or_lt_of_le hij with h | h
    · rw [← h]
      exact le_of_eq (by ring)
    · have h' := hf i (j - 1) (by omega)
      rw [show j - 1 + 1 = j by ring] at h'
      exact h'
  have hT3 : f (i - 2) * f (j + 1) ≤ f i * f (j - 1) := h3.trans h4
  simp only [show i - 1 - 1 = i - 2 by ring, show j + 1 - 1 = j by ring]
  nlinarith [mul_le_mul_of_nonneg_left h1 (mul_nonneg hc hc),
    mul_le_mul_of_nonneg_left h2 (mul_nonneg hd hd),
    mul_le_mul_of_nonneg_left hT3 (mul_nonneg hc hd)]

/-! ### The Poisson binomial mass function -/

section construction

open Polynomial

/-- The generating polynomial `\prod_{i\in s}(1-p_i+p_iz)`. -/
noncomputable def pbPoly (s : Finset ι) (p : ι → ℝ) : Polynomial ℝ :=
  ∏ i ∈ s, (C (1 - p i) + C (p i) * X)

/-- The mass function of `\sum_{i\in s}\mathrm{Bernoulli}(p_i)`, indexed by `ℤ` so that the
Bernoulli recursion's `j-1` is honest subtraction. -/
noncomputable def pbPmf (s : Finset ι) (p : ι → ℝ) (j : ℤ) : ℝ :=
  if 0 ≤ j then (pbPoly s p).coeff j.toNat else 0

theorem pbPmf_of_neg (s : Finset ι) (p : ι → ℝ) {j : ℤ} (hj : j < 0) : pbPmf s p j = 0 := by
  simp [pbPmf, not_le.2 hj]

theorem pbPmf_eq_coeff (s : Finset ι) (p : ι → ℝ) {j : ℤ} (hj : 0 ≤ j) :
    pbPmf s p j = (pbPoly s p).coeff j.toNat := by
  simp [pbPmf, hj]

theorem pbPoly_empty (p : ι → ℝ) : pbPoly (∅ : Finset ι) p = 1 := by
  simp [pbPoly]

theorem pbPmf_empty (p : ι → ℝ) (j : ℤ) :
    pbPmf (∅ : Finset ι) p j = if j = 0 then (1 : ℝ) else 0 := by
  rcases lt_or_ge j 0 with hj | hj
  · rw [pbPmf_of_neg _ _ hj, if_neg (by omega)]
  · rw [pbPmf_eq_coeff _ _ hj, pbPoly_empty, Polynomial.coeff_one]
    by_cases h : j = 0
    · simp [h]
    · rw [if_neg h, if_neg (by omega : ¬ j.toNat = 0)]

variable [DecidableEq ι]

theorem pbPoly_erase {s : Finset ι} {i : ι} (hi : i ∈ s) (p : ι → ℝ) :
    pbPoly s p = (C (1 - p i) + C (p i) * X) * pbPoly (s.erase i) p := by
  rw [pbPoly, pbPoly, ← Finset.mul_prod_erase s _ hi]

/-- **The Bernoulli recursion**: removing one variable. -/
theorem pbPmf_rec {s : Finset ι} {i : ι} (hi : i ∈ s) (p : ι → ℝ) (j : ℤ) :
    pbPmf s p j
      = (1 - p i) * pbPmf (s.erase i) p j + p i * pbPmf (s.erase i) p (j - 1) := by
  rcases lt_trichotomy j 0 with hj | hj | hj
  · rw [pbPmf_of_neg _ _ hj, pbPmf_of_neg _ _ hj, pbPmf_of_neg _ _ (by omega : j - 1 < 0)]
    ring
  · subst hj
    rw [pbPmf_of_neg _ _ (by norm_num : (0 : ℤ) - 1 < 0), mul_zero, add_zero,
      pbPmf_eq_coeff _ _ le_rfl, pbPmf_eq_coeff _ _ le_rfl, pbPoly_erase hi p]
    simp
  · obtain ⟨m, hm⟩ : ∃ m : ℕ, j = (m : ℤ) + 1 := ⟨(j - 1).toNat, by omega⟩
    subst hm
    have h0 : ((m : ℤ) + 1) ≥ 0 := by omega
    have h1 : ((m : ℤ) + 1 - 1) ≥ 0 := by omega
    have hn0 : ((m : ℤ) + 1).toNat = m + 1 := by omega
    have hn1 : ((m : ℤ) + 1 - 1).toNat = m := by omega
    rw [pbPmf_eq_coeff _ _ h0, pbPmf_eq_coeff _ _ h0, pbPmf_eq_coeff _ _ h1, hn0, hn1,
      pbPoly_erase hi p, add_mul, Polynomial.coeff_add, Polynomial.coeff_C_mul, mul_assoc,
      Polynomial.coeff_C_mul, Polynomial.coeff_X_mul]

/-- Nonnegativity. -/
theorem pbPmf_nonneg {p : ι → ℝ} (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1) (s : Finset ι) :
    ∀ j : ℤ, 0 ≤ pbPmf s p j := by
  induction s using Finset.induction_on with
  | empty =>
      intro j
      rw [pbPmf_empty]
      split <;> norm_num
  | insert i t hit ih =>
      intro j
      have hi : i ∈ insert i t := Finset.mem_insert_self i t
      have herase : (insert i t).erase i = t := Finset.erase_insert hit
      rw [pbPmf_rec hi p j, herase]
      have hp := hp0 i
      have hq := hp1 i
      have ha := ih j
      have hb := ih (j - 1)
      nlinarith

/-- **`IsPF2` for the Poisson binomial**, hence log-concavity of its mass function. -/
theorem pbPmf_isPF2 {p : ι → ℝ} (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1) (s : Finset ι) :
    IsPF2 (pbPmf s p) := by
  induction s using Finset.induction_on with
  | empty =>
      have h : pbPmf (∅ : Finset ι) p = fun j : ℤ => if j = 0 then (1 : ℝ) else 0 :=
        funext (pbPmf_empty p)
      rw [h]
      exact isPF2_deltaZero
  | insert i t hit ih =>
      have hi : i ∈ insert i t := Finset.mem_insert_self i t
      have herase : (insert i t).erase i = t := Finset.erase_insert hit
      have hfun : pbPmf (insert i t) p
          = fun j : ℤ => (1 - p i) * pbPmf t p j + p i * pbPmf t p (j - 1) := by
        funext j
        rw [pbPmf_rec hi p j, herase]
      rw [hfun]
      exact ih.bernConv (by linarith [hp1 i]) (hp0 i)

/-- **The upward double-counting identity** `(j+1)a_{j+1} = \sum_ip_ib_{i,j}`, which is the product
rule for the generating polynomial read off one coefficient. -/
theorem pbPmf_countUp (p : ι → ℝ) (s : Finset ι) (j : ℤ) :
    ((j : ℝ) + 1) * pbPmf s p (j + 1) = ∑ i ∈ s, p i * pbPmf (s.erase i) p j := by
  have hder : Polynomial.derivative (pbPoly s p)
      = ∑ i ∈ s, C (p i) * pbPoly (s.erase i) p := by
    rw [pbPoly, Polynomial.derivative_prod_finset]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Polynomial.derivative_add, Polynomial.derivative_C, Polynomial.derivative_C_mul,
      Polynomial.derivative_X, zero_add, mul_one, pbPoly]
    ring
  rcases lt_trichotomy j (-1) with hj | hj | hj
  · rw [pbPmf_of_neg _ _ (by omega : j + 1 < 0)]
    rw [Finset.sum_congr rfl fun i _ => by rw [pbPmf_of_neg _ _ (by omega : j < 0)]]
    simp
  · subst hj
    rw [Finset.sum_congr rfl fun i _ => by rw [pbPmf_of_neg _ _ (by norm_num : (-1 : ℤ) < 0)]]
    simp
  · obtain ⟨n, hn⟩ : ∃ n : ℕ, j = (n : ℤ) := ⟨j.toNat, by omega⟩
    subst hn
    have h0 : ((n : ℤ)) ≥ 0 := by omega
    have h1 : ((n : ℤ) + 1) ≥ 0 := by omega
    have hn0 : ((n : ℤ)).toNat = n := by omega
    have hn1 : ((n : ℤ) + 1).toNat = n + 1 := by omega
    have hcoeff := congrArg (fun q : Polynomial ℝ => q.coeff n) hder
    simp only [Polynomial.coeff_derivative, Polynomial.finsetSum_coeff,
      Polynomial.coeff_C_mul] at hcoeff
    rw [pbPmf_eq_coeff _ _ h1, hn1]
    rw [Finset.sum_congr rfl fun i _ => by rw [pbPmf_eq_coeff _ _ h0, hn0]]
    rw [← hcoeff]
    push_cast
    ring

/-- **The downward double-counting identity**, from the upward one and the recursion. -/
theorem pbPmf_countDown {p : ι → ℝ} (s : Finset ι) (k : ℤ) :
    ((s.card : ℝ) - k) * pbPmf s p k = ∑ i ∈ s, (1 - p i) * pbPmf (s.erase i) p k := by
  have hup := pbPmf_countUp p s (k - 1)
  rw [show k - 1 + 1 = k by ring] at hup
  have hcast : (((k - 1 : ℤ) : ℝ)) + 1 = (k : ℝ) := by push_cast; ring
  rw [hcast] at hup
  have hsplit : ∑ i ∈ s, (1 - p i) * pbPmf (s.erase i) p k
      = ∑ i ∈ s, (pbPmf s p k - p i * pbPmf (s.erase i) p (k - 1)) := by
    refine Finset.sum_congr rfl fun i hi => ?_
    have h := pbPmf_rec hi p k
    linarith
  rw [hsplit, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, ← hup]
  ring

/-- **The tie inequality for the Poisson binomial.**  A tie `a_k = a_{k+1} > 0` puts the mean
`\sum_ip_i` in `[k,k+1]`. -/
theorem pbPmf_tie_mean_bounds {p : ι → ℝ} (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    {s : Finset ι} {k : ℤ} (htie : pbPmf s p k = pbPmf s p (k + 1))
    (hpos : 0 < pbPmf s p k) :
    (k : ℝ) ≤ ∑ i ∈ s, p i ∧ ∑ i ∈ s, p i ≤ (k : ℝ) + 1 :=
  tie_mean_bounds (b := fun i => pbPmf (s.erase i) p)
    (fun i _ => hp0 i) (fun i _ => hp1 i)
    (fun _i _ j => pbPmf_nonneg hp0 hp1 _ j)
    (fun _i hi j => pbPmf_rec hi p j)
    (fun i _ j => (pbPmf_isPF2 hp0 hp1 (s.erase i)).logConcave j)
    (pbPmf_countUp p s k) (pbPmf_countDown s k) htie hpos

end construction

/-! ### Exponential tilting, and Darroch's theorem -/

section tilting

open Polynomial

/-- The tilted parameters.  Tilting a Poisson binomial by `t` gives another one, with
`p_i \mapsto p_it/(1-p_i+p_it)`. -/
noncomputable def pbTilt (p : ι → ℝ) (t : ℝ) (i : ι) : ℝ := p i * t / (1 - p i + p i * t)

theorem pbDenom_pos {p : ι → ℝ} {t : ℝ} {i : ι} (ht : 0 < t) (hp0 : 0 ≤ p i)
    (hp1 : p i ≤ 1) :
    0 < 1 - p i + p i * t := by
  rcases eq_or_lt_of_le hp1 with h | h
  · rw [h]; simpa using ht
  · have : 0 < 1 - p i := by linarith
    have : 0 ≤ p i * t := mul_nonneg hp0 ht.le
    linarith

theorem pbTilt_nonneg {p : ι → ℝ} {t : ℝ} (ht : 0 < t) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    (i : ι) : 0 ≤ pbTilt p t i :=
  div_nonneg (mul_nonneg (hp0 i) ht.le) (pbDenom_pos ht (hp0 i) (hp1 i)).le

theorem pbTilt_le_one {p : ι → ℝ} {t : ℝ} (ht : 0 < t) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    (i : ι) : pbTilt p t i ≤ 1 := by
  rw [pbTilt, div_le_one₀ (pbDenom_pos ht (hp0 i) (hp1 i))]
  linarith [hp1 i]

theorem pbTilt_le {p : ι → ℝ} {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (hp0 : ∀ i, 0 ≤ p i)
    (hp1 : ∀ i, p i ≤ 1) (i : ι) : pbTilt p t i ≤ p i := by
  have hd := pbDenom_pos ht (hp0 i) (hp1 i)
  rw [pbTilt, div_le_iff₀ hd]
  nlinarith [mul_nonneg (mul_nonneg (hp0 i) (sub_nonneg.2 (hp1 i))) (sub_nonneg.2 ht1)]

/-- Equality in `pbTilt_le` forces `p_i \in \{0,1\}` when `t < 1`. -/
theorem pbTilt_eq_imp {p : ι → ℝ} {t : ℝ} {i : ι} (ht : 0 < t) (ht1 : t < 1) (hp0 : 0 ≤ p i)
    (hp1 : p i ≤ 1) (heq : pbTilt p t i = p i) : p i * (1 - p i) = 0 := by
  have hd := pbDenom_pos ht hp0 hp1
  rw [pbTilt, div_eq_iff (ne_of_gt hd)] at heq
  have hfac : p i * (1 - p i) * (t - 1) = 0 := by linarith [heq]
  rcases mul_eq_zero.1 hfac with h | h
  · exact h
  · exact absurd h (by linarith)

theorem pbPoly_eval_pos {p : ι → ℝ} {t : ℝ} (ht : 0 < t) (hp0 : ∀ i, 0 ≤ p i)
    (hp1 : ∀ i, p i ≤ 1) (s : Finset ι) : 0 < (pbPoly s p).eval t := by
  rw [pbPoly, Polynomial.eval_prod]
  refine Finset.prod_pos fun i _ => ?_
  have := pbDenom_pos ht (hp0 i) (hp1 i)
  simpa using this

variable [DecidableEq ι]

/-- **The tilted mass function.**  `a'_j = a_jt^j/f(t)`, so the tilted law is the original weighted
by `t^j` and renormalized — which is what makes a tie constructible at any prescribed ratio. -/
theorem pbPmf_tilt {p : ι → ℝ} {t : ℝ} (ht : 0 < t) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    (s : Finset ι) : ∀ j : ℤ,
    pbPmf s (pbTilt p t) j * (pbPoly s p).eval t = pbPmf s p j * t ^ j := by
  have htne : t ≠ 0 := ne_of_gt ht
  induction s using Finset.induction_on with
  | empty =>
      intro j
      rw [pbPoly_empty, Polynomial.eval_one, mul_one, pbPmf_empty, pbPmf_empty]
      by_cases h : j = 0
      · simp [h]
      · simp [h]
  | insert i u hiu ih =>
      intro j
      have hi : i ∈ insert i u := Finset.mem_insert_self i u
      have herase : (insert i u).erase i = u := Finset.erase_insert hiu
      have hq : pbTilt p t i * (1 - p i + p i * t) = p i * t := by
        rw [pbTilt, div_mul_cancel₀ _ (ne_of_gt (pbDenom_pos ht (hp0 i) (hp1 i)))]
      have hq' : (1 - pbTilt p t i) * (1 - p i + p i * t) = 1 - p i := by
        have := hq
        ring_nf
        ring_nf at this
        linarith [this]
      have heval : (pbPoly (insert i u) p).eval t
          = (1 - p i + p i * t) * (pbPoly u p).eval t := by
        rw [pbPoly_erase hi p, herase, Polynomial.eval_mul]
        simp
      rw [pbPmf_rec (i := i) hi (pbTilt p t) j, pbPmf_rec (i := i) hi p j, herase, heval]
      have h1 := ih j
      have h2 := ih (j - 1)
      have hz : t ^ (j - 1) * t = t ^ j := by
        rw [zpow_sub_one₀ htne, mul_assoc, inv_mul_cancel₀ htne, mul_one]
      calc ((1 - pbTilt p t i) * pbPmf u (pbTilt p t) j
              + pbTilt p t i * pbPmf u (pbTilt p t) (j - 1))
            * ((1 - p i + p i * t) * (pbPoly u p).eval t)
          = (1 - pbTilt p t i) * (1 - p i + p i * t)
              * (pbPmf u (pbTilt p t) j * (pbPoly u p).eval t)
            + pbTilt p t i * (1 - p i + p i * t)
              * (pbPmf u (pbTilt p t) (j - 1) * (pbPoly u p).eval t) := by ring
        _ = (1 - p i) * (pbPmf u p j * t ^ j) + p i * t * (pbPmf u p (j - 1) * t ^ (j - 1)) := by
              rw [hq, hq', h1, h2]
        _ = ((1 - p i) * pbPmf u p j + p i * pbPmf u p (j - 1)) * t ^ j := by
              rw [← hz]; ring

/-- **Reflection.**  Replacing every `p_i` by `1-p_i` reverses the mass function. -/
theorem pbPmf_reflect {p : ι → ℝ} (s : Finset ι) : ∀ j : ℤ,
    pbPmf s (fun i => 1 - p i) j = pbPmf s p ((s.card : ℤ) - j) := by
  induction s using Finset.induction_on with
  | empty =>
      intro j
      rw [pbPmf_empty, pbPmf_empty]
      simp only [Finset.card_empty, Nat.cast_zero, zero_sub, neg_eq_zero]
  | insert i u hiu ih =>
      intro j
      have hi : i ∈ insert i u := Finset.mem_insert_self i u
      have herase : (insert i u).erase i = u := Finset.erase_insert hiu
      have hcard : ((insert i u).card : ℤ) = (u.card : ℤ) + 1 := by
        rw [Finset.card_insert_of_notMem hiu]
        norm_cast
      rw [pbPmf_rec (i := i) hi (fun i => 1 - p i) j, pbPmf_rec (i := i) hi p _, herase, hcard]
      rw [ih j, ih (j - 1)]
      have e1 : (u.card : ℤ) - j = (u.card : ℤ) + 1 - j - 1 := by ring
      have e2 : (u.card : ℤ) - (j - 1) = (u.card : ℤ) + 1 - j := by ring
      rw [e1, e2]
      ring

/-- **Darroch's theorem, one step**: with an integer mean `M`, the mass at `M+1` does not exceed the
mass at `M`.

The argument is a contradiction by tilting.  If `a_{M+1} > a_M > 0`, tilt by `t = a_M/a_{M+1} < 1`;
the tilted law ties at `(M,M+1)`, so the tie inequality forces its mean to be at least `M`.  But
tilting by `t < 1` never increases any parameter, so the tilted mean is at most `M` — and equality
forces the tilt to be the identity, which forces `t = 1`. -/
theorem pbPmf_succ_le {p : ι → ℝ} (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    {s : Finset ι} {M : ℤ} (hmean : ∑ i ∈ s, p i = (M : ℝ)) (hpos : 0 < pbPmf s p M) :
    pbPmf s p (M + 1) ≤ pbPmf s p M := by
  by_contra hcon
  rw [not_le] at hcon
  have hposS : 0 < pbPmf s p (M + 1) := lt_trans hpos hcon
  set t : ℝ := pbPmf s p M / pbPmf s p (M + 1) with hT
  have ht : 0 < t := div_pos hpos hposS
  have ht1 : t < 1 := by
    rw [hT, div_lt_one hposS]
    exact hcon
  set q : ι → ℝ := pbTilt p t with hQ
  have hq0 : ∀ i, 0 ≤ q i := fun i => pbTilt_nonneg ht hp0 hp1 i
  have hq1 : ∀ i, q i ≤ 1 := fun i => pbTilt_le_one ht hp0 hp1 i
  have hf : 0 < (pbPoly s p).eval t := pbPoly_eval_pos ht hp0 hp1 s
  have hAM := pbPmf_tilt ht hp0 hp1 s M
  have hAM1 := pbPmf_tilt ht hp0 hp1 s (M + 1)
  -- the tilted law ties at `(M, M+1)`
  have htie : pbPmf s q M = pbPmf s q (M + 1) := by
    have hz : t ^ (M + 1) = t ^ M * t := by rw [zpow_add_one₀ (ne_of_gt ht)]
    have hkey : pbPmf s p (M + 1) * t ^ (M + 1) = pbPmf s p M * t ^ M := by
      rw [hz, hT]
      field_simp
    have h1 : pbPmf s q M * (pbPoly s p).eval t
        = pbPmf s q (M + 1) * (pbPoly s p).eval t := by
      rw [hAM, hAM1, hkey]
    exact mul_right_cancel₀ (ne_of_gt hf) h1
  have hqpos : 0 < pbPmf s q M := by
    have hzp : 0 < t ^ M := zpow_pos ht M
    have hprod : 0 < pbPmf s q M * (pbPoly s p).eval t := by
      rw [hAM]; exact mul_pos hpos hzp
    by_contra hnp
    rw [not_lt] at hnp
    have hnn := mul_nonneg (neg_nonneg.2 hnp) hf.le
    nlinarith [hprod, hnn]
  -- the tie inequality, against the pointwise bound
  have hlow := (pbPmf_tie_mean_bounds hq0 hq1 htie hqpos).1
  have hptw : ∀ i ∈ s, q i ≤ p i := fun i _ => pbTilt_le ht ht1.le hp0 hp1 i
  have hsum : ∑ i ∈ s, q i ≤ ∑ i ∈ s, p i := Finset.sum_le_sum hptw
  have heqsum : ∑ i ∈ s, q i = ∑ i ∈ s, p i := by
    rw [hmean] at hsum ⊢
    exact le_antisymm hsum hlow
  have heqi : ∀ i ∈ s, q i = p i :=
    (Finset.sum_eq_sum_iff_of_le hptw).1 heqsum
  -- so the tilt is the identity on `s`, and then `t = 1`
  have hpoly : pbPoly s q = pbPoly s p := by
    rw [pbPoly, pbPoly]
    exact Finset.prod_congr rfl fun i hi => by rw [heqi i hi]
  have hpmf : ∀ j : ℤ, pbPmf s q j = pbPmf s p j := by
    intro j
    rcases lt_or_ge j 0 with hj | hj
    · rw [pbPmf_of_neg _ _ hj, pbPmf_of_neg _ _ hj]
    · rw [pbPmf_eq_coeff _ _ hj, pbPmf_eq_coeff _ _ hj, hpoly]
  rw [hpmf M] at hAM
  rw [hpmf (M + 1)] at hAM1
  have hfM : (pbPoly s p).eval t = t ^ M := mul_left_cancel₀ (ne_of_gt hpos) hAM
  have hone : t = 1 := by
    rw [hfM, zpow_add_one₀ (ne_of_gt ht)] at hAM1
    have hzp : (0 : ℝ) < t ^ M := zpow_pos ht M
    have hc : 0 < pbPmf s p (M + 1) * t ^ M := mul_pos hposS hzp
    have hrw : pbPmf s p (M + 1) * (t ^ M * t) = (pbPmf s p (M + 1) * t ^ M) * t := by ring
    rw [hrw] at hAM1
    have h1 : (pbPmf s p (M + 1) * t ^ M) * 1 = (pbPmf s p (M + 1) * t ^ M) * t := by
      rw [mul_one]; exact hAM1
    exact (mul_left_cancel₀ (ne_of_gt hc) h1).symm
  exact absurd hone (by linarith)

/-- **Darroch's theorem.**  When the mean `\sum_ip_i` is an integer `M`, the mass function of
`\sum_i\mathrm{Bernoulli}(p_i)` is maximized at `M`. -/
theorem pbPmf_le_of_mean_eq {p : ι → ℝ} (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    {s : Finset ι} {M : ℤ} (hmean : ∑ i ∈ s, p i = (M : ℝ)) (hpos : 0 < pbPmf s p M) :
    ∀ j : ℤ, pbPmf s p j ≤ pbPmf s p M := by
  have hpf2 := pbPmf_isPF2 hp0 hp1 s
  have hnn := pbPmf_nonneg hp0 hp1 s
  have hup : pbPmf s p (M + 1) ≤ pbPmf s p M := pbPmf_succ_le hp0 hp1 hmean hpos
  -- the reflected instance gives the step to the left
  have hdown : pbPmf s p (M - 1) ≤ pbPmf s p M := by
    set p' : ι → ℝ := fun i => 1 - p i with hp'
    have hp'0 : ∀ i, 0 ≤ p' i := fun i => by rw [hp']; linarith [hp1 i]
    have hp'1 : ∀ i, p' i ≤ 1 := fun i => by rw [hp']; linarith [hp0 i]
    have hmean' : ∑ i ∈ s, p' i = (((s.card : ℤ) - M : ℤ) : ℝ) := by
      rw [hp', Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one, hmean]
      push_cast
      ring
    have hrefl : ∀ j : ℤ, pbPmf s p' j = pbPmf s p ((s.card : ℤ) - j) := pbPmf_reflect s
    have hpos' : 0 < pbPmf s p' ((s.card : ℤ) - M) := by
      rw [hrefl]
      have : (s.card : ℤ) - ((s.card : ℤ) - M) = M := by ring
      rw [this]
      exact hpos
    have h := pbPmf_succ_le hp'0 hp'1 hmean' hpos'
    rw [hrefl, hrefl] at h
    have e1 : (s.card : ℤ) - ((s.card : ℤ) - M + 1) = M - 1 := by ring
    have e2 : (s.card : ℤ) - ((s.card : ℤ) - M) = M := by ring
    rw [e1, e2] at h
    exact h
  -- and log-concavity spreads both steps
  have hstepR : ∀ n : ℕ, pbPmf s p (M + (n : ℤ) + 1) ≤ pbPmf s p (M + (n : ℤ)) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simpa using hup
    · have hpf := hpf2 (M + 1) (M + (n : ℤ)) (by omega)
      rw [show M + 1 - 1 = M by ring] at hpf
      have hj := hnn (M + (n : ℤ))
      have hchain : pbPmf s p M * pbPmf s p (M + (n : ℤ) + 1)
          ≤ pbPmf s p M * pbPmf s p (M + (n : ℤ)) := by
        have h2 := mul_le_mul_of_nonneg_right hup hj
        linarith [hpf, h2]
      exact le_of_mul_le_mul_left hchain hpos
  have hright : ∀ n : ℕ, pbPmf s p (M + (n : ℤ)) ≤ pbPmf s p M := by
    intro n
    induction n with
    | zero => simp
    | succ m ihm =>
        have hc : ((m + 1 : ℕ) : ℤ) = (m : ℤ) + 1 := by push_cast; ring
        rw [hc, ← add_assoc]
        exact le_trans (hstepR m) ihm
  have hstepL : ∀ n : ℕ, pbPmf s p (M - (n : ℤ) - 1) ≤ pbPmf s p (M - (n : ℤ)) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simpa using hdown
    · have hpf := hpf2 (M - (n : ℤ)) (M - 1) (by omega)
      rw [show M - 1 + 1 = M by ring] at hpf
      have hj := hnn (M - (n : ℤ))
      have hchain : pbPmf s p (M - (n : ℤ) - 1) * pbPmf s p M
          ≤ pbPmf s p (M - (n : ℤ)) * pbPmf s p M := by
        have h2 := mul_le_mul_of_nonneg_left hdown hj
        linarith [hpf, h2]
      exact le_of_mul_le_mul_right hchain hpos
  have hleft : ∀ n : ℕ, pbPmf s p (M - (n : ℤ)) ≤ pbPmf s p M := by
    intro n
    induction n with
    | zero => simp
    | succ m ihm =>
        have hc : ((m + 1 : ℕ) : ℤ) = (m : ℤ) + 1 := by push_cast; ring
        rw [hc, ← sub_sub]
        exact le_trans (hstepL m) ihm
  intro j
  rcases le_or_gt M j with hj | hj
  · obtain ⟨n, hn⟩ : ∃ n : ℕ, j = M + (n : ℤ) := ⟨(j - M).toNat, by omega⟩
    rw [hn]
    exact hright n
  · obtain ⟨n, hn⟩ : ∃ n : ℕ, j = M - (n : ℤ) := ⟨(M - j).toNat, by omega⟩
    rw [hn]
    exact hleft n

end tilting

end Shields
