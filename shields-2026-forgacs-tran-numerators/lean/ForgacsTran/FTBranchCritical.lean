/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib

/-!
# Zeros of the critical polynomial

`Forgacs2017RationalDenominator` Lemma 5 concerns
`R(t) = t^{2r} (d/dt)(-P(t)/t^r) = r t^{r-1} P(t) - t^r P'(t)`, which up to the
factor `-t^{r-1}` is the polynomial `E(t) = t P'(t) - r P(t)` that `Geometry`
carries as `ftCritical`.

## Main statements

* `ftCriticalReal` — `E` over `ℝ`, and `hasDerivAt_ftRatio`, the identity
  `(P/t^r)' = E/t^{r+1}` that makes `E` the critical polynomial.
* `exists_ftCriticalReal_root_between` — Rolle: between two positive zeros of `P`
  there is a zero of `E`.
* `existsUnique_neg_root_ftCriticalReal` — the second half of their Lemma 5: for
  `r = 1` and `deg P ≥ 2`, `E` has exactly one negative zero.

## Implementation notes

Sorry-free.

## References

Formalizes `Forgacs2017RationalDenominator` Lemmas 2--5, the branch
`thm:FT-geometry` imports.

## Tags

critical polynomial, denominator pencil, zeros
-/

namespace ForgacsTran

open Real Set Polynomial

/-- `E(t) = t P'(t) - r P(t)`, over `ℝ`. -/
noncomputable def ftCriticalReal (P : Polynomial ℝ) (r : ℕ) : Polynomial ℝ :=
  X * derivative P - C (r : ℝ) * P

@[simp] theorem eval_ftCriticalReal (P : Polynomial ℝ) (r : ℕ) (t : ℝ) :
    (ftCriticalReal P r).eval t = t * (derivative P).eval t - r * P.eval t := by
  simp [ftCriticalReal]

/-- `P(t) = c ∏_k (τ_k - t)` over `ℝ`. -/
noncomputable def ftRootPolyReal {n : ℕ} (c : ℝ) (a : Fin n → ℝ) : Polynomial ℝ :=
  C c * ∏ k, (C (a k) - X)

@[simp] theorem eval_ftRootPolyReal {n : ℕ} (c : ℝ) (a : Fin n → ℝ) (t : ℝ) :
    (ftRootPolyReal c a).eval t = c * ∏ k, (a k - t) := by
  simp [ftRootPolyReal, eval_prod]

/-- `E = t^{r+1} (P/t^r)'`, which is why the zeros of `E` off the origin are the
critical points of the fiber map. -/
theorem hasDerivAt_ftRatio (P : Polynomial ℝ) {r : ℕ} (hr : 1 ≤ r) {t : ℝ} (ht : t ≠ 0) :
    HasDerivAt (fun s => P.eval s / s ^ r) ((ftCriticalReal P r).eval t / t ^ (r + 1)) t := by
  have hpow : t ^ r ≠ 0 := pow_ne_zero _ ht
  have hsplit : t ^ r = t * t ^ (r - 1) := by
    conv_lhs => rw [show r = 1 + (r - 1) by omega]
    rw [pow_add, pow_one]
  have h := (P.hasDerivAt t).div (hasDerivAt_pow r t) hpow
  refine h.congr_deriv ?_
  have h1 : ((t : ℝ) ^ r) ^ 2 ≠ 0 := pow_ne_zero _ hpow
  have h2 : (t : ℝ) ^ r * t ≠ 0 := mul_ne_zero hpow ht
  have hE : (t : ℝ) ^ (r + 1) = t ^ r * t := pow_succ t r
  rw [eval_ftCriticalReal, hE, div_eq_div_iff h1 h2, hsplit]
  ring

/-- **Rolle between two zeros of `P`.**  This is the step that puts a zero of `E`
in each interval `(τ_k, τ_{k+1})` of `Forgacs2017RationalDenominator` Lemma 5. -/
theorem exists_ftCriticalReal_root_between {P : Polynomial ℝ} {r : ℕ} (hr : 1 ≤ r) {x y : ℝ}
    (hx : 0 < x) (hxy : x < y) (hPx : P.eval x = 0) (hPy : P.eval y = 0) :
    ∃ ξ ∈ Ioo x y, (ftCriticalReal P r).eval ξ = 0 := by
  have hne : ∀ s ∈ Icc x y, s ≠ 0 := fun s hs => ne_of_gt (lt_of_lt_of_le hx hs.1)
  have hcont : ContinuousOn (fun s => P.eval s / s ^ r) (Icc x y) := by
    refine P.continuousOn.div (continuousOn_pow r) fun s hs => pow_ne_zero _ (hne s hs)
  have hval : P.eval x / x ^ r = P.eval y / y ^ r := by rw [hPx, hPy]; simp
  obtain ⟨ξ, hξ, hξ0⟩ := exists_hasDerivAt_eq_zero hxy hcont hval
    (fun s hs => hasDerivAt_ftRatio P hr (hne s (Ioo_subset_Icc_self hs)))
  refine ⟨ξ, hξ, ?_⟩
  have hξpos : (0 : ℝ) < ξ := lt_trans hx hξ.1
  have hp : ξ ^ (r + 1) ≠ 0 := pow_ne_zero _ (ne_of_gt hξpos)
  exact (div_eq_zero_iff.1 hξ0).resolve_right hp

/-- The logarithmic derivative of `∏_k (τ_k - X)`, in cleared form.  Stated over a
field, since the branch argument needs it over `ℂ` as well as over `ℝ`. -/
theorem eval_derivative_prod_sub {K ι : Type*} [Field K] (s : Finset ι)
    (a : ι → K) (t : K) (h : ∀ k ∈ s, a k - t ≠ 0) :
    (derivative (∏ k ∈ s, (C (a k) - X))).eval t
      = -(∑ k ∈ s, 1 / (a k - t)) * ∏ k ∈ s, (a k - t) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
      have hi' : a i - t ≠ 0 := h i (Finset.mem_insert_self i s)
      have hs : ∀ k ∈ s, a k - t ≠ 0 := fun k hk => h k (Finset.mem_insert_of_mem hk)
      have hd1 : (derivative (C (a i) - X)).eval t = -1 := by simp
      have he : (C (a i) - X).eval t = a i - t := by simp
      have hpe : (∏ k ∈ s, (C (a k) - X)).eval t = ∏ k ∈ s, (a k - t) := by
        simp [eval_prod]
      rw [Finset.prod_insert hi, derivative_mul, Finset.sum_insert hi, Finset.prod_insert hi,
        eval_add, eval_mul, eval_mul, hd1, he, ih hs, hpe]
      field

/-- **`Forgacs2017RationalDenominator` Lemma 5, the negative zero.**  For `r = 1`
and `deg P ≥ 2`, `E` has exactly one negative zero — equivalently, so does their
`R(t) = P(t) - t P'(t) = -E(t)`. -/
theorem existsUnique_neg_root_ftCriticalReal {n : ℕ} {c : ℝ} {a : Fin n → ℝ}
    (hn : 2 ≤ n) (hc : c ≠ 0) (ha : ∀ k, 0 < a k) :
    ∃! t : ℝ, t < 0 ∧ (ftCriticalReal (ftRootPolyReal c a) 1).eval t = 0 := by
  classical
  set G : ℝ → ℝ := fun t => (∑ k, t / (a k - t)) + 1 with hG
  have hane : ∀ (t : ℝ), t ≤ 0 → ∀ k, a k - t ≠ 0 := fun t ht k => by
    have := ha k; intro hh; linarith [sub_eq_zero.1 hh]
  have hPne : ∀ t : ℝ, t ≤ 0 → (ftRootPolyReal c a).eval t ≠ 0 := by
    intro t ht
    rw [eval_ftRootPolyReal]
    exact mul_ne_zero hc (Finset.prod_ne_zero_iff.2 fun k _ => hane t ht k)
  -- `E = -P · G` on `t ≤ 0`
  have hfac : ∀ t : ℝ, t ≤ 0 →
      (ftCriticalReal (ftRootPolyReal c a) 1).eval t = -((ftRootPolyReal c a).eval t) * G t := by
    intro t ht
    have hd : (derivative (ftRootPolyReal c a)).eval t
        = -c * ((∑ k, 1 / (a k - t)) * ∏ k, (a k - t)) := by
      rw [ftRootPolyReal, derivative_mul, derivative_C, zero_mul, zero_add, eval_mul, eval_C,
        eval_derivative_prod_sub _ a t fun k _ => hane t ht k]
      ring
    have hsum : ∑ k, t / (a k - t) = t * ∑ k, 1 / (a k - t) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by rw [mul_one_div]
    rw [eval_ftCriticalReal, hd, eval_ftRootPolyReal, hG]
    simp only [hsum]
    push_cast
    ring
  -- `G` is strictly increasing on `(-∞, 0]`
  have hmono : ∀ x y : ℝ, x < y → y ≤ 0 → G x < G y := by
    intro x y hxy hy0
    have hx0 : x ≤ 0 := le_of_lt (lt_of_lt_of_le hxy hy0)
    have hlt : (∑ k, x / (a k - x)) < ∑ k, y / (a k - y) := by
      refine Finset.sum_lt_sum_of_nonempty
        (Finset.univ_nonempty_iff.2 (Fin.pos_iff_nonempty.1 (by omega))) ?_
      intro k _
      have hax : 0 < a k - x := by linarith [ha k]
      have hay : 0 < a k - y := by linarith [ha k]
      rw [div_lt_div_iff₀ hax hay]
      nlinarith [ha k]
    simp only [hG]
    linarith
  -- an explicit point where `G` is negative
  have hSpos : 0 < ∑ k, a k :=
    Finset.sum_pos (fun k _ => ha k)
      (Finset.univ_nonempty_iff.2 (Fin.pos_iff_nonempty.1 (by omega)))
  have hM : G (-(2 * ∑ k, a k)) < 0 := by
    have hterm : ∀ k : Fin n, (-(2 * ∑ j, a j)) / (a k - -(2 * ∑ j, a j)) ≤ -(2 / 3) := by
      intro k
      have hak : a k ≤ ∑ j, a j :=
        Finset.single_le_sum (f := a) (fun i _ => (ha i).le) (Finset.mem_univ k)
      have hpos : 0 < a k + 2 * ∑ j, a j := by linarith [ha k]
      rw [show a k - -(2 * ∑ j, a j) = a k + 2 * ∑ j, a j by ring, div_le_iff₀ hpos]
      linarith
    have hsum := Finset.sum_le_sum (fun k (_ : k ∈ Finset.univ) => hterm k)
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
    have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
    simp only [hG]
    linarith
  have hG0 : G 0 = 1 := by simp [hG]
  -- a zero of `G` in `(-M, 0)`
  have hcontG : ContinuousOn G (Icc (-(2 * ∑ k, a k)) 0) := by
    refine ContinuousOn.add (continuousOn_finsetSum _ fun k _ => ?_) continuousOn_const
    exact continuousOn_id.div (continuousOn_const.sub continuousOn_id)
      fun t ht => hane t ht.2 k
  obtain ⟨t₀, ht₀mem, ht₀⟩ := intermediate_value_Icc
    (by linarith : -(2 * ∑ k, a k) ≤ (0 : ℝ)) hcontG
    ⟨hM.le, by rw [hG0]; norm_num⟩
  have ht₀neg : t₀ < 0 := by
    rcases lt_or_eq_of_le ht₀mem.2 with h | h
    · exact h
    · rw [h, hG0] at ht₀; norm_num at ht₀
  refine ⟨t₀, ⟨ht₀neg, by rw [hfac t₀ ht₀neg.le, ht₀, mul_zero]⟩, ?_⟩
  rintro s ⟨hsneg, hs⟩
  have hGs : G s = 0 := by
    have h1 := hfac s hsneg.le
    rw [hs] at h1
    have hP := hPne s hsneg.le
    have h2 : (ftRootPolyReal c a).eval s * G s = 0 := by linear_combination h1
    rcases mul_eq_zero.1 h2 with h | h
    · exact absurd h hP
    · exact h
  rcases lt_trichotomy s t₀ with h | h | h
  · exact absurd (hmono s t₀ h ht₀neg.le) (by rw [hGs, ht₀]; exact lt_irrefl 0)
  · exact h
  · exact absurd (hmono t₀ s h hsneg.le) (by rw [hGs, ht₀]; exact lt_irrefl 0)

end ForgacsTran
