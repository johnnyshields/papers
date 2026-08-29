/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib.Analysis.Complex.TaylorSeries
import Shields.Analysis.Complex.HadamardRigidity
import Shields.Analysis.Complex.ValueDistribution.MaxModulus
import Shields.Analysis.Complex.ValueDistribution.Nevanlinna

/-!
# Polynomial growth forces a polynomial

`Shields.iteratedDeriv_eq_zero_of_re_growth` annihilates the `n`-th derivative of an entire `g`
whose real part on the ball of radius `S` is bounded by an `M S` with `M S / S ^ n → 0`, so such a
`g` is a polynomial of degree less than `n`.  At `n = 2` that is `Shields.eq_affine_of_re_growth`;
what the Edrei argument needs is `n = 3`, where the conclusion is a quadratic and an odd function
is therefore linear.

The other half of this file is where the majorant comes from.  The Nevanlinna characteristic of
`e^g` at radius `2S` bounds `\Re g` on the ball of radius `S`, so an order below three — or an
exponent of convergence below three for the `(-1)`-points — is all a caller has to produce.

## Main results

* `Shields.eq_sum_range_of_iteratedDeriv_eq_zero` — an entire function with vanishing `n`-th
  derivative is its Taylor polynomial of degree below `n`.
* `Shields.eq_quadratic_of_re_growth` — subcubic growth makes `g` a quadratic polynomial.
* `Shields.odd_eq_linear_of_re_growth` — an odd such `g` is linear.
* `Shields.isLittleO_rpow_pow_atTop` — `S ^ q` is `o(S ^ n)` at infinity when `q < n`.
* `Shields.odd_eq_linear_of_order_lt_three` — an odd entire `g` with `exp ∘ g` of order below three
  is linear, three being the exponent the rigidity step allows.
* `Shields.odd_eq_linear_of_order_le_two` — its order-two case.
* `Shields.odd_eq_linear_of_expConvergence_lt_three` — the same conclusion straight from the
  exponent of convergence of the `(-1)`-points of `exp ∘ g`.
* `Shields.odd_eq_linear_of_expConvergence_le_two` — its exponent-two case.

## Tags

Hadamard factorization, order of growth, Nevanlinna characteristic, value distribution
-/

open Asymptotics Complex Filter Metric Real Set ValueDistribution
open scoped ENNReal NNReal Topology

namespace Shields

variable {g : ℂ → ℂ} {M : ℝ → ℝ}

/-! ### Truncation of the Taylor series -/

/-- **An entire function whose `n`-th derivative vanishes identically is its own Taylor polynomial
of degree below `n`.**  Every derivative from the `n`-th on is then identically zero, so the Taylor
series about any center `c` has only its first `n` terms. -/
theorem eq_sum_range_of_iteratedDeriv_eq_zero {f : ℂ → ℂ} {n : ℕ} (hf : Differentiable ℂ f)
    (h : ∀ w, iteratedDeriv n f w = 0) (c z : ℂ) :
    f z = ∑ k ∈ Finset.range n, (k.factorial : ℂ)⁻¹ * iteratedDeriv k f c * (z - c) ^ k := by
  have hiter : deriv^[n] f = fun _ : ℂ ↦ (0 : ℂ) := by
    funext w
    have := h w
    rwa [iteratedDeriv_eq_iterate] at this
  have hvanish : ∀ k, n ≤ k → iteratedDeriv k f c = 0 := by
    intro k hk
    obtain ⟨m, rfl⟩ : ∃ m, k = m + n := ⟨k - n, by omega⟩
    rw [iteratedDeriv_eq_iterate, Function.iterate_add_apply, hiter, ← iteratedDeriv_eq_iterate]
    exact iteratedDeriv_fun_const_zero
  rw [← Complex.taylorSeries_eq_of_entire' (c := c) (z := z) hf,
    tsum_eq_sum (s := Finset.range n) fun k hk ↦ by
      rw [hvanish k (by simpa using hk)]; ring]

/-! ### Subcubic growth forces a quadratic -/

/-- **Subcubic growth of `\Re g` makes `g` a quadratic polynomial.** -/
theorem eq_quadratic_of_re_growth (hg : Differentiable ℂ g) (hMpos : ∀ S, 0 < M S)
    (hbound : ∀ S : ℝ, 0 < S → ∀ z ∈ ball (0 : ℂ) S, (g z).re ≤ M S)
    (hgrow : Tendsto (fun S : ℝ ↦ M S / S ^ 3) atTop (𝓝 0)) :
    ∀ z, g z = g 0 + deriv g 0 * z + iteratedDeriv 2 g 0 / 2 * z ^ 2 := by
  intro z
  rw [eq_sum_range_of_iteratedDeriv_eq_zero (n := 3) hg
      (iteratedDeriv_eq_zero_of_re_growth (by norm_num) hg hMpos hbound hgrow) 0 z,
    Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
  simp only [iteratedDeriv_zero, iteratedDeriv_one, sub_zero, pow_zero, pow_one,
    Nat.factorial_zero, Nat.factorial_one, Nat.factorial_two, Nat.cast_one, Nat.cast_ofNat,
    inv_one, one_mul, mul_one]
  ring

/-- **An odd entire function of subcubic real-part growth is linear.** -/
theorem odd_eq_linear_of_re_growth (hg : Differentiable ℂ g) (hodd : ∀ z, g (-z) = -g z)
    (hMpos : ∀ S, 0 < M S)
    (hbound : ∀ S : ℝ, 0 < S → ∀ z ∈ ball (0 : ℂ) S, (g z).re ≤ M S)
    (hgrow : Tendsto (fun S : ℝ ↦ M S / S ^ 3) atTop (𝓝 0)) :
    ∀ z, g z = deriv g 0 * z := by
  have hquad := eq_quadratic_of_re_growth hg hMpos hbound hgrow
  have hg0 : g 0 = 0 := by
    have := hodd 0
    simp only [neg_zero] at this
    linear_combination this / 2
  have ha : iteratedDeriv 2 g 0 = 0 := by
    have h1 := hquad 1
    have h2 := hquad (-1)
    have h3 := hodd 1
    rw [h1, h2] at h3
    rw [hg0] at h3
    linear_combination h3
  intro z
  rw [hquad z, hg0, ha]
  ring

/-! ### The value-distribution hypothesis -/

/-- **A power below `n` is `o(S ^ n)`.**  For `0 < q < n`, `S ^ q = o(S ^ n)` at infinity.

Mathlib compares `rpow` against `exp` and against `log`, but carries no comparison of two real
powers of the variable itself. -/
theorem isLittleO_rpow_pow_atTop {q : ℝ} {n : ℕ} (hq0 : 0 < q) (hqn : q < n) :
    (fun S : ℝ ↦ S ^ q) =o[atTop] fun S : ℝ ↦ S ^ n := by
  rw [isLittleO_iff_tendsto fun x hx ↦ ?_]
  · refine (tendsto_rpow_neg_atTop (y := (n : ℝ) - q) (by linarith)).congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with S hS
    rw [← Real.rpow_natCast S n, ← Real.rpow_sub hS]
    congr 1
    ring
  · have hx0 : x = 0 := by
      by_contra hx0
      exact absurd hx (pow_ne_zero n hx0)
    rw [hx0]
    exact Real.zero_rpow hq0.ne'

/-- **A subcubic characteristic gives a subcubic majorant.**  If `T = O(r^q)` with `q < 3`, then
`S ↦ max 0 (3 T(2S)) + 1` is `o(S³)`.

That awkward expression is exactly the majorant `Shields.odd_eq_linear_of_re_growth` consumes, and
each of its three parts is forced: the `2S` because the real-part bound on the ball of radius `S`
is read off the characteristic at radius `2S`, the `max 0` and the `+ 1` because the majorant must
be strictly positive.  None of the three costs an order of growth, which is the only thing that
has to be checked and is what this states. -/
theorem isLittleO_majorant_of_isBigO_rpow {T : ℝ → ℝ} {q : ℝ} (hq0 : 0 < q) (hq3 : q < 3)
    (hO : T =O[atTop] fun r : ℝ ↦ r ^ q) :
    (fun S : ℝ ↦ max 0 (3 * T (2 * S)) + 1) =o[atTop] fun S : ℝ ↦ S ^ 3 := by
  have hbig : (fun S : ℝ ↦ max 0 (3 * T (2 * S)) + 1) =O[atTop] fun S : ℝ ↦ S ^ q := by
    have hT2 : (fun S : ℝ ↦ T (2 * S)) =O[atTop] fun S : ℝ ↦ (2 * S) ^ q :=
      hO.comp_tendsto (Filter.Tendsto.const_mul_atTop two_pos tendsto_id)
    have hscale : (fun S : ℝ ↦ (2 * S) ^ q) =O[atTop] fun S : ℝ ↦ S ^ q := by
      rw [isBigO_iff]
      refine ⟨(2 : ℝ) ^ q, ?_⟩
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with S hS
      rw [Real.mul_rpow (by norm_num) hS, Real.norm_of_nonneg (by positivity),
        Real.norm_of_nonneg (by positivity)]
    have hmax : (fun S : ℝ ↦ max 0 (3 * T (2 * S))) =O[atTop] fun S : ℝ ↦ T (2 * S) := by
      rw [isBigO_iff]
      refine ⟨3, Eventually.of_forall fun S ↦ ?_⟩
      rw [Real.norm_of_nonneg (le_max_left _ _), Real.norm_eq_abs]
      refine max_le (by positivity) ?_
      have := le_abs_self (T (2 * S))
      linarith
    have hone : (fun _ : ℝ ↦ (1 : ℝ)) =O[atTop] fun S : ℝ ↦ S ^ q := by
      rw [isBigO_iff]
      refine ⟨1, ?_⟩
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with S hS
      rw [Real.norm_of_nonneg zero_le_one, one_mul,
        Real.norm_of_nonneg (Real.rpow_nonneg (by linarith) _)]
      exact Real.one_le_rpow hS hq0.le
    exact (hmax.trans (hT2.trans hscale)).add hone
  exact hbig.trans_isLittleO (isLittleO_rpow_pow_atTop hq0 (by exact_mod_cast hq3))

/-- **An odd entire `g` with `e^g` of order below three is linear.**

Fix an exponent `q` strictly between the order and `3`, and above `1` so that `r ^ q` is unbounded.
The characteristic of `e^g` is `O(r^q)`, the Poisson bound turns that into a majorant for `\Re g` on
every ball, and the majorant is subcubic, so `Shields.odd_eq_linear_of_re_growth` applies.  Three is
the ceiling because the rigidity step annihilates the third derivative. -/
theorem odd_eq_linear_of_order_lt_three (hg : Differentiable ℂ g) (hodd : ∀ z, g (-z) = -g z)
    (horder : order (fun z ↦ Complex.exp (g z)) < 3) :
    ∀ z, g z = deriv g 0 * z := by
  obtain ⟨q, hq, hq3⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1
    (max_lt horder (by norm_num : (1 : ℝ≥0∞) < 3))
  have hqorder : order (fun z ↦ Complex.exp (g z)) < q := lt_of_le_of_lt (le_max_left _ _) hq
  have hq1 : (1 : ℝ) < (q : ℝ) := by
    have h : (1 : ℝ≥0∞) < (q : ℝ≥0∞) := lt_of_le_of_lt (le_max_right _ _) hq
    have : (1 : ℝ≥0) < q := by exact_mod_cast h
    exact_mod_cast this
  have hq3' : (q : ℝ) < 3 := by
    have : q < (3 : ℝ≥0) := by exact_mod_cast hq3
    exact_mod_cast this
  set T : ℝ → ℝ := characteristic (fun z ↦ Complex.exp (g z)) ⊤ with hTdef
  have hMpos : ∀ S : ℝ, 0 < max 0 (3 * T (2 * S)) + 1 := fun S ↦ by
    have : (0 : ℝ) ≤ max 0 (3 * T (2 * S)) := le_max_left _ _
    linarith
  have hbound : ∀ S : ℝ, 0 < S → ∀ z ∈ ball (0 : ℂ) S,
      (g z).re ≤ max 0 (3 * T (2 * S)) + 1 := by
    intro S hS z hz
    have h := re_le_characteristic hg hS hz
    rw [← hTdef] at h
    have hle : 3 * T (2 * S) ≤ max 0 (3 * T (2 * S)) := le_max_right _ _
    linarith
  have hlittle : (fun S : ℝ ↦ max 0 (3 * T (2 * S)) + 1) =o[atTop] fun S : ℝ ↦ S ^ 3 :=
    isLittleO_majorant_of_isBigO_rpow (by linarith) hq3'
      (hTdef ▸ isBigO_rpow_of_order_lt hqorder)
  exact odd_eq_linear_of_re_growth hg hodd hMpos hbound hlittle.tendsto_div_nhds_zero

/-- **An odd entire `g` with `e^g` of order at most two is linear.**

The order-two case of `Shields.odd_eq_linear_of_order_lt_three`, which is the one the Edrei argument
reaches through the exponent of convergence of the `(-1)`-points. -/
theorem odd_eq_linear_of_order_le_two (hg : Differentiable ℂ g) (hodd : ∀ z, g (-z) = -g z)
    (horder : order (fun z ↦ Complex.exp (g z)) ≤ 2) :
    ∀ z, g z = deriv g 0 * z :=
  odd_eq_linear_of_order_lt_three hg hodd (lt_of_le_of_lt horder (by norm_num))

/-- **The Edrei input, at any exponent below three.**  If `g` is entire and odd and the
`(-1)`-points of `e^g` have exponent of convergence below three, then `g` is linear.

This is Nevanlinna's theorem and Hadamard rigidity in series: the exponent of convergence bounds the
order of `e^g` (`Shields.order_le_expConvergence`), the order bounds the growth of `\Re g`
(`Shields.re_le_characteristic`), and subcubic growth of an odd function forces linearity.  The
bound the rigidity step imposes is three, not two, so the hypothesis a caller has to supply is
summability of `‖z‖ ^ (-p)` over the `(-1)`-points for a single `p < 3`, and any such `p` will do.
-/
theorem odd_eq_linear_of_expConvergence_lt_three (hg : Differentiable ℂ g)
    (hodd : ∀ z, g (-z) = -g z)
    (hexp : expConvergence
      (MeromorphicOn.divisor ((fun z ↦ Complex.exp (g z)) · - (-1)) univ)⁺ < 3) :
    ∀ z, g z = deriv g 0 * z := by
  refine odd_eq_linear_of_order_lt_three hg hodd (lt_of_le_of_lt ?_ hexp)
  exact order_le_expConvergence hg.cexp (fun z ↦ Complex.exp_ne_zero _) (by norm_num)

/-- **The Edrei input.**  If `g` is entire and odd and the `(-1)`-points of `e^g` have exponent of
convergence at most two, then `g` is linear. -/
theorem odd_eq_linear_of_expConvergence_le_two (hg : Differentiable ℂ g)
    (hodd : ∀ z, g (-z) = -g z)
    (hexp : expConvergence
      (MeromorphicOn.divisor ((fun z ↦ Complex.exp (g z)) · - (-1)) univ)⁺ ≤ 2) :
    ∀ z, g z = deriv g 0 * z :=
  odd_eq_linear_of_expConvergence_lt_three hg hodd (lt_of_le_of_lt hexp (by norm_num))


/-! ### Axiom footprint -/

/-- info: 'Shields.odd_eq_linear_of_order_le_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms odd_eq_linear_of_order_le_two

/-- info: 'Shields.odd_eq_linear_of_expConvergence_le_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms odd_eq_linear_of_expConvergence_le_two

end Shields
