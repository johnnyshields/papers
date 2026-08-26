/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Shields.Analysis.Complex.HadamardRigidity
import Shields.Analysis.Complex.ValueDistribution.MaxModulus
import Shields.Analysis.Complex.ValueDistribution.Nevanlinna

/-!
# Polynomial growth forces a polynomial

Hadamard rigidity at an arbitrary degree: an entire `g` whose real part on the ball of radius `S`
is bounded by an `M S` with `M S / S ^ n → 0` has vanishing `n`-th derivative, hence is a
polynomial of degree less than `n`.  The degree-two case is
`Shields.eq_affine_of_re_growth`; what the Edrei argument needs is the degree-three case, where the
majorant comes from a Nevanlinna characteristic of order below three.

## Main results

* `Shields.iteratedDeriv_eq_zero_of_re_growth` — the rigidity statement at degree `n`.
* `Shields.eq_quadratic_of_re_growth` — subcubic growth makes `g` a quadratic polynomial.
* `Shields.odd_eq_linear_of_re_growth` — an odd such `g` is linear.
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

/-! ### Rigidity at degree `n` -/

/-- **The `n`-th derivative vanishes identically.**

The Cauchy estimate at an arbitrary center `w` with radius `R`, fed by the Borel–Carathéodory
bound on the ball of radius `2(R+‖w‖)`, is `O(M(2(R+‖w‖))/R^n)`, and `R ≥ ‖w‖` makes that radius at
most `4R`, so the growth hypothesis sends it to `0`. -/
theorem iteratedDeriv_eq_zero_of_re_growth {n : ℕ} (hn : n ≠ 0) (hg : Differentiable ℂ g)
    (hMpos : ∀ S, 0 < M S)
    (hbound : ∀ S : ℝ, 0 < S → ∀ z ∈ ball (0 : ℂ) S, (g z).re ≤ M S)
    (hgrow : Tendsto (fun S : ℝ ↦ M S / S ^ n) atTop (𝓝 0)) (w : ℂ) :
    iteratedDeriv n g w = 0 := by
  have hdc : ∀ (c : ℂ) (R : ℝ), DiffContOnCl ℂ g (ball c R) :=
    fun c R ↦ ⟨hg.differentiableOn, hg.continuous.continuousOn⟩
  set ψ : ℝ → ℝ := fun S ↦ (n.factorial : ℝ) * 4 ^ n *
    (2 * (M S / S ^ n) + 3 * ‖g 0‖ / S ^ n) with hψdef
  have hψ : Tendsto ψ atTop (𝓝 0) := by
    have h1 : Tendsto (fun S : ℝ ↦ 2 * (M S / S ^ n)) atTop (𝓝 0) := by
      simpa using hgrow.const_mul (2 : ℝ)
    have h2 : Tendsto (fun S : ℝ ↦ 3 * ‖g 0‖ / S ^ n) atTop (𝓝 0) :=
      Filter.Tendsto.const_div_atTop (tendsto_pow_atTop hn) (3 * ‖g 0‖)
    simpa [hψdef] using (h1.add h2).const_mul ((n.factorial : ℝ) * 4 ^ n)
  have hStop : Tendsto (fun R : ℝ ↦ 2 * (R + ‖w‖)) atTop atTop :=
    Filter.Tendsto.const_mul_atTop two_pos (tendsto_atTop_add_const_right atTop ‖w‖ tendsto_id)
  have hev : ∀ᶠ R : ℝ in atTop, ‖iteratedDeriv n g w‖ ≤ ψ (2 * (R + ‖w‖)) := by
    filter_upwards [eventually_ge_atTop (max 1 ‖w‖)] with R hR
    have hR1 : (1 : ℝ) ≤ R := le_trans (le_max_left _ _) hR
    have hRw : ‖w‖ ≤ R := le_trans (le_max_right _ _) hR
    have hRpos : 0 < R := by linarith
    have hSpos : 0 < 2 * (R + ‖w‖) := by nlinarith [norm_nonneg w]
    have hS4R : 2 * (R + ‖w‖) ≤ 4 * R := by linarith
    have hsphere : ∀ z ∈ sphere w R, ‖g z‖ ≤ 2 * M (2 * (R + ‖w‖)) + 3 * ‖g 0‖ := by
      intro z hz
      have hzn : ‖z‖ ≤ 2 * (R + ‖w‖) / 2 := by
        rw [mem_sphere_iff_norm] at hz
        have := norm_sub_norm_le z w
        rw [hz] at this
        linarith
      exact norm_le_of_re_le hg hSpos (hMpos _) (hbound _ hSpos) hzn
    have hcauchy := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le
      (f := g) (c := w) (R := R) (C := 2 * M (2 * (R + ‖w‖)) + 3 * ‖g 0‖) n hRpos (hdc w R) hsphere
    refine hcauchy.trans ?_
    have hA : 0 ≤ 2 * M (2 * (R + ‖w‖)) + 3 * ‖g 0‖ := by
      have h₁ := (hMpos (2 * (R + ‖w‖))).le
      have h₂ := norm_nonneg (g 0)
      linarith
    have hNnn : (0 : ℝ) ≤ (n.factorial : ℝ) := by positivity
    have hRn : (0 : ℝ) < R ^ n := by positivity
    have hSn : (0 : ℝ) < (2 * (R + ‖w‖)) ^ n := by positivity
    have hpow : (2 * (R + ‖w‖)) ^ n ≤ 4 ^ n * R ^ n := by
      calc (2 * (R + ‖w‖)) ^ n ≤ (4 * R) ^ n := pow_le_pow_left₀ hSpos.le hS4R n
        _ = 4 ^ n * R ^ n := mul_pow 4 R n
    have hψS : ψ (2 * (R + ‖w‖)) = (n.factorial : ℝ) * 4 ^ n *
        (2 * M (2 * (R + ‖w‖)) + 3 * ‖g 0‖) / (2 * (R + ‖w‖)) ^ n := by
      rw [hψdef]
      field_simp
    rw [hψS, div_le_div_iff₀ hRn hSn]
    have hmul := mul_le_mul_of_nonneg_left hpow (mul_nonneg hNnn hA)
    nlinarith [hmul]
  have hle : ‖iteratedDeriv n g w‖ ≤ 0 := ge_of_tendsto (hψ.comp hStop) hev
  exact norm_eq_zero.1 (le_antisymm hle (norm_nonneg _))

/-! ### Subcubic growth forces a quadratic -/

/-- **Subcubic growth of `\Re g` makes `g` a quadratic polynomial.** -/
theorem eq_quadratic_of_re_growth (hg : Differentiable ℂ g) (hMpos : ∀ S, 0 < M S)
    (hbound : ∀ S : ℝ, 0 < S → ∀ z ∈ ball (0 : ℂ) S, (g z).re ≤ M S)
    (hgrow : Tendsto (fun S : ℝ ↦ M S / S ^ 3) atTop (𝓝 0)) :
    ∀ z, g z = g 0 + deriv g 0 * z + iteratedDeriv 2 g 0 / 2 * z ^ 2 := by
  set a : ℂ := iteratedDeriv 2 g 0 with hadef
  have h3 : ∀ w, deriv (deriv (deriv g)) w = 0 := by
    intro w
    have := iteratedDeriv_eq_zero_of_re_growth (n := 3) (by norm_num) hg hMpos hbound hgrow w
    rwa [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_one] at this
  have hderiv2 : ∀ w, deriv (deriv g) w = a := by
    intro w
    have hconst := is_const_of_deriv_eq_zero hg.deriv.deriv h3 w 0
    rw [hadef, iteratedDeriv_succ, iteratedDeriv_one]
    exact hconst
  -- the first derivative is affine
  have hderiv1 : ∀ z, deriv g z = deriv g 0 + a * z := by
    have hzero : ∀ w, HasDerivAt (fun z ↦ deriv g z - a * z) 0 w := by
      intro w
      have h1 : HasDerivAt (deriv g) (deriv (deriv g) w) w := (hg.deriv w).hasDerivAt
      have h2 : HasDerivAt (fun z : ℂ ↦ a * z) a w := by
        simpa using (hasDerivAt_id w).const_mul a
      have := h1.sub h2
      rwa [hderiv2 w, sub_self] at this
    intro z
    have := is_const_of_deriv_eq_zero (f := fun z ↦ deriv g z - a * z)
      (fun w ↦ (hzero w).differentiableAt) (fun w ↦ (hzero w).deriv) z 0
    simp only [mul_zero, sub_zero] at this
    linear_combination this
  -- and `g` itself is quadratic
  have hzero : ∀ w, HasDerivAt (fun z ↦ g z - (deriv g 0 * z + a / 2 * z ^ 2)) 0 w := by
    intro w
    have h1 : HasDerivAt g (deriv g w) w := (hg w).hasDerivAt
    have h2 : HasDerivAt (fun z : ℂ ↦ deriv g 0 * z + a / 2 * z ^ 2)
        (deriv g 0 + a / 2 * (2 * w)) w := by
      have hlin : HasDerivAt (fun z : ℂ ↦ deriv g 0 * z) (deriv g 0) w := by
        simpa using (hasDerivAt_id w).const_mul (deriv g 0)
      have hsq : HasDerivAt (fun z : ℂ ↦ a / 2 * z ^ 2) (a / 2 * (2 * w)) w := by
        simpa using ((hasDerivAt_pow 2 w).const_mul (a / 2))
      exact hlin.add hsq
    have := h1.sub h2
    rw [hderiv1 w] at this
    have hcalc : deriv g 0 + a * w - (deriv g 0 + a / 2 * (2 * w)) = 0 := by ring
    rwa [hcalc] at this
  intro z
  have := is_const_of_deriv_eq_zero (f := fun z ↦ g z - (deriv g 0 * z + a / 2 * z ^ 2))
    (fun w ↦ (hzero w).differentiableAt) (fun w ↦ (hzero w).deriv) z 0
  simp only [mul_zero, zero_pow, sub_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    add_zero] at this
  linear_combination this

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
  refine hbig.trans_isLittleO ?_
  rw [isLittleO_iff_tendsto (fun x hx ↦ ?_)]
  · have hneg : Tendsto (fun S : ℝ ↦ S ^ (-(3 - q))) atTop (𝓝 0) :=
      tendsto_rpow_neg_atTop (by linarith)
    refine hneg.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with S hS
    rw [← Real.rpow_natCast S 3, ← Real.rpow_sub hS]
    congr 1
    push_cast
    ring
  · have hx0 : x = 0 := by
      by_contra hx0
      exact absurd hx (pow_ne_zero 3 hx0)
    rw [hx0]
    exact Real.zero_rpow hq0.ne'

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

end Shields
