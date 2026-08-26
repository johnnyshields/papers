/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-!
# Hadamard's factorization: the rigidity half

The Hadamard factorization theorem splits into two halves.  The *product* half builds a canonical
product with prescribed zeros — `Shields.Analysis.Complex.CanonicalProduct` for genus zero.  The
*rigidity* half says that an entire function with no zeros and controlled growth is the exponential
of a polynomial; that is what this file proves, at the order relevant to genus zero and one.

## Main results

* `Shields.exists_exp_comp_eq` — a nonvanishing entire function is `exp ∘ g` for an entire `g`.
* `Shields.eq_affine_of_re_growth` — an entire `g` whose real part is bounded on every ball
  `‖z‖ < S` by an `M S` with `M S/S^2 \to 0` is affine.
* `Shields.exists_affine_exp_of_growth` — the two together: a nonvanishing entire `h` with
  `‖h z‖ \le e^{M S}` on `‖z‖ < S` and `M S/S^2 \to 0` equals `e^{az+b}`.
* `Shields.eq_mul_exp_affine_of_growth` — Hadamard's conclusion in the form it is applied: if
  `f = P \cdot h` with `h` entire, nonvanishing and of that growth, then `f = Pe^{az+b}`.
* `Shields.eq_const_of_sublinear_growth` — the Liouville statement for the *logarithmic-derivative*
  route to the same conclusion: an entire function bounded by `o(R)` on a sequence of circles is
  constant.  That route needs no lower bound on any modulus, so it bypasses the minimum-modulus
  estimate whenever the function's logarithmic derivative can be bounded directly.

## Implementation notes

Mathlib carries every ingredient, at the pinned revision:

* `Differentiable.isExactOn_univ` (Morera on the plane) gives the primitive of the logarithmic
  derivative, so the entire logarithm needs no covering-space argument.  `Complex.exp_log` then
  fixes the additive constant.
* `Complex.borelCaratheodory` turns the one-sided bound on `\Re g` into a two-sided bound on `‖g‖`.
  Read on the circle `‖z‖ = S/2` inside the ball of radius `S`, it gives `2M(S)+3‖g(0)‖`, and the
  factors `2` and `3` are where the choice `S = 2(R+‖w‖)` comes from.
* `Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le` is the Cauchy estimate, applied to
  the *second* derivative at an arbitrary center.  `Shields.tendsto_cauchy_bound_two` is where
  letting `R \to \infty` kills it — the one place the growth hypothesis is spent — and
  `is_const_of_deriv_eq_zero` twice turns `g'' \equiv 0` into affineness: no power series and no
  vanishing-coefficient argument.

The growth hypothesis is stated with an explicit majorant `M : ℝ → ℝ` rather than an order or a
type, because that is the form the minimum-modulus estimate for a canonical product delivers, and
because it keeps the conclusion free of any `\limsup`.

What is **not** here is the minimum modulus itself: the lower bound on a canonical product that
supplies `M`.  That is the remaining input to a full Hadamard factorization.
-/

namespace Shields

open Complex Filter Metric Set Topology

/-! ### The entire logarithm -/

/-- **A nonvanishing entire function is the exponential of an entire function.**

The logarithmic derivative `h'/h` is entire, so Morera on the plane gives it a primitive `G`; then
`he^{-G}` has zero derivative, hence is a nonzero constant, whose logarithm is the additive
correction. -/
theorem exists_exp_comp_eq {h : ℂ → ℂ} (hh : Differentiable ℂ h) (hne : ∀ z, h z ≠ 0) :
    ∃ g : ℂ → ℂ, Differentiable ℂ g ∧ ∀ z, h z = Complex.exp (g z) := by
  have hF : Differentiable ℂ fun z => deriv h z / h z := hh.deriv.div hh hne
  obtain ⟨G, hG⟩ := hF.isExactOn_univ
  have hGd : ∀ z, HasDerivAt G (deriv h z / h z) z := fun z => hG z (Set.mem_univ z)
  have hGdiff : Differentiable ℂ G := fun z => (hGd z).differentiableAt
  -- `h e^{-G}` has vanishing derivative
  have hu : ∀ z, HasDerivAt (fun w => h w * Complex.exp (-G w)) 0 z := by
    intro z
    have h1 : HasDerivAt h (deriv h z) z := (hh z).hasDerivAt
    have h2 : HasDerivAt (fun w => Complex.exp (-G w))
        (Complex.exp (-G z) * -(deriv h z / h z)) z := ((hGd z).neg).cexp
    have hmul := h1.mul h2
    have hval : deriv h z * Complex.exp (-G z)
        + h z * (Complex.exp (-G z) * -(deriv h z / h z)) = 0 := by
      have hz := hne z
      field
    rw [hval] at hmul
    exact hmul
  have hconst : ∀ z, h z * Complex.exp (-G z) = h 0 * Complex.exp (-G 0) :=
    fun z =>
      is_const_of_deriv_eq_zero (fun w => (hu w).differentiableAt) (fun w => (hu w).deriv) z 0
  have hne0 : h 0 * Complex.exp (-G 0) ≠ 0 :=
    mul_ne_zero (hne 0) (Complex.exp_ne_zero _)
  refine ⟨fun z => G z + Complex.log (h 0 * Complex.exp (-G 0)), hGdiff.add_const _, fun z => ?_⟩
  rw [Complex.exp_add, Complex.exp_log hne0, ← hconst z]
  rw [mul_comm (h z) (Complex.exp (-G z)), ← mul_assoc, mul_comm (Complex.exp (G z))]
  rw [← Complex.exp_add]
  simp

/-! ### Subquadratic growth forces affineness -/

variable {g : ℂ → ℂ} {M : ℝ → ℝ}

/-- The Borel–Carathéodory bound read on the middle circle: if `\Re g \le M(S)` on `‖z‖ < S`, then
`‖g‖ \le 2M(S)+3‖g(0)‖` on `‖z‖ \le S/2`. -/
theorem norm_le_of_re_le (hg : Differentiable ℂ g) {S : ℝ} (hS : 0 < S) (hM : 0 < M S)
    (hbound : ∀ z ∈ ball (0 : ℂ) S, (g z).re ≤ M S) {z : ℂ} (hz : ‖z‖ ≤ S / 2) :
    ‖g z‖ ≤ 2 * M S + 3 * ‖g 0‖ := by
  have hzball : z ∈ ball (0 : ℂ) S := by
    rw [mem_ball_zero_iff]
    linarith
  have hbc := Complex.borelCaratheodory (f := g) (M := M S) (R := S) (z := z) hM
    hg.differentiableOn (fun w hw => hbound w hw) hS hzball
  have hden : S / 2 ≤ S - ‖z‖ := by linarith
  have hdenpos : (0 : ℝ) < S - ‖z‖ := by linarith
  have h1 : 2 * M S * ‖z‖ / (S - ‖z‖) ≤ 2 * M S := by
    rw [div_le_iff₀ hdenpos]
    nlinarith [norm_nonneg z, hM, hz, hden]
  have h2 : ‖g 0‖ * (S + ‖z‖) / (S - ‖z‖) ≤ 3 * ‖g 0‖ := by
    rw [div_le_iff₀ hdenpos]
    nlinarith [norm_nonneg (g 0), norm_nonneg z, hz, hden]
  linarith

/-- **The Cauchy estimate on the second derivative, from a bound on the real part.**  On the
sphere of radius `R` about `w` every point has norm at most `S / 2` with `S = 2(R + ‖w‖)`, so
`Shields.norm_le_of_re_le` turns the real-part bound `M S` into `‖g‖ ≤ 2 M S + 3‖g 0‖` there, and
Cauchy's estimate at order two divides by `R^2`.

The radius and the ball are tied together on purpose: `S` is chosen as a function of `R` so that
one hypothesis on `M` -- subquadratic growth -- controls the whole family at once. -/
theorem norm_iteratedDeriv_two_le (hg : Differentiable ℂ g) (hMpos : ∀ S, 0 < M S)
    (hbound : ∀ S : ℝ, 0 < S → ∀ z ∈ ball (0 : ℂ) S, (g z).re ≤ M S) (w : ℂ)
    {R : ℝ} (hR : 0 < R) :
    ‖iteratedDeriv 2 g w‖ ≤ 2 * (2 * M (2 * (R + ‖w‖)) + 3 * ‖g 0‖) / R ^ 2 := by
  set S : ℝ := 2 * (R + ‖w‖) with hS
  have hSpos : 0 < S := by have := norm_nonneg w; rw [hS]; linarith
  have hsphere : ∀ z ∈ sphere w R, ‖g z‖ ≤ 2 * M S + 3 * ‖g 0‖ := by
    intro z hz
    have hzn : ‖z‖ ≤ S / 2 := by
      rw [mem_sphere_iff_norm] at hz
      have := norm_sub_norm_le z w
      rw [hz] at this
      rw [hS]; linarith
    exact norm_le_of_re_le hg hSpos (hMpos S) (hbound S hSpos) hzn
  have hcauchy := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le
    (f := g) (c := w) (R := R) (C := 2 * M S + 3 * ‖g 0‖) 2 hR
    ⟨hg.differentiableOn, hg.continuous.continuousOn⟩ hsphere
  rw [show ((Nat.factorial 2 : ℕ) : ℝ) = 2 by norm_num] at hcauchy
  exact hcauchy

/-- **The Cauchy bound tends to zero, and that is where subquadratic growth is spent.**

Written at `S = 2(R + ‖w‖)`, the bound of `Shields.norm_iteratedDeriv_two_le` is
`4 M S / R^2 + 6C / R^2`.  Once `R ≥ ‖w‖` one has `S ≤ 4R`, so `1/R^2 ≤ 16/S^2` and the first
term is at most `64 (M S / S^2)` — which the hypothesis drives to `0`.  The second is `O(R^{-2})`.

This is the only place `M S / S^2 → 0` is used, and it is used here and nowhere else because the
radius `R` and the ball radius `S` are tied by `S = 2(R + ‖w‖)`: one hypothesis on `M` then
controls the whole family. -/
theorem tendsto_cauchy_bound_two (hMpos : ∀ S, 0 < M S)
    (hgrow : Tendsto (fun S : ℝ => M S / S ^ 2) atTop (nhds 0)) (w : ℂ) {C : ℝ} (hC : 0 ≤ C) :
    Tendsto (fun R : ℝ => 2 * (2 * M (2 * (R + ‖w‖)) + 3 * C) / R ^ 2) atTop (nhds 0) := by
  have hSat : Tendsto (fun R : ℝ => 2 * (R + ‖w‖)) atTop atTop :=
    Filter.Tendsto.const_mul_atTop two_pos (tendsto_atTop_add_const_right _ ‖w‖ tendsto_id)
  have hquot : Tendsto (fun R : ℝ => M (2 * (R + ‖w‖)) / (2 * (R + ‖w‖)) ^ 2) atTop (nhds 0) :=
    hgrow.comp hSat
  have htail : Tendsto (fun R : ℝ => 6 * C / R ^ 2) atTop (nhds 0) :=
    Filter.Tendsto.const_div_atTop (tendsto_pow_atTop two_ne_zero) (6 * C)
  have hmaj : Tendsto
      (fun R : ℝ => 64 * (M (2 * (R + ‖w‖)) / (2 * (R + ‖w‖)) ^ 2) + 6 * C / R ^ 2)
      atTop (nhds 0) := by
    simpa using (hquot.const_mul (64 : ℝ)).add htail
  refine squeeze_zero' ?_ ?_ hmaj
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    have := (hMpos (2 * (R + ‖w‖))).le
    positivity
  · filter_upwards [eventually_ge_atTop ‖w‖, eventually_gt_atTop (0 : ℝ)] with R hRw hR
    set S : ℝ := 2 * (R + ‖w‖) with hS
    have hSpos : 0 < S := by rw [hS]; have := norm_nonneg w; linarith
    have hS4 : S ≤ 4 * R := by rw [hS]; linarith
    have hMS : 0 < M S := hMpos S
    have hR2 : (0 : ℝ) < R ^ 2 := by positivity
    have hS2 : S ^ 2 ≤ 16 * R ^ 2 := by nlinarith [hSpos, hS4]
    have hfirst : 4 * M S / R ^ 2 ≤ 64 * (M S / S ^ 2) := by
      rw [div_le_iff₀ hR2]
      have hrw : 64 * (M S / S ^ 2) * R ^ 2 = 64 * M S * R ^ 2 / S ^ 2 := by ring
      rw [hrw, le_div_iff₀ (by positivity : (0 : ℝ) < S ^ 2)]
      nlinarith [mul_le_mul_of_nonneg_left hS2 hMS.le]
    have hsplit : 2 * (2 * M S + 3 * C) / R ^ 2 = 4 * M S / R ^ 2 + 6 * C / R ^ 2 := by
      field_simp; ring
    rw [hsplit]
    linarith

/-- **The second derivative vanishes identically.**

`Shields.norm_iteratedDeriv_two_le` bounds `‖g''(w)‖` at every radius by a quantity
`Shields.tendsto_cauchy_bound_two` sends to `0`, and a constant below a null sequence is `0`. -/
theorem iteratedDeriv_two_eq_zero_of_re_growth (hg : Differentiable ℂ g)
    (hMpos : ∀ S, 0 < M S)
    (hbound : ∀ S : ℝ, 0 < S → ∀ z ∈ ball (0 : ℂ) S, (g z).re ≤ M S)
    (hgrow : Tendsto (fun S : ℝ => M S / S ^ 2) atTop (nhds 0)) (w : ℂ) :
    iteratedDeriv 2 g w = 0 := by
  have hev : ∀ᶠ R : ℝ in atTop, ‖iteratedDeriv 2 g w‖
      ≤ 2 * (2 * M (2 * (R + ‖w‖)) + 3 * ‖g 0‖) / R ^ 2 := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    exact norm_iteratedDeriv_two_le hg hMpos hbound w hR
  have hle : ‖iteratedDeriv 2 g w‖ ≤ 0 :=
    ge_of_tendsto (tendsto_cauchy_bound_two hMpos hgrow w (norm_nonneg (g 0))) hev
  exact norm_eq_zero.1 (le_antisymm hle (norm_nonneg _))

/-- **Subquadratic growth of `\Re g` forces `g` affine.** -/
theorem eq_affine_of_re_growth (hg : Differentiable ℂ g) (hMpos : ∀ S, 0 < M S)
    (hbound : ∀ S : ℝ, 0 < S → ∀ z ∈ ball (0 : ℂ) S, (g z).re ≤ M S)
    (hgrow : Tendsto (fun S : ℝ => M S / S ^ 2) atTop (nhds 0)) :
    ∀ z, g z = g 0 + deriv g 0 * z := by
  have h2 : ∀ w, deriv (deriv g) w = 0 := by
    intro w
    have := iteratedDeriv_two_eq_zero_of_re_growth hg hMpos hbound hgrow w
    rwa [iteratedDeriv_succ, iteratedDeriv_one] at this
  have hderiv : ∀ w, deriv g w = deriv g 0 :=
    fun w => is_const_of_deriv_eq_zero hg.deriv h2 w 0
  have haff : ∀ w, HasDerivAt (fun z => g z - deriv g 0 * z) 0 w := by
    intro w
    have h1 : HasDerivAt g (deriv g w) w := (hg w).hasDerivAt
    have h2' : HasDerivAt (fun z : ℂ => deriv g 0 * z) (deriv g 0) w := by
      simpa using (hasDerivAt_id w).const_mul (deriv g 0)
    have := h1.sub h2'
    rw [hderiv w, sub_self] at this
    exact this
  intro z
  have := is_const_of_deriv_eq_zero (f := fun z => g z - deriv g 0 * z)
    (fun w => (haff w).differentiableAt) (fun w => (haff w).deriv) z 0
  simp only [mul_zero, sub_zero] at this
  linear_combination this

/-! ### Sublinear growth forces a constant -/

/-- **Sublinear growth on a sequence of circles forces a constant.**

If `E` is entire and `\sup_{‖z‖=R_k}\|E\|/R_k \to 0` for some `R_k \to \infty`, then `E` is
constant.  This is the Liouville statement that a *difference of logarithmic derivatives* needs: the
bound is on `E` itself, on circles only, and needs neither a lower bound on any modulus nor a bound
in every direction.

The proof is the Cauchy estimate for the first derivative at an arbitrary center, with the maximum
modulus principle carrying the circle bound to the whole disc. -/
theorem eq_const_of_sublinear_growth {E : ℂ → ℂ} (hE : Differentiable ℂ E) {R C : ℕ → ℝ}
    (hRpos : ∀ k, 0 < R k) (hR : Tendsto R atTop atTop) (hCnn : ∀ k, 0 ≤ C k)
    (hbound : ∀ k, ∀ z ∈ sphere (0 : ℂ) (R k), ‖E z‖ ≤ C k)
    (hgrow : Tendsto (fun k => C k / R k) atTop (nhds 0)) :
    ∀ z, E z = E 0 := by
  have hdc : ∀ (c : ℂ) (r : ℝ), DiffContOnCl ℂ E (ball c r) :=
    fun c r => ⟨hE.differentiableOn, hE.continuous.continuousOn⟩
  have hdisc : ∀ k, ∀ z ∈ closedBall (0 : ℂ) (R k), ‖E z‖ ≤ C k := by
    intro k z hz
    refine Complex.norm_le_of_forall_mem_frontier_norm_le
      (U := ball (0 : ℂ) (R k)) isBounded_ball (hdc 0 (R k)) ?_ ?_
    · rw [frontier_ball _ (ne_of_gt (hRpos k))]
      exact hbound k
    · rwa [closure_ball _ (ne_of_gt (hRpos k))]
  have hderiv : ∀ w : ℂ, deriv E w = 0 := by
    intro w
    have hev : ∀ᶠ k in atTop, ‖deriv E w‖ ≤ 2 * (C k / R k) := by
      filter_upwards [hR.eventually_ge_atTop (2 * ‖w‖ + 1)] with k hk
      have hRk : 0 < R k := hRpos k
      have hwnn : (0 : ℝ) ≤ ‖w‖ := norm_nonneg w
      have hρ : 0 < R k - ‖w‖ := by linarith
      have hsph : ∀ z ∈ sphere w (R k - ‖w‖), ‖E z‖ ≤ C k := by
        intro z hz
        have hmem : z ∈ closedBall (0 : ℂ) (R k) := by
          rw [mem_closedBall_zero_iff]
          rw [mem_sphere_iff_norm] at hz
          have := norm_sub_norm_le z w
          rw [hz] at this
          linarith
        exact hdisc k z hmem
      have hcauchy := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le
        (f := E) (c := w) (R := R k - ‖w‖) (C := C k) 1 hρ (hdc w (R k - ‖w‖)) hsph
      rw [iteratedDeriv_one] at hcauchy
      have hfac : ((Nat.factorial 1 : ℕ) : ℝ) = 1 := by norm_num
      rw [hfac, one_mul, pow_one] at hcauchy
      refine hcauchy.trans ?_
      rw [div_le_iff₀ hρ]
      have h2 : R k / 2 ≤ R k - ‖w‖ := by linarith
      have hC := hCnn k
      have hstep : C k * (R k / 2) ≤ C k * (R k - ‖w‖) :=
        mul_le_mul_of_nonneg_left h2 hC
      calc C k = 2 * (C k / R k) * (R k / 2) := by field_simp
        _ ≤ 2 * (C k / R k) * (R k - ‖w‖) := by
            refine mul_le_mul_of_nonneg_left h2 ?_
            positivity
    have hlim : Tendsto (fun k => 2 * (C k / R k)) atTop (nhds 0) := by
      simpa using hgrow.const_mul (2 : ℝ)
    have hle : ‖deriv E w‖ ≤ 0 := ge_of_tendsto hlim hev
    exact norm_eq_zero.1 (le_antisymm hle (norm_nonneg _))
  exact fun z => is_const_of_deriv_eq_zero hE hderiv z 0

/-! ### Hadamard's rigidity -/

/-- **A nonvanishing entire function of subquadratic logarithmic growth is `e^{az+b}`.**

This is the rigidity half of the Hadamard factorization at genus zero and one: the hypothesis
`‖h z‖ \le e^{M(S)}` on `‖z‖ < S` with `M(S)/S^2 \to 0` covers every function of order `< 2`, so in
particular order one, where the exponential factor is affine. -/
theorem exists_affine_exp_of_growth {h : ℂ → ℂ} (hh : Differentiable ℂ h) (hne : ∀ z, h z ≠ 0)
    (hMpos : ∀ S, 0 < M S)
    (hbound : ∀ S : ℝ, 0 < S → ∀ z ∈ ball (0 : ℂ) S, ‖h z‖ ≤ Real.exp (M S))
    (hgrow : Tendsto (fun S : ℝ => M S / S ^ 2) atTop (nhds 0)) :
    ∃ a b : ℂ, ∀ z, h z = Complex.exp (a * z + b) := by
  obtain ⟨g, hgd, hgeq⟩ := exists_exp_comp_eq hh hne
  have hre : ∀ S : ℝ, 0 < S → ∀ z ∈ ball (0 : ℂ) S, (g z).re ≤ M S := by
    intro S hS z hz
    have h1 := hbound S hS z hz
    rw [hgeq z, Complex.norm_exp] at h1
    exact Real.exp_le_exp.1 h1
  have haff := eq_affine_of_re_growth hgd hMpos hre hgrow
  refine ⟨deriv g 0, g 0, fun z => ?_⟩
  rw [hgeq z, haff z]
  ring_nf

/-- **Hadamard's conclusion, in the form it is applied.**  Once the quotient by a canonical product
is known to be entire, nonvanishing and of subquadratic logarithmic growth, the original function is
that product times `e^{az+b}`. -/
theorem eq_mul_exp_affine_of_growth {f P h : ℂ → ℂ} (hfac : ∀ z, f z = P z * h z)
    (hh : Differentiable ℂ h) (hne : ∀ z, h z ≠ 0) (hMpos : ∀ S, 0 < M S)
    (hbound : ∀ S : ℝ, 0 < S → ∀ z ∈ ball (0 : ℂ) S, ‖h z‖ ≤ Real.exp (M S))
    (hgrow : Tendsto (fun S : ℝ => M S / S ^ 2) atTop (nhds 0)) :
    ∃ a b : ℂ, ∀ z, f z = P z * Complex.exp (a * z + b) := by
  obtain ⟨a, b, hab⟩ := exists_affine_exp_of_growth hh hne hMpos hbound hgrow
  exact ⟨a, b, fun z => by rw [hfac z, hab z]⟩

end Shields
