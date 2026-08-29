/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Shields.Analysis.Complex.ValueDistribution.Jensen
import Shields.Analysis.Complex.ValueDistribution.PolynomialGrowth

/-!
# The odd part of a real entire exponent

`Shields.odd_eq_linear_of_expConvergence_lt_three` makes an odd entire function linear, with a
complex coefficient.  Two things stand between that and the statement a Pólya-frequency argument
consumes: the exponent is `g z - g (-z)` rather than an odd function given as such, and the
coefficient has to be real.  Realness comes from the exponential being real on the real axis, which
is what a real coefficient sequence gives: the imaginary part of `g` on the real axis is continuous
and takes values in `π ℤ`, hence is constantly `g 0`'s.

The remaining hypothesis is a statement about the `(-1)`-points of `exp (g z - g (-z))` alone:
either that their exponent of convergence is below `3`, or the summability at a single exponent
`p < 3` that bounds it.

## Main results

* `Shields.im_eq_zero_of_exp_im_eq_zero` — an entire `g` with `g 0 = 0` whose exponential is real
  on the real axis is itself real there.
* `Shields.deriv_im_eq_zero` — an entire function real on the real axis has real derivative at `0`.
* `Shields.oddPart_eq_of_expConvergence_lt_three` — the odd part of `g` is `2 γ z` for a real `γ`.
* `Shields.oddPart_eq_of_expConvergence_le_two` — its exponent-two case.
* `Shields.oddPart_eq_of_summable_rpow` — the same, from summability of `‖z‖ ^ (-p)` over the
  `(-1)`-points at a single `p < 3`.
* `Shields.oddPart_eq_of_summable` — its exponent-two case.
* `Shields.im_eq_zero_of_hasSum_real` — a power series with real coefficients is real on the real
  axis.
* `Shields.hasSum_evenPart`, `Shields.evenPart_coeff_nonneg` — the even part's coefficients, and
  their nonnegativity.
* `Shields.divisor_negOne_eq_divisor_evenPart` — the `(-1)`-points of `exp (g z - g (-z))` are
  the zeros of the even part `z ↦ exp (g z) + exp (g (-z))`.
* `Shields.oddPart_eq_of_hasSum_of_summable_rpow` — the two combined, so that a real coefficient
  sequence for `exp ∘ g` and summability at one `p < 3` over the zeros of the even part are the only
  inputs.
* `Shields.oddPart_eq_of_hasSum_of_summable` — its exponent-two case.
* `Shields.oddPart_eq_of_hasSum_of_growth` — the same conclusion from a growth bound on the even
  part along the positive real axis, for a nonnegative coefficient sequence: no summability
  hypothesis and no information about the location of the zeros.

## Tags

value distribution, order of growth, exponent of convergence, Pólya frequency sequence
-/

open Complex Filter Metric Real Set ValueDistribution
open scoped ENNReal NNReal Topology

namespace Shields

variable {g : ℂ → ℂ}

/-- An entire function whose exponential is real on the real axis and which vanishes at `0` is
itself real on the real axis.  The imaginary part is continuous and lands in `π ℤ`, so the set
where it vanishes is clopen and nonempty. -/
theorem im_eq_zero_of_exp_im_eq_zero (hg : Continuous g) (hg0 : g 0 = 0)
    (h : ∀ x : ℝ, (Complex.exp (g x)).im = 0) (x : ℝ) : (g (x : ℂ)).im = 0 := by
  set u : ℝ → ℝ := fun x ↦ (g (x : ℂ)).im with hu
  have hcont : Continuous u := Complex.continuous_im.comp (hg.comp Complex.continuous_ofReal)
  have hsin : ∀ y : ℝ, Real.sin (u y) = 0 := by
    intro y
    have hy := h y
    rw [Complex.exp_im] at hy
    rcases mul_eq_zero.1 hy with h1 | h2
    · exact absurd h1 (Real.exp_ne_zero _)
    · exact h2
  have hopen : IsOpen {y : ℝ | u y = 0} := by
    rw [isOpen_iff_mem_nhds]
    intro y hy
    have hmem : Set.Ioo (-π) π ∈ 𝓝 (u y) := by
      rw [Set.mem_ofPred_eq] at hy
      rw [hy]
      exact Ioo_mem_nhds (by linarith [Real.pi_pos]) Real.pi_pos
    filter_upwards [hcont.continuousAt.eventually_mem hmem] with z hz
    exact (Real.sin_eq_zero_iff_of_lt_of_lt hz.1 hz.2).1 (hsin z)
  have hclosed : IsClosed {y : ℝ | u y = 0} := isClosed_eq hcont continuous_const
  have huniv : {y : ℝ | u y = 0} = Set.univ :=
    IsClopen.eq_univ ⟨hclosed, hopen⟩ ⟨0, by simp [hu, hg0]⟩
  have : x ∈ {y : ℝ | u y = 0} := huniv ▸ Set.mem_univ x
  exact this

/-- The derivative at `0` of an entire function that is real on the real axis is real. -/
theorem deriv_im_eq_zero (hg : Differentiable ℂ g) (h : ∀ x : ℝ, (g (x : ℂ)).im = 0) :
    (deriv g 0).im = 0 := by
  have h1 : HasDerivAt g (deriv g 0) ((0 : ℝ) : ℂ) := by
    simpa using (hg 0).hasDerivAt
  have h2 : HasDerivAt (fun x : ℝ ↦ g (x : ℂ)) (deriv g 0) 0 := h1.comp_ofReal
  have h3 : HasDerivAt (fun x : ℝ ↦ (g (x : ℂ)).im) (deriv g 0).im 0 := by
    simpa [Function.comp_def] using Complex.imCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h2
  have h4 : HasDerivAt (fun x : ℝ ↦ (g (x : ℂ)).im) 0 0 := by
    rw [funext h]
    exact hasDerivAt_const _ _
  exact h3.unique h4

/-- **The odd part of `g` is linear with a real coefficient.**

`g` is entire, vanishes at `0`, and has a real exponential on the real axis; the `(-1)`-points of
`exp (g z - g (-z))` have exponent of convergence below `3`. -/
theorem oddPart_eq_of_expConvergence_lt_three (hg : Differentiable ℂ g) (hg0 : g 0 = 0)
    (hreal : ∀ x : ℝ, (Complex.exp (g (x : ℂ))).im = 0)
    (hexp : expConvergence (MeromorphicOn.divisor
      ((fun z ↦ Complex.exp (g z - g (-z))) · - (-1)) Set.univ)⁺ < 3) :
    ∃ γ : ℝ, ∀ z, g z - g (-z) = 2 * (γ : ℂ) * z := by
  set G : ℂ → ℂ := fun z ↦ g z - g (-z) with hGdef
  have hGdiff : Differentiable ℂ G := hg.sub (hg.comp differentiable_neg)
  have hGodd : ∀ z, G (-z) = -G z := by
    intro z
    simp [hGdef, neg_neg, neg_sub]
  have hlin := odd_eq_linear_of_expConvergence_lt_three hGdiff hGodd hexp
  have hgreal : ∀ x : ℝ, (g (x : ℂ)).im = 0 :=
    im_eq_zero_of_exp_im_eq_zero hg.continuous hg0 hreal
  have hGreal : ∀ x : ℝ, (G (x : ℂ)).im = 0 := by
    intro x
    have hneg : ((-x : ℝ) : ℂ) = -(x : ℂ) := Complex.ofReal_neg x
    simp only [hGdef, Complex.sub_im, hgreal x, ← hneg, hgreal (-x), sub_zero]
  have hGim : (deriv G 0).im = 0 := deriv_im_eq_zero hGdiff hGreal
  have hcast : ((deriv G 0).re : ℂ) = deriv G 0 :=
    Complex.conj_eq_iff_re.1 (Complex.conj_eq_iff_im.2 hGim)
  refine ⟨(deriv G 0).re / 2, fun z ↦ ?_⟩
  have hz := hlin z
  rw [show g z - g (-z) = G z from rfl, hz]
  push_cast
  rw [hcast]
  ring

/-- The exponent-two case of `Shields.oddPart_eq_of_expConvergence_lt_three`. -/
theorem oddPart_eq_of_expConvergence_le_two (hg : Differentiable ℂ g) (hg0 : g 0 = 0)
    (hreal : ∀ x : ℝ, (Complex.exp (g (x : ℂ))).im = 0)
    (hexp : expConvergence (MeromorphicOn.divisor
      ((fun z ↦ Complex.exp (g z - g (-z))) · - (-1)) Set.univ)⁺ ≤ 2) :
    ∃ γ : ℝ, ∀ z, g z - g (-z) = 2 * (γ : ℂ) * z :=
  oddPart_eq_of_expConvergence_lt_three hg hg0 hreal (lt_of_le_of_lt hexp (by norm_num))

/-- The odd part of `g` is linear with a real coefficient, from the summability of `‖z‖ ^ (-p)` over
the `(-1)`-points of `exp (g z - g (-z))` at a single exponent `p < 3`.

The exponent is not `2`: what the rigidity step needs is a subcubic majorant, so any `p` below `3`
gives the conclusion.  A caller with summability at `p = 2` — the critical exponent for the zeros of
an order-one function of `z ^ 2` — has more than is required, and a caller who can only reach some
`p` in `(2, 3)` still has enough. -/
theorem oddPart_eq_of_summable_rpow {p : NNReal} (hp : (p : ℝ) < 3) (hg : Differentiable ℂ g)
    (hg0 : g 0 = 0) (hreal : ∀ x : ℝ, (Complex.exp (g (x : ℂ))).im = 0)
    (hsum : Summable fun z : ℂ ↦ ((MeromorphicOn.divisor
      ((fun z ↦ Complex.exp (g z - g (-z))) · - (-1)) Set.univ)⁺ z : ℝ) * ‖z‖ ^ (-(p : ℝ))) :
    ∃ γ : ℝ, ∀ z, g z - g (-z) = 2 * (γ : ℂ) * z := by
  refine oddPart_eq_of_expConvergence_lt_three hg hg0 hreal ?_
  set D := (MeromorphicOn.divisor ((fun z ↦ Complex.exp (g z - g (-z))) · - (-1)) Set.univ)⁺
    with hD
  have hp3 : ((p : ℝ≥0∞)) < 3 := by
    have : p < (3 : NNReal) := by exact_mod_cast hp
    exact_mod_cast this
  exact lt_of_le_of_lt (expConvergence_le (D := D) (p := p) hsum) hp3

/-- The exponent-two case of `Shields.oddPart_eq_of_summable_rpow`. -/
theorem oddPart_eq_of_summable (hg : Differentiable ℂ g) (hg0 : g 0 = 0)
    (hreal : ∀ x : ℝ, (Complex.exp (g (x : ℂ))).im = 0)
    (hsum : Summable fun z : ℂ ↦ ((MeromorphicOn.divisor
      ((fun z ↦ Complex.exp (g z - g (-z))) · - (-1)) Set.univ)⁺ z : ℝ) * ‖z‖ ^ (-(2 : ℝ))) :
    ∃ γ : ℝ, ∀ z, g z - g (-z) = 2 * (γ : ℂ) * z := by
  refine oddPart_eq_of_summable_rpow (p := (2 : NNReal)) (by norm_num) hg hg0 hreal ?_
  have hcoe : (((2 : NNReal) : ℝ)) = (2 : ℝ) := by norm_num
  rw [hcoe]
  exact hsum

/-- **A power series with real coefficients takes real values on the real axis.**

This is the realness hypothesis of `Shields.oddPart_eq_of_summable`, discharged from the
coefficient statement alone: nothing beyond realness of `d` is used, and no property of `F`
beyond being the sum. -/
theorem im_eq_zero_of_hasSum_real {F : ℂ → ℂ} {d : ℕ → ℝ}
    (h : ∀ z : ℂ, HasSum (fun n ↦ (d n : ℂ) * z ^ n) (F z)) (x : ℝ) :
    (F (x : ℂ)).im = 0 := by
  have him := ((Complex.hasSum_iff _ _).1 (h (x : ℂ))).2
  have hz : (fun n : ℕ ↦ ((d n : ℂ) * (x : ℂ) ^ n).im) = fun _ ↦ (0 : ℝ) := by
    funext n
    rw [← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_im]
  rw [hz] at him
  exact him.unique hasSum_zero

/-- **The `(-1)`-points of `exp (g z - g (-z))` are the zeros of the even part of `exp ∘ g`.**

`exp (g (-z))` never vanishes and
`exp (g z - g (-z)) + 1 = (exp (g z) + exp (g (-z))) / exp (g (-z))`, so the two functions differ
by a nonvanishing analytic factor and their divisors agree point by point, multiplicity included.
Both functions are entire, so both divisors are nonnegative and the positive part is a no-op. -/
theorem divisor_negOne_eq_divisor_evenPart (hg : Differentiable ℂ g) :
    MeromorphicOn.divisor ((fun z ↦ Complex.exp (g z - g (-z))) · - (-1)) Set.univ
      = MeromorphicOn.divisor (fun z ↦ Complex.exp (g z) + Complex.exp (g (-z))) Set.univ := by
  have hgneg : Differentiable ℂ fun z : ℂ ↦ g (-z) := hg.comp differentiable_neg
  have hA : Differentiable ℂ fun z ↦ Complex.exp (g z - g (-z)) - (-1) :=
    ((hg.sub hgneg).cexp).sub_const _
  have hB : Differentiable ℂ fun z : ℂ ↦ Complex.exp (g (-z)) := hgneg.cexp
  have hfactor : (fun z ↦ Complex.exp (g z) + Complex.exp (g (-z)))
      = (fun z : ℂ ↦ Complex.exp (g (-z))) * fun z ↦ Complex.exp (g z - g (-z)) - (-1) := by
    funext z
    have hne : Complex.exp (g (-z)) ≠ 0 := Complex.exp_ne_zero _
    simp only [Pi.mul_apply, Complex.exp_sub]
    field
  ext z
  rw [hfactor,
    MeromorphicOn.divisor_apply (fun x _ ↦ (hA.analyticAt x).meromorphicAt) (Set.mem_univ z),
    MeromorphicOn.divisor_apply
      (fun x _ ↦ ((hB.mul hA).analyticAt x).meromorphicAt) (Set.mem_univ z),
    meromorphicOrderAt_mul_of_ne_zero (hB.analyticAt z) (Complex.exp_ne_zero _)]

/-- The divisor of an entire function is its own positive part. -/
theorem divisor_posPart_eq_self {f : ℂ → ℂ} (hf : Differentiable ℂ f) :
    (MeromorphicOn.divisor f Set.univ)⁺ = MeromorphicOn.divisor f Set.univ :=
  posPart_eq_self.2 (MeromorphicOn.AnalyticOnNhd.divisor_nonneg fun x _ ↦ hf.analyticAt x)

/-- The odd part of `g` is linear with a real coefficient, from a real coefficient sequence for
`exp ∘ g` together with the summability of `‖z‖ ^ (-p)`, at a single exponent `p < 3`, over the
zeros of the even part `z ↦ exp (g z) + exp (g (-z))`.

The two hypotheses are independent: the coefficients give realness on the real axis, the
summability gives the growth bound.  Stating the second over the even part rather than over the
`(-1)`-points of `exp (g z - g (-z))` is `Shields.divisor_negOne_eq_divisor_evenPart`; it makes the
remaining obligation a statement about the zeros of an entire function. -/
theorem oddPart_eq_of_hasSum_of_summable_rpow {d : ℕ → ℝ} {p : NNReal} (hp : (p : ℝ) < 3)
    (hg : Differentiable ℂ g) (hg0 : g 0 = 0)
    (hd : ∀ z : ℂ, HasSum (fun n ↦ (d n : ℂ) * z ^ n) (Complex.exp (g z)))
    (hsum : Summable fun z : ℂ ↦ ((MeromorphicOn.divisor
      (fun z ↦ Complex.exp (g z) + Complex.exp (g (-z))) Set.univ) z : ℝ) * ‖z‖ ^ (-(p : ℝ))) :
    ∃ γ : ℝ, ∀ z, g z - g (-z) = 2 * (γ : ℂ) * z := by
  refine oddPart_eq_of_summable_rpow hp hg hg0 (im_eq_zero_of_hasSum_real hd) ?_
  have hgneg : Differentiable ℂ fun z : ℂ ↦ g (-z) := hg.comp differentiable_neg
  have hA : Differentiable ℂ fun z ↦ Complex.exp (g z - g (-z)) - (-1) :=
    ((hg.sub hgneg).cexp).sub_const _
  rw [divisor_posPart_eq_self hA, divisor_negOne_eq_divisor_evenPart hg]
  exact hsum

/-- The exponent-two case of `Shields.oddPart_eq_of_hasSum_of_summable_rpow`. -/
theorem oddPart_eq_of_hasSum_of_summable {d : ℕ → ℝ} (hg : Differentiable ℂ g) (hg0 : g 0 = 0)
    (hd : ∀ z : ℂ, HasSum (fun n ↦ (d n : ℂ) * z ^ n) (Complex.exp (g z)))
    (hsum : Summable fun z : ℂ ↦ ((MeromorphicOn.divisor
      (fun z ↦ Complex.exp (g z) + Complex.exp (g (-z))) Set.univ) z : ℝ) * ‖z‖ ^ (-(2 : ℝ))) :
    ∃ γ : ℝ, ∀ z, g z - g (-z) = 2 * (γ : ℂ) * z := by
  refine oddPart_eq_of_hasSum_of_summable_rpow (p := (2 : NNReal)) (by norm_num) hg hg0 hd ?_
  have hcoe : (((2 : NNReal) : ℝ)) = (2 : ℝ) := by norm_num
  rw [hcoe]
  exact hsum


/-- **The even part of a power series carries the even half of its coefficients.**  If `exp ∘ g` is
the sum of `d n z ^ n`, then `z ↦ exp (g z) + exp (g (-z))` is the sum of
`(1 + (-1) ^ n) d n z ^ n`, which is `2 d n` at even `n` and `0` at odd `n`. -/
theorem hasSum_evenPart {d : ℕ → ℝ}
    (hd : ∀ z : ℂ, HasSum (fun n ↦ (d n : ℂ) * z ^ n) (Complex.exp (g z))) (z : ℂ) :
    HasSum (fun n ↦ (((1 + (-1 : ℝ) ^ n) * d n : ℝ) : ℂ) * z ^ n)
      (Complex.exp (g z) + Complex.exp (g (-z))) := by
  have h := (hd z).add (hd (-z))
  have hfun : (fun n ↦ (d n : ℂ) * z ^ n + (d n : ℂ) * (-z) ^ n)
      = fun n ↦ (((1 + (-1 : ℝ) ^ n) * d n : ℝ) : ℂ) * z ^ n := by
    funext n
    push_cast
    rw [neg_pow]
    ring
  rwa [hfun] at h

/-- The even part's coefficients are nonnegative as soon as the original's are. -/
theorem evenPart_coeff_nonneg {d : ℕ → ℝ} (hdnn : ∀ n, 0 ≤ d n) (n : ℕ) :
    0 ≤ (1 + (-1 : ℝ) ^ n) * d n := by
  rcases Nat.even_or_odd n with hn | hn
  · rw [hn.neg_one_pow]
    nlinarith [hdnn n]
  · rw [hn.neg_one_pow]
    simp

/-- **The odd part is linear as soon as the even part grows slower than `r ^ 3` on the positive
axis.**

When the coefficient sequence `d` of `exp ∘ g` is nonnegative, the even part
`E z = exp (g z) + exp (g (-z))` has nonnegative Taylor coefficients `(1 + (-1) ^ n) * d n`, so
`‖E z‖ ≤ E ‖z‖`: its maximum modulus on a circle sits at the positive real point.  A growth bound
`log E r = O(r ^ σ)` along the positive axis then bounds the counting function of the zeros of `E`
through Jensen's inequality, hence makes `∑ ‖z‖ ^ (-p)` converge over those zeros at every `p`
strictly between `σ` and `3`.  Nothing is assumed about where the zeros of `E` lie, and the bound
`σ < 3` is the exponent the rigidity step allows. -/
theorem oddPart_eq_of_hasSum_of_growth {d : ℕ → ℝ} {σ : ℝ} (hσ : 0 ≤ σ) (hσ3 : σ < 3)
    (hg : Differentiable ℂ g) (hg0 : g 0 = 0) (hdnn : ∀ n, 0 ≤ d n)
    (hd : ∀ z : ℂ, HasSum (fun n ↦ (d n : ℂ) * z ^ n) (Complex.exp (g z)))
    (hgrowth : (fun r : ℝ ↦ Real.log ‖Complex.exp (g (r : ℂ)) + Complex.exp (g (-(r : ℂ)))‖)
      =O[atTop] fun r : ℝ ↦ r ^ σ) :
    ∃ γ : ℝ, ∀ z, g z - g (-z) = 2 * (γ : ℂ) * z := by
  have hgneg : Differentiable ℂ fun z : ℂ ↦ g (-z) := hg.comp differentiable_neg
  have hF0 : (fun z : ℂ ↦ Complex.exp (g z) + Complex.exp (g (-z))) 0 ≠ 0 := by
    simp only [neg_zero, hg0, Complex.exp_zero]
    norm_num
  -- an exponent strictly between `σ` and `3`
  have hσ3' : σ < (σ + 3) / 2 := by linarith
  have hp3 : (((⟨(σ + 3) / 2, by positivity⟩ : NNReal) : ℝ)) < 3 := by
    linarith
  refine oddPart_eq_of_hasSum_of_summable_rpow (p := ⟨(σ + 3) / 2, by positivity⟩) hp3 hg hg0
    hd ?_
  exact summable_rpow_divisor_of_growth
    (F := fun z : ℂ ↦ Complex.exp (g z) + Complex.exp (g (-z)))
    (a := fun n ↦ (1 + (-1 : ℝ) ^ n) * d n) (p := (σ + 3) / 2)
    (hg.cexp.add hgneg.cexp) hF0 (evenPart_coeff_nonneg hdnn) (hasSum_evenPart hd) hσ hσ3' hgrowth


/-! ### Axiom footprint -/

/-- info: 'Shields.oddPart_eq_of_expConvergence_le_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms oddPart_eq_of_expConvergence_le_two

/-- info: 'Shields.oddPart_eq_of_summable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms oddPart_eq_of_summable

/-- info: 'Shields.oddPart_eq_of_hasSum_of_summable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms oddPart_eq_of_hasSum_of_summable

/-- info: 'Shields.oddPart_eq_of_hasSum_of_growth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms oddPart_eq_of_hasSum_of_growth

end Shields
