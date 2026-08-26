/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib
import ForgacsTran.CubicPhaseSign
import ForgacsTran.CubicWitnessInterior
import ForgacsTran.ViewingAngle

/-!
# The phase derivative at the cubic pencil

`eq:phase-derivative-bound` asserts that a continuous branch `ψ = arg W` of the
residue amplitude's argument has `|ψ'| ≤ κ` on every component of the arc minus
the amplitude's zero set.  This module proves it at `Q = (1-t)^3`, `r = 1`,
`B = 3t^2 + 1`, with an explicit `κ`, and delivers what
`ClauseThree.exists_phaseZeros` consumes: the binders `hΦc` and `hΦm` for
`Φ_M θ = (M+1)θ - ψ θ`.

Two facts carry the module, and both are special to this pencil.  The root
equation eliminates the spectral parameter from `eq:W-def`, leaving the amplitude
a rational function of the branch point alone,

`W(θ) = γ(3γ²+1)/((1-γ)²(2γ+1))`;

and the branch relation `2τ³cos θ = 3τ² - 1`, with its own derivative, eliminates
`θ` from `ψ' = Im(W'/W)`, leaving

`ψ'(θ) = 1 + 2(τ⁴+τ²+1)/(τ⁴+3) - 2/3 - 2(2τ²+1)/(3(τ²+2))`,

one summand per factor of `W`.  Since `0 < τ ≤ 1`, that is bounded by `3/2` at
every angle, so `κ` does not move with the subarc and `M` may be fixed before the
subarc is.  That quantifier order is what `thm:main` needs and what a
compactness argument on the subarc could not supply.

## Main statements

* `ftAmp_cubic_eq` — `eq:W-def` with the spectral parameter eliminated.
* `im_cubicAmpLogDeriv` — `eq:phase-derivative-bound` in closed form: `ψ'` as a
  rational function of `τ`, with no `θ` in it.
* `abs_im_cubicAmpLogDeriv_le` — that bound made explicit, `κ = 3/2`, uniform
  over the whole arc.
* `cubic_phase_binders` — `hΦc` and `hΦm` of `ClauseThree.exists_phaseZeros`,
  discharged at this pencil for every `M ≥ 1`.
* `cubic_exists_phaseZeros` — `prop:angular-discrepancy` at this pencil with no
  analytic binder assumed, the subarc quantified after `M`.

## Tags

cubic pencil, phase derivative, argument lift, angular discrepancy
-/

namespace ForgacsTran

open Polynomial Complex Set

variable {θ : ℝ}

/-! ### The branch point is off the real axis

Every denominator in the closed form below is a linear or quadratic factor
vanishing only on the real axis, and the branch meets the real axis only at the
endpoints.  So one fact -- `0 < Im γ` on the open arc -- clears all of them. -/

/-- The branch point's imaginary part, `τ(θ) sin θ`. -/
theorem im_ftPrincipal_cubicTau (θ : ℝ) :
    (ftPrincipal cubicTau θ).im = cubicTau θ * Real.sin θ := by
  rw [ftPrincipal, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.exp_ofReal_mul_I_im]
  ring

theorem im_ftPrincipal_cubicTau_pos (hθ : θ ∈ Set.Ioo 0 Real.pi) :
    0 < (ftPrincipal cubicTau θ).im := by
  rw [im_ftPrincipal_cubicTau]
  exact mul_pos (cubicTau_pos θ) (Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2)

theorem one_sub_ftPrincipal_cubicTau_ne_zero (hθ : θ ∈ Set.Ioo 0 Real.pi) :
    1 - ftPrincipal cubicTau θ ≠ 0 := by
  intro h
  have him := congrArg Complex.im h
  simp only [Complex.sub_im, Complex.one_im, Complex.zero_im, zero_sub, neg_eq_zero] at him
  exact (im_ftPrincipal_cubicTau_pos hθ).ne' him

theorem two_mul_ftPrincipal_cubicTau_add_one_ne_zero (hθ : θ ∈ Set.Ioo 0 Real.pi) :
    2 * ftPrincipal cubicTau θ + 1 ≠ 0 := by
  intro h
  have him := congrArg Complex.im h
  simp only [Complex.add_im, Complex.mul_im, Complex.one_im, Complex.zero_im,
    Complex.re_ofNat, Complex.im_ofNat] at him
  have := im_ftPrincipal_cubicTau_pos hθ
  linarith

/-! ### The amplitude is a rational function of the branch point

`eq:W-def` reads `W = -B(γ)/∂_tD(γ)`, and at this pencil the root equation
eliminates the spectral parameter from it: `cubicZ_eq_neg_div`'s `z = -(1-γ)³/γ`
turns `eval_derivative_ftDen_cubicQ`'s `∂_tD(γ) = -3(1-γ)² + z` into
`-(1-γ)²(2γ+1)/γ`, and

`W(θ) = γ(3γ²+1) / ((1-γ)²(2γ+1))`

with no `z` and no `τ` left.  This is what makes the phase derivative elementary
here: `ψ' = Im(W'/W)` is `Im(γ' L(γ))` for a fixed rational `L`, so the only
input from the branch is `γ'`. -/

/-- The cofactor at the branch point, `∂_tD(γ) = -(1-γ)²(2γ+1)/γ`. -/
theorem eval_derivative_ftDen_cubicQ_ftPrincipal (θ : ℝ) :
    (derivative (ftDen cubicQ 1 ((cubicZ (cubicTau θ) θ : ℝ) : ℂ))).eval
        (ftPrincipal cubicTau θ)
      = -((1 - ftPrincipal cubicTau θ) ^ 2 * (2 * ftPrincipal cubicTau θ + 1))
          / ftPrincipal cubicTau θ := by
  have hg := ftPrincipal_cubicTau_ne_zero θ
  rw [eval_derivative_ftDen_cubicQ, cubicZ_eq_neg_div θ]
  field_simp
  ring

/-- **`eq:W-def` at the cubic pencil, with the parameter eliminated.**  The
residue amplitude is the rational function `γ(3γ²+1)/((1-γ)²(2γ+1))` of the
branch point. -/
theorem ftAmp_cubic_eq (hθ : θ ∈ Set.Ioo 0 Real.pi) :
    ftAmp cubicQ witB 1 ((cubicZ (cubicTau θ) θ : ℝ) : ℂ) (ftPrincipal cubicTau θ)
      = ftPrincipal cubicTau θ * (3 * ftPrincipal cubicTau θ ^ 2 + 1)
        / ((1 - ftPrincipal cubicTau θ) ^ 2 * (2 * ftPrincipal cubicTau θ + 1)) := by
  have hg := ftPrincipal_cubicTau_ne_zero θ
  have h1 := one_sub_ftPrincipal_cubicTau_ne_zero hθ
  have h2 := two_mul_ftPrincipal_cubicTau_add_one_ne_zero hθ
  rw [ftAmp_eq_neg_div_derivative (ftDen_cubicQ_eval_ftPrincipal θ),
    eval_derivative_ftDen_cubicQ_ftPrincipal, witB_eval]
  field_simp


/-! ### The branch and the amplitude are differentiable along the arc

`cubicTau` has the closed form `1/(2cos((π-θ)/3))` on `[0,π]`, which is what
`hasDerivAt_cubicTau` reads its derivative off.  Nothing further is needed: the
amplitude is a rational function of `γ = τe^{iθ}` whose three denominators are
nonzero on the open arc. -/

/-- The branch function's derivative, as a name. -/
noncomputable def cubicTauDeriv (θ : ℝ) : ℝ :=
  -Real.sin ((Real.pi - θ) / 3) / (6 * Real.cos ((Real.pi - θ) / 3) ^ 2)

/-- The branch point's derivative, `γ' = e^{iθ}(τ' + iτ)`. -/
noncomputable def cubicGammaDeriv (θ : ℝ) : ℂ :=
  Complex.exp ((θ : ℂ) * I) * ((cubicTauDeriv θ : ℂ) + ((cubicTau θ : ℝ) : ℂ) * I)

theorem hasDerivAt_ftPrincipal_cubicTau (hθ : θ ∈ Set.Ioo 0 Real.pi) :
    HasDerivAt (ftPrincipal cubicTau) (cubicGammaDeriv θ) θ := by
  have hτ : HasDerivAt (fun t : ℝ => ((cubicTau t : ℝ) : ℂ)) ((cubicTauDeriv θ : ℂ)) θ :=
    (hasDerivAt_cubicTau hθ).ofReal_comp
  have hE : HasDerivAt (fun t : ℝ => Complex.exp (((t : ℝ) : ℂ) * I))
      (Complex.exp (((θ : ℝ) : ℂ) * I) * I) θ := by
    have : HasDerivAt (fun w : ℂ => Complex.exp (w * I))
        (Complex.exp (((θ : ℝ) : ℂ) * I) * I) (((θ : ℝ) : ℂ)) := by
      simpa using ((hasDerivAt_id (((θ : ℝ) : ℂ))).mul_const I).cexp
    exact this.comp_ofReal
  have hmul := hτ.mul hE
  have hfun : ftPrincipal cubicTau
      = fun t : ℝ => ((cubicTau t : ℝ) : ℂ) * Complex.exp (((t : ℝ) : ℂ) * I) := rfl
  rw [hfun]
  refine hmul.congr_deriv ?_
  rw [cubicGammaDeriv]
  ring

/-- The residue amplitude along the branch, as a function of the angle. -/
noncomputable def cubicAmp (θ : ℝ) : ℂ :=
  ftAmp cubicQ witB 1 ((cubicZ (cubicTau θ) θ : ℝ) : ℂ) (ftPrincipal cubicTau θ)

/-- The logarithmic derivative `W'/W = γ' L(γ)`, with

`L(t) = 1/t + 6t/(3t²+1) + 2/(1-t) - 2/(2t+1)`

the logarithmic derivative of `t(3t²+1)/((1-t)²(2t+1))`.  Off the amplitude's
zero this is `W'/W`; at the zero the middle term's denominator vanishes and the
name means nothing, which is why every statement below carries `θ ≠ π/2`. -/
noncomputable def cubicAmpLogDeriv (θ : ℝ) : ℂ :=
  cubicGammaDeriv θ * (1 / ftPrincipal cubicTau θ
    + 6 * ftPrincipal cubicTau θ / (3 * ftPrincipal cubicTau θ ^ 2 + 1)
    + 2 / (1 - ftPrincipal cubicTau θ)
    - 2 / (2 * ftPrincipal cubicTau θ + 1))

/-- `3γ² + 1 ≠ 0` off the amplitude's zero angle: this is `lem:amplitude-divisor`
at the witness, in the form the quotient rule consumes. -/
theorem three_mul_sq_ftPrincipal_add_one_ne_zero (hθ : θ ∈ Set.Ioo 0 Real.pi)
    (hhalf : θ ≠ Real.pi / 2) : 3 * ftPrincipal cubicTau θ ^ 2 + 1 ≠ 0 := by
  intro h
  refine hhalf ((witB_eval_ftPrincipal_eq_zero_iff ⟨hθ.1.le, hθ.2.le⟩).1 ?_)
  rw [witB_eval]
  exact h

/-- **`eq:phase-derivative-bound`, the differentiation step.**  The amplitude is
differentiable along the arc with `W' = L(γ)γ' · W`. -/
theorem hasDerivAt_cubicAmp (hθ : θ ∈ Set.Ioo 0 Real.pi) (hhalf : θ ≠ Real.pi / 2) :
    HasDerivAt cubicAmp (cubicAmpLogDeriv θ * cubicAmp θ) θ := by
  have hg := ftPrincipal_cubicTau_ne_zero θ
  have h1 := one_sub_ftPrincipal_cubicTau_ne_zero hθ
  have h2 := two_mul_ftPrincipal_cubicTau_add_one_ne_zero hθ
  have h3 := three_mul_sq_ftPrincipal_add_one_ne_zero hθ hhalf
  have hgd := hasDerivAt_ftPrincipal_cubicTau hθ
  have hDne : ((1 - ftPrincipal cubicTau θ) ^ 2 * (2 * ftPrincipal cubicTau θ + 1)) ≠ 0 :=
    mul_ne_zero (pow_ne_zero 2 h1) h2
  have hN := hgd.mul (((hgd.pow 2).const_mul (3 : ℂ)).add_const 1)
  have hD := (((hasDerivAt_const θ (1 : ℂ)).sub hgd).pow 2).mul
    ((hgd.const_mul (2 : ℂ)).add_const 1)
  have hquot := hN.div hD hDne
  refine (hquot.congr_deriv ?_).congr_of_eventuallyEq ?_
  swap
  · filter_upwards [Ioo_mem_nhds hθ.1 hθ.2] with t ht
    simpa [cubicAmp] using ftAmp_cubic_eq ht
  simp only [Pi.pow_apply, Pi.sub_apply, Pi.mul_apply]
  norm_num
  rw [cubicAmpLogDeriv, cubicAmp, ftAmp_cubic_eq hθ]
  have h1' : ftPrincipal cubicTau θ - 1 ≠ 0 := fun hc => h1 (by linear_combination -hc)
  have h2' : ftPrincipal cubicTau θ * 2 + 1 ≠ 0 := fun hc => h2 (by linear_combination hc)
  have h3' : ftPrincipal cubicTau θ ^ 2 * 3 + 1 ≠ 0 := fun hc => h3 (by linear_combination hc)
  field_simp
  ring


/-! ### The retained set, and continuity there

`cubicTheta` deletes `|θ - π/2| < 1` at every `M`, so the retained set is
contained in the open arc minus the amplitude's zero angle.  That set is where
every object below is regular, and it is open, which is what the lift's
hypotheses ask for. -/

/-- The open arc minus the amplitude's zero angle: the set on which the
amplitude is differentiable and nonvanishing. -/
def cubicRetained : Set ℝ := Set.Ioo 0 Real.pi \ {Real.pi / 2}

theorem isOpen_cubicRetained : IsOpen cubicRetained :=
  isOpen_Ioo.sdiff isClosed_singleton

theorem mem_cubicRetained_iff {θ : ℝ} :
    θ ∈ cubicRetained ↔ θ ∈ Set.Ioo 0 Real.pi ∧ θ ≠ Real.pi / 2 := Iff.rfl

/-- **`lem:amplitude-divisor` at the witness, as a nonvanishing statement.** -/
theorem cubicAmp_ne_zero {θ : ℝ} (hθ : θ ∈ cubicRetained) : cubicAmp θ ≠ 0 := by
  intro h
  exact hθ.2 ((ftAmp_witB_eq_zero_iff hθ.1).1 h)

theorem continuousAt_cubicTauDeriv {θ : ℝ} (hθ : θ ∈ Set.Icc 0 Real.pi) :
    ContinuousAt cubicTauDeriv θ := by
  have hc : 0 < Real.cos ((Real.pi - θ) / 3) := cos_third_pos hθ
  have hne : (6 : ℝ) * Real.cos ((Real.pi - θ) / 3) ^ 2 ≠ 0 :=
    (mul_pos (by norm_num) (pow_pos hc 2)).ne'
  exact ContinuousAt.div (by fun_prop) (by fun_prop) hne

theorem continuousAt_cubicGammaDeriv {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 Real.pi) :
    ContinuousAt cubicGammaDeriv θ := by
  have hτ : ContinuousAt (fun t : ℝ => ((cubicTau t : ℝ) : ℂ)) θ :=
    Complex.continuous_ofReal.continuousAt.comp (hasDerivAt_cubicTau hθ).continuousAt
  have hd : ContinuousAt (fun t : ℝ => ((cubicTauDeriv t : ℝ) : ℂ)) θ :=
    Complex.continuous_ofReal.continuousAt.comp
      (continuousAt_cubicTauDeriv ⟨hθ.1.le, hθ.2.le⟩)
  have hE : ContinuousAt (fun t : ℝ => Complex.exp ((t : ℂ) * I)) θ := by fun_prop
  exact hE.mul (hd.add (hτ.mul continuousAt_const))

theorem continuousAt_cubicAmpLogDeriv {θ : ℝ} (hθ : θ ∈ cubicRetained) :
    ContinuousAt cubicAmpLogDeriv θ := by
  have hg : ContinuousAt (ftPrincipal cubicTau) θ :=
    (hasDerivAt_ftPrincipal_cubicTau hθ.1).continuousAt
  have h0 := ftPrincipal_cubicTau_ne_zero θ
  have h1 := one_sub_ftPrincipal_cubicTau_ne_zero hθ.1
  have h2 := two_mul_ftPrincipal_cubicTau_add_one_ne_zero hθ.1
  have h3 := three_mul_sq_ftPrincipal_add_one_ne_zero hθ.1 hθ.2
  refine (continuousAt_cubicGammaDeriv hθ.1).mul ?_
  refine ContinuousAt.sub (ContinuousAt.add (ContinuousAt.add ?_ ?_) ?_) ?_
  · exact continuousAt_const.div hg h0
  · exact (continuousAt_const.mul hg).div
      ((continuousAt_const.mul (hg.pow 2)).add continuousAt_const) h3
  · exact continuousAt_const.div (continuousAt_const.sub hg) h1
  · exact continuousAt_const.div ((continuousAt_const.mul hg).add continuousAt_const) h2

theorem continuousAt_cubicAmp {θ : ℝ} (hθ : θ ∈ cubicRetained) : ContinuousAt cubicAmp θ :=
  (hasDerivAt_cubicAmp hθ.1 hθ.2).continuousAt

theorem continuousOn_cubicAmpDeriv :
    ContinuousOn (fun s => cubicAmpLogDeriv s * cubicAmp s) cubicRetained :=
  fun _ hx =>
    ((continuousAt_cubicAmpLogDeriv hx).mul (continuousAt_cubicAmp hx)).continuousWithinAt


/-! ### The phase derivative in closed form

`eq:phase-derivative-bound` asserts only that `κ` is finite.  At this pencil it
can be exhibited, because `ψ'` collapses to a rational function of the branch
modulus alone:

`ψ'(θ) = 1 + 2(τ⁴+τ²+1)/(τ⁴+3) - 2/3 - 2(2τ²+1)/(3(τ²+2))`,

one summand per factor of `W = γ(3γ²+1)/((1-γ)²(2γ+1))`, and **no `θ` survives in
it**.  Two eliminations do that.  The branch relation `2τ³cos θ = 3τ² - 1` gives
`cos θ` as a function of `τ`; and differentiating that same relation gives
`τ'`, which enters the four terms only through the products `τ'sin θ` and
`sin²θ`, both of which the relation makes rational in `τ`.  So the square root in
`τ' = -τ√(4τ²-1)/3` never appears.

The consequence is what the composition needs.  Compactness bounds `ψ'` on a
subarc but says nothing uniform as the subarc moves, while `0 < τ ≤ 1` bounds
this expression on the *whole* arc at once, so the same `κ` serves every subarc
and `M` may be chosen before the subarc rather than after it.  The three
singularities that the compactness route had to route around are visibly absent
here: each is a factor `(τ²-1)`, `(4τ²-1)`, `(3τ²-1)` that cancels between the
numerator and `‖·‖²` of the same factor of `W`, which is `lem:amplitude-divisor`'s
"the singular terms are real, hence disappear from `Im(W'/W)`" made explicit.

**Differs from the paper's route.**  `lem:amplitude-divisor` argues qualitatively
-- the singular part of `W'/W` at an amplitude zero or an endpoint is real, so it
drops from the imaginary part, and compactness of what is left supplies `κ`.  The
closed form below is not in the paper.  Its measured range, on
`scripts/check_cubic_phase_derivative.py`, is `ψ' ∈ [47/63, 7/6]`. -/

/-- **The branch relation, differentiated.**  `2τ³cos θ = 3τ² - 1` holds at every
angle, so its derivative vanishes; this is that derivative. -/
theorem cubicTau_branch_deriv (hθ : θ ∈ Set.Ioo 0 Real.pi) :
    -2 * Real.sin θ * cubicTau θ ^ 3
        + 6 * Real.cos θ * cubicTau θ ^ 2 * cubicTauDeriv θ
        - 6 * cubicTau θ * cubicTauDeriv θ = 0 := by
  have hτ : HasDerivAt cubicTau (cubicTauDeriv θ) θ := hasDerivAt_cubicTau hθ
  have h1 : HasDerivAt (fun x : ℝ => 2 * Real.cos x * cubicTau x ^ 3 - 3 * cubicTau x ^ 2 + 1)
      (-2 * Real.sin θ * cubicTau θ ^ 3
        + 6 * Real.cos θ * cubicTau θ ^ 2 * cubicTauDeriv θ
        - 6 * cubicTau θ * cubicTauDeriv θ) θ := by
    have hc := (Real.hasDerivAt_cos θ).const_mul (2 : ℝ)
    have h3 := hτ.pow 3
    have h2 := (hτ.pow 2).const_mul (3 : ℝ)
    refine (((hc.mul h3).sub h2).add_const 1).congr_deriv ?_
    simp only [Pi.pow_apply]
    push_cast
    ring
  have h0 : HasDerivAt (fun x : ℝ => 2 * Real.cos x * cubicTau x ^ 3 - 3 * cubicTau x ^ 2 + 1)
      0 θ := by
    have hfun : (fun x : ℝ => 2 * Real.cos x * cubicTau x ^ 3 - 3 * cubicTau x ^ 2 + 1)
        = fun _ : ℝ => (0 : ℝ) := funext fun x => cubicTau_branch x
    rw [hfun]
    exact hasDerivAt_const θ 0
  exact h1.unique h0

/-- `sin²θ` along the branch, rational in `τ`. -/
theorem cubicTau_sin_sq (θ : ℝ) :
    4 * cubicTau θ ^ 6 * Real.sin θ ^ 2
      = (cubicTau θ ^ 2 - 1) ^ 2 * (4 * cubicTau θ ^ 2 - 1) := by
  have hbr : 2 * Real.cos θ * cubicTau θ ^ 3 = 3 * cubicTau θ ^ 2 - 1 := by
    linarith [cubicTau_branch θ]
  have hpy : Real.cos θ ^ 2 + Real.sin θ ^ 2 = 1 := Real.cos_sq_add_sin_sq θ
  linear_combination (-(2 * Real.cos θ * cubicTau θ ^ 3 - 3 * cubicTau θ ^ 2 + 1)
      - 2 * (3 * cubicTau θ ^ 2 - 1)) * hbr + (4 * cubicTau θ ^ 6) * hpy

/-- **`τ' sin θ` is rational in `τ`.**  This is the identity that removes `θ`
from the phase derivative: `τ'` and `sin θ` are each irrational in `τ`, and only
their product occurs. -/
theorem cubicTauDeriv_mul_sin (hθ : θ ∈ Set.Ioo 0 Real.pi) :
    6 * cubicTau θ ^ 2 * (cubicTauDeriv θ * Real.sin θ)
      = (cubicTau θ ^ 2 - 1) * (4 * cubicTau θ ^ 2 - 1) := by
  have ht0 : 0 < cubicTau θ := cubicTau_pos θ
  have ht1 : cubicTau θ < 1 := cubicTau_lt_one hθ
  have hne : cubicTau θ ^ 2 - 1 ≠ 0 := by nlinarith
  have hA := cubicTau_branch_deriv hθ
  have hbr : 2 * Real.cos θ * cubicTau θ ^ 3 = 3 * cubicTau θ ^ 2 - 1 := by
    linarith [cubicTau_branch θ]
  have hs2 := cubicTau_sin_sq θ
  refine mul_left_cancel₀ hne ?_
  linear_combination (2 * cubicTau θ ^ 3 * Real.sin θ) * hA
    - (6 * cubicTau θ ^ 2 * cubicTauDeriv θ * Real.sin θ) * hbr + hs2

/-! ### Real and imaginary parts along the branch -/

theorem re_ftPrincipal_cubicTau (θ : ℝ) :
    (ftPrincipal cubicTau θ).re = cubicTau θ * Real.cos θ := by
  rw [ftPrincipal, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
  ring

theorem re_cubicGammaDeriv (θ : ℝ) :
    (cubicGammaDeriv θ).re
      = cubicTauDeriv θ * Real.cos θ - cubicTau θ * Real.sin θ := by
  rw [cubicGammaDeriv]
  simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
  ring

theorem im_cubicGammaDeriv (θ : ℝ) :
    (cubicGammaDeriv θ).im
      = cubicTauDeriv θ * Real.sin θ + cubicTau θ * Real.cos θ := by
  rw [cubicGammaDeriv]
  simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
  ring

/-- The imaginary part of a quotient, from a scaled numerator identity.  `k` is
the power of `τ` a term has to be cleared by before the branch relation applies,
and `d` the denominator of the value. -/
private theorem im_div_of_scaled {w z : ℂ} (hz : z ≠ 0) {n d k : ℝ} (hd : d ≠ 0) (hk : k ≠ 0)
    (h : k * d * (w.im * z.re - w.re * z.im) = k * n * Complex.normSq z) :
    (w / z).im = n / d := by
  have hns : Complex.normSq z ≠ 0 := fun hc => hz (Complex.normSq_eq_zero.1 hc)
  have h1 : d * (w.im * z.re - w.re * z.im) = n * Complex.normSq z :=
    mul_left_cancel₀ hk (by linear_combination h)
  have hdiv : (w / z).im = (w.im * z.re - w.re * z.im) / Complex.normSq z := by
    rw [Complex.div_im]; ring
  rw [hdiv, div_eq_div_iff hns hd]
  linear_combination h1


/-! ### The four factors, one at a time

`W = γ(3γ²+1)/((1-γ)²(2γ+1))`, so `W'/W` is a sum of four logarithmic
derivatives and `ψ'` is the sum of their imaginary parts.  Each is computed
here, and each comes out rational in `τ` alone. -/

theorem cubicAmpLogDeriv_split (θ : ℝ) :
    cubicAmpLogDeriv θ
      = cubicGammaDeriv θ / ftPrincipal cubicTau θ
        + 6 * ftPrincipal cubicTau θ * cubicGammaDeriv θ
            / (3 * ftPrincipal cubicTau θ ^ 2 + 1)
        + 2 * cubicGammaDeriv θ / (1 - ftPrincipal cubicTau θ)
        - 2 * cubicGammaDeriv θ / (2 * ftPrincipal cubicTau θ + 1) := by
  rw [cubicAmpLogDeriv]
  ring

/-- The factor `γ`: its logarithmic derivative has imaginary part exactly `1`,
because `arg γ = θ`. -/
theorem im_cubicTerm_gamma (θ : ℝ) :
    (cubicGammaDeriv θ / ftPrincipal cubicTau θ).im = 1 := by
  have key : (1 : ℝ) * 1 * ((cubicGammaDeriv θ).im * (ftPrincipal cubicTau θ).re
      - (cubicGammaDeriv θ).re * (ftPrincipal cubicTau θ).im)
      = 1 * 1 * Complex.normSq (ftPrincipal cubicTau θ) := by
    rw [Complex.normSq_apply, re_ftPrincipal_cubicTau, im_ftPrincipal_cubicTau,
      re_cubicGammaDeriv, im_cubicGammaDeriv]
    ring
  simpa using
    im_div_of_scaled (ftPrincipal_cubicTau_ne_zero θ) one_ne_zero one_ne_zero key

/-- The factor `(1-γ)^{-2}`: imaginary part exactly `-2/3`, with the `(τ²-1)`
of the endpoint cancelling between numerator and modulus. -/
theorem im_cubicTerm_one_sub (hθ : θ ∈ Set.Ioo 0 Real.pi) :
    (2 * cubicGammaDeriv θ / (1 - ftPrincipal cubicTau θ)).im = -2 / 3 := by
  have ht0 : 0 < cubicTau θ := cubicTau_pos θ
  have hpy : Real.cos θ ^ 2 + Real.sin θ ^ 2 = 1 := Real.cos_sq_add_sin_sq θ
  have hbr : 2 * Real.cos θ * cubicTau θ ^ 3 = 3 * cubicTau θ ^ 2 - 1 := by
    linarith [cubicTau_branch θ]
  have hts := cubicTauDeriv_mul_sin hθ
  refine im_div_of_scaled (one_sub_ftPrincipal_cubicTau_ne_zero hθ)
    (by norm_num : (3 : ℝ) ≠ 0) (pow_ne_zero 2 ht0.ne') ?_
  simp only [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
    Complex.one_re, Complex.one_im, Complex.re_ofNat, Complex.im_ofNat,
    Complex.normSq_apply]
  rw [re_ftPrincipal_cubicTau, im_ftPrincipal_cubicTau, re_cubicGammaDeriv,
    im_cubicGammaDeriv]
  linear_combination hbr - 4 * cubicTau θ ^ 4 * hpy + hts

/-- The factor `(2γ+1)^{-1}`: the `(4τ²-1)` of the upper endpoint cancels. -/
theorem im_cubicTerm_two_add (hθ : θ ∈ Set.Ioo 0 Real.pi) :
    (2 * cubicGammaDeriv θ / (2 * ftPrincipal cubicTau θ + 1)).im
      = 2 * (2 * cubicTau θ ^ 2 + 1) / (3 * (cubicTau θ ^ 2 + 2)) := by
  have ht0 : 0 < cubicTau θ := cubicTau_pos θ
  have hpy : Real.cos θ ^ 2 + Real.sin θ ^ 2 = 1 := Real.cos_sq_add_sin_sq θ
  have hbr : 2 * Real.cos θ * cubicTau θ ^ 3 = 3 * cubicTau θ ^ 2 - 1 := by
    linarith [cubicTau_branch θ]
  have hts := cubicTauDeriv_mul_sin hθ
  have hd : (3 * (cubicTau θ ^ 2 + 2) : ℝ) ≠ 0 := by positivity
  refine im_div_of_scaled (two_mul_ftPrincipal_cubicTau_add_one_ne_zero hθ) hd
    (pow_ne_zero 2 ht0.ne') ?_
  simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
    Complex.one_re, Complex.one_im, Complex.re_ofNat, Complex.im_ofNat,
    Complex.normSq_apply]
  rw [re_ftPrincipal_cubicTau, im_ftPrincipal_cubicTau, re_cubicGammaDeriv,
    im_cubicGammaDeriv]
  linear_combination (2 - 5 * cubicTau θ ^ 2) * hbr
    + (-4 * cubicTau θ ^ 6 + 16 * cubicTau θ ^ 4) * hpy
    + (cubicTau θ ^ 2 + 2) * hts

/-- The factor `3γ²+1`, the amplitude's divisor: the `(3τ²-1)` of the zero at
`θ = π/2` cancels, which is `lem:amplitude-divisor`'s "the singular term is
real" at this pencil. -/
theorem im_cubicTerm_amp (hθ : θ ∈ Set.Ioo 0 Real.pi) (hhalf : θ ≠ Real.pi / 2) :
    (6 * ftPrincipal cubicTau θ * cubicGammaDeriv θ
        / (3 * ftPrincipal cubicTau θ ^ 2 + 1)).im
      = 2 * (cubicTau θ ^ 4 + cubicTau θ ^ 2 + 1) / (cubicTau θ ^ 4 + 3) := by
  have ht0 : 0 < cubicTau θ := cubicTau_pos θ
  have hpy : Real.cos θ ^ 2 + Real.sin θ ^ 2 = 1 := Real.cos_sq_add_sin_sq θ
  have hbr : 2 * Real.cos θ * cubicTau θ ^ 3 = 3 * cubicTau θ ^ 2 - 1 := by
    linarith [cubicTau_branch θ]
  have hts := cubicTauDeriv_mul_sin hθ
  have hd : (cubicTau θ ^ 4 + 3 : ℝ) ≠ 0 := by positivity
  refine im_div_of_scaled (three_mul_sq_ftPrincipal_add_one_ne_zero hθ hhalf) hd ht0.ne' ?_
  simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
    Complex.one_re, Complex.one_im, Complex.re_ofNat, Complex.im_ofNat,
    Complex.normSq_apply]
  rw [re_ftPrincipal_cubicTau, im_ftPrincipal_cubicTau, re_cubicGammaDeriv,
    im_cubicGammaDeriv]
  linear_combination
    (-9 * Real.cos θ ^ 3 * cubicTau θ ^ 4 + 18 * Real.cos θ ^ 3 * cubicTau θ ^ 2
      - 27 * Real.cos θ ^ 2 * cubicTau θ ^ 3 / 2 + 63 * Real.cos θ ^ 2 * cubicTau θ / 2
      - 9 * Real.cos θ * Real.sin θ ^ 2 * cubicTau θ ^ 4
      + 18 * Real.cos θ * Real.sin θ ^ 2 * cubicTau θ ^ 2
      + 3 * Real.cos θ * cubicTau θ ^ 4 - 30 * Real.cos θ * cubicTau θ ^ 2
      + 6 * Real.cos θ + 6 * cubicTauDeriv θ * Real.sin θ * cubicTau θ ^ 3
      - 27 * Real.sin θ ^ 2 * cubicTau θ ^ 3 / 2 + 63 * Real.sin θ ^ 2 * cubicTau θ / 2
      + 9 * cubicTau θ ^ 3 / 2 - 69 * cubicTau θ / 2) * hbr
    + (-18 * Real.cos θ * cubicTau θ ^ 2 - 18 * Real.sin θ ^ 2 * cubicTau θ ^ 7
      + 36 * Real.sin θ ^ 2 * cubicTau θ ^ 5 - 12 * cubicTau θ ^ 7
      + 15 * cubicTau θ ^ 5 / 2 + 102 * cubicTau θ ^ 3 - 63 * cubicTau θ / 2) * hpy
    + (6 * Real.cos θ + 3 * cubicTau θ ^ 3 - cubicTau θ) * hts

/-- **`eq:phase-derivative-bound` in closed form at the cubic pencil.**  The
phase derivative is a rational function of the branch modulus with no `θ` in it. -/
theorem im_cubicAmpLogDeriv (hθ : θ ∈ Set.Ioo 0 Real.pi) (hhalf : θ ≠ Real.pi / 2) :
    (cubicAmpLogDeriv θ).im
      = 1 + 2 * (cubicTau θ ^ 4 + cubicTau θ ^ 2 + 1) / (cubicTau θ ^ 4 + 3)
        - 2 / 3 - 2 * (2 * cubicTau θ ^ 2 + 1) / (3 * (cubicTau θ ^ 2 + 2)) := by
  rw [cubicAmpLogDeriv_split, Complex.sub_im, Complex.add_im, Complex.add_im,
    im_cubicTerm_gamma, im_cubicTerm_amp hθ hhalf, im_cubicTerm_one_sub hθ,
    im_cubicTerm_two_add hθ]
  ring


/-- **`eq:phase-derivative-bound` with an explicit constant, uniform over the
whole arc.**  `κ = 3/2` serves at every angle, so the same constant serves every
subarc and `M` may be fixed before the subarc.

`3/2` is not the supremum: `ψ'` runs over `[47/63, 7/6]`
(`scripts/check_cubic_phase_derivative.py`).  It is the bound the two crude
estimates below give, and it is already low enough that `M ≥ 1` clears it. -/
theorem abs_im_cubicAmpLogDeriv_le (hθ : θ ∈ Set.Ioo 0 Real.pi) (hhalf : θ ≠ Real.pi / 2) :
    |(cubicAmpLogDeriv θ).im| ≤ 3 / 2 := by
  have ht0 : 0 < cubicTau θ := cubicTau_pos θ
  have ht1 : cubicTau θ ≤ 1 := cubicTau_le_one θ
  have h1 : (0 : ℝ) < cubicTau θ ^ 4 + 3 := by positivity
  have h2 : (0 : ℝ) < 3 * (cubicTau θ ^ 2 + 2) := by positivity
  have ht2 : cubicTau θ ^ 2 ≤ 1 := by nlinarith
  have ht4 : cubicTau θ ^ 4 ≤ 1 := by nlinarith
  have hA : 2 * (cubicTau θ ^ 4 + cubicTau θ ^ 2 + 1) / (cubicTau θ ^ 4 + 3) ≤ 3 / 2 := by
    rw [div_le_iff₀ h1]; linarith
  have hA0 : 0 ≤ 2 * (cubicTau θ ^ 4 + cubicTau θ ^ 2 + 1) / (cubicTau θ ^ 4 + 3) := by
    positivity
  have hB : 2 * (2 * cubicTau θ ^ 2 + 1) / (3 * (cubicTau θ ^ 2 + 2)) ≤ 2 / 3 := by
    rw [div_le_iff₀ h2]; linarith
  have hB0 : 1 / 3 ≤ 2 * (2 * cubicTau θ ^ 2 + 1) / (3 * (cubicTau θ ^ 2 + 2)) := by
    rw [le_div_iff₀ h2]; nlinarith [sq_nonneg (cubicTau θ)]
  rw [im_cubicAmpLogDeriv hθ hhalf, abs_le]
  constructor <;> linarith

theorem abs_im_cubicAmpLogDeriv_le_of_mem {θ : ℝ} (hθ : θ ∈ cubicRetained) :
    |(cubicAmpLogDeriv θ).im| ≤ 3 / 2 :=
  abs_im_cubicAmpLogDeriv_le hθ.1 hθ.2

/-! ### The continuous branch of the argument

`eq:phase-derivative-bound` quantifies over "a continuous branch `ψ = arg W`" on
a component of the complement of the amplitude's zero set.  Here the branch is
built rather than hypothesized, by the `logLift` of `sec:geometry`: `ψ` is the
imaginary part of `log W(u) + ∫ W'/W`, so `ψ' = Im(W'/W)` holds by construction
and `W = ‖W‖e^{iψ}` throughout the subarc.  The bound on `ψ'` is then the closed
form above, which needs no compactness and is the same at every subarc.

**Differs from the paper's route.**  `lem:amplitude-divisor` bounds `ψ'` on each
component of `(0,π/r)` minus the amplitude's zeros, endpoints included, by
identifying and discarding the real singular parts.  This module bounds it on
subarcs of the *open* arc that miss the zero, which is the only form
`exists_phaseZeros` consumes; the endpoint analysis of `eq:W-endpoint-form` is
not reproduced, and neither endpoint of `(0,π)` is in `cubicRetained`. -/

/-- The continuous branch of `arg W` on a subarc starting at `u`. -/
noncomputable def cubicPsi (u : ℝ) : ℝ → ℝ :=
  polarAngle cubicAmp (fun s => cubicAmpLogDeriv s * cubicAmp s) 0 u

/-- `ftPrincipalAmp` at the witness is `‖W‖`. -/
theorem ftPrincipalAmp_cubic_eq (θ : ℝ) :
    ftPrincipalAmp cubicQ witB 1 (fun θ' => cubicZ (cubicTau θ') θ') cubicTau θ
      = ‖cubicAmp θ‖ := rfl

/-- **`eq:principal-decomposition`'s polar form at the witness.**  `W = ‖W‖e^{iψ}`
on the subarc, with `ψ` the constructed branch. -/
theorem cubicAmp_eq_polar {u v : ℝ} (huv : u ≤ v) (hsub : Set.Icc u v ⊆ cubicRetained)
    {θ : ℝ} (hθ : θ ∈ Set.Icc u v) :
    cubicAmp θ = ((‖cubicAmp θ‖ : ℝ) : ℂ) * Complex.exp ((cubicPsi u θ : ℂ) * I) := by
  have hd := polar_decomposition (γ := cubicAmp)
    (dγ := fun s => cubicAmpLogDeriv s * cubicAmp s) (β := 0) (U := cubicRetained)
    huv isOpen_cubicRetained hsub
    (fun s hs => hasDerivAt_cubicAmp hs.1 hs.2) continuousOn_cubicAmpDeriv
    (fun s hs => cubicAmp_ne_zero (hsub hs)) hθ
  rw [sub_zero] at hd
  have hnorm : ‖cubicAmp θ‖
      = polarModulus cubicAmp (fun s => cubicAmpLogDeriv s * cubicAmp s) 0 u θ := by
    rw [hd, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (polarModulus_pos _ _ _ _ _)]
  rw [hnorm]
  exact hd

/-- **`eq:phase-derivative-bound`, the identity `ψ' = Im(W'/W)`.**  The
constructed branch differentiates to the imaginary part of the amplitude's
logarithmic derivative. -/
theorem hasDerivAt_cubicPsi {u v : ℝ} (hsub : Set.Icc u v ⊆ cubicRetained)
    {θ : ℝ} (hθ : θ ∈ Set.Icc u v) :
    HasDerivAt (cubicPsi u) ((cubicAmpLogDeriv θ).im) θ := by
  have h := hasDerivAt_polarAngle (γ := cubicAmp)
    (dγ := fun s => cubicAmpLogDeriv s * cubicAmp s) (β := 0) (a := u) (b := v)
    isOpen_cubicRetained hsub
    (fun s hs => hasDerivAt_cubicAmp hs.1 hs.2) continuousOn_cubicAmpDeriv
    (fun s hs => cubicAmp_ne_zero (hsub hs)) hθ
  have hne := cubicAmp_ne_zero (hsub hθ)
  rw [sub_zero, mul_div_assoc, div_self hne, mul_one] at h
  exact h

/-- **`eq:phase-derivative-bound` integrated.**  The phase's variation across the
subarc is at most `3/2` times its length.  This is the form
`prop:angular-discrepancy` consumes: it turns the derivative bound into the
lower bound `Φ(v) - Φ(u) ≥ (M - 1/2)(v - u)` on the turning. -/
theorem cubicPsi_sub_le {u v : ℝ} (huv : u ≤ v) (hsub : Set.Icc u v ⊆ cubicRetained) :
    cubicPsi u v - cubicPsi u u ≤ 3 / 2 * (v - u) := by
  have hmono : MonotoneOn (fun θ => 3 / 2 * θ - cubicPsi u θ) (Set.Icc u v) := by
    have hlin : ∀ x : ℝ, HasDerivAt (fun θ : ℝ => 3 / 2 * θ) (3 / 2 : ℝ) x := fun x => by
      simpa using (hasDerivAt_id x).const_mul (3 / 2 : ℝ)
    refine monotoneOn_of_deriv_nonneg (convex_Icc u v) ?_ ?_ ?_
    · intro x hx
      exact ((continuousAt_const.mul continuousAt_id).sub
        (hasDerivAt_cubicPsi hsub hx).continuousAt).continuousWithinAt
    · rw [interior_Icc]
      intro x hx
      exact (((hlin x).sub
        (hasDerivAt_cubicPsi hsub ⟨hx.1.le, hx.2.le⟩)).differentiableAt).differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      have hxm : x ∈ Set.Icc u v := ⟨hx.1.le, hx.2.le⟩
      have hD : HasDerivAt (fun θ => 3 / 2 * θ - cubicPsi u θ)
          ((3 / 2 : ℝ) - (cubicAmpLogDeriv x).im) x :=
        (hlin x).sub (hasDerivAt_cubicPsi hsub hxm)
      rw [hD.deriv]
      have h2 : (cubicAmpLogDeriv x).im ≤ 3 / 2 :=
        le_trans (le_abs_self _) (abs_im_cubicAmpLogDeriv_le_of_mem (hsub hxm))
      linarith
  have h := hmono (Set.left_mem_Icc.2 huv) (Set.right_mem_Icc.2 huv) huv
  simp only at h
  linarith

/-! ### `hΦc` and `hΦm` at the cubic pencil

`ClauseThree.exists_phaseZeros` takes the phase's continuity and strict
monotonicity as binders, over an unspecified `ψ` tied to the amplitude only
through `hpolar`.  Both are delivered here, for one `ψ` that meets `hpolar`
globally: on the subarc it is the constructed branch, and off it the principal
argument, which meets the identity pointwise for the trivial reason that
`‖w‖e^{i arg w} = w` for every `w`.

Strict monotonicity is where `M` enters, and it enters exactly as
`eq:phase-derivative-bound` predicts: `Φ' = (M+1) - ψ' ≥ (M+1) - 3/2`, so every
`M ≥ 1` serves, at every subarc. -/

/-- **`hΦc` and `hΦm` of `ClauseThree.exists_phaseZeros`, discharged at
`Q = (1-t)^3`, `r = 1`, `B = 3t^2 + 1`.**  On a compact subarc of the open arc
missing the amplitude's zero angle there is a phase `ψ` satisfying `hpolar`
whose `Φ_M = (M+1)θ - ψ` is continuous at every `M`, strictly increasing at
every `M ≥ 1`, and whose variation across the subarc is at most `3/2` times its
length.  The threshold is `1` because `eq:phase-derivative-bound` holds
here with `κ = 3/2`, uniformly in the subarc: `M + 1 ≥ 2 > 3/2`. -/
theorem cubic_phase_binders {u v : ℝ} (huv : u ≤ v) (hsub : Set.Icc u v ⊆ cubicRetained) :
    ∃ ψ : ℝ → ℝ,
      (∀ θ : ℝ, ftAmp cubicQ witB 1 ((cubicZ (cubicTau θ) θ : ℝ) : ℂ)
          (ftPrincipal cubicTau θ)
        = ((ftPrincipalAmp cubicQ witB 1 (fun θ' => cubicZ (cubicTau θ') θ') cubicTau θ : ℝ) : ℂ)
          * Complex.exp ((ψ θ : ℂ) * Complex.I)) ∧
      (∀ M : ℕ, ContinuousOn (fun θ => ((M : ℝ) + 1) * θ - ψ θ) (Set.Icc u v)) ∧
      (∀ M : ℕ, 1 ≤ M →
        StrictMonoOn (fun θ => ((M : ℝ) + 1) * θ - ψ θ) (Set.Icc u v)) ∧
      ψ v - ψ u ≤ 3 / 2 * (v - u) := by
  classical
  refine ⟨fun θ => if θ ∈ Set.Icc u v then cubicPsi u θ else Complex.arg (cubicAmp θ),
    ?_, ?_, ?_, ?_⟩
  · intro θ
    rw [ftPrincipalAmp_cubic_eq]
    by_cases h : θ ∈ Set.Icc u v
    · simp only [h, if_true]
      exact cubicAmp_eq_polar huv hsub h
    · simp only [h, if_false]
      exact (Complex.norm_mul_exp_arg_mul_I (cubicAmp θ)).symm
  · intro M
    have heq : Set.EqOn
        (fun θ => ((M : ℝ) + 1) * θ
          - (if θ ∈ Set.Icc u v then cubicPsi u θ else Complex.arg (cubicAmp θ)))
        (fun θ => ((M : ℝ) + 1) * θ - cubicPsi u θ) (Set.Icc u v) := by
      intro x hx
      simp [hx]
    refine ContinuousOn.congr ?_ heq
    intro x hx
    exact ((continuousAt_const.mul continuousAt_id).sub
      (hasDerivAt_cubicPsi hsub hx).continuousAt).continuousWithinAt
  · intro M hM
    have hmain : StrictMonoOn (fun θ => ((M : ℝ) + 1) * θ - cubicPsi u θ) (Set.Icc u v) := by
      refine strictMonoOn_of_deriv_pos (convex_Icc u v) ?_ ?_
      · intro x hx
        exact ((continuousAt_const.mul continuousAt_id).sub
          (hasDerivAt_cubicPsi hsub hx).continuousAt).continuousWithinAt
      · intro x hx
        rw [interior_Icc] at hx
        have hxm : x ∈ Set.Icc u v := ⟨hx.1.le, hx.2.le⟩
        have hlin : HasDerivAt (fun θ : ℝ => ((M : ℝ) + 1) * θ) ((M : ℝ) + 1) x := by
          simpa using (hasDerivAt_id x).const_mul ((M : ℝ) + 1)
        have hD : HasDerivAt (fun θ => ((M : ℝ) + 1) * θ - cubicPsi u θ)
            (((M : ℝ) + 1) - (cubicAmpLogDeriv x).im) x :=
          hlin.sub (hasDerivAt_cubicPsi hsub hxm)
        rw [hD.deriv]
        have h1 := abs_im_cubicAmpLogDeriv_le_of_mem (hsub hxm)
        have h2 : (cubicAmpLogDeriv x).im ≤ 3 / 2 := le_trans (le_abs_self _) h1
        have h3 : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
        linarith
    intro a ha b hb hab
    have h := hmain ha hb hab
    simpa [ha, hb] using h
  · simp only [if_pos (Set.left_mem_Icc.2 huv), if_pos (Set.right_mem_Icc.2 huv)]
    exact cubicPsi_sub_le huv hsub


/-! ### The count, with nothing assumed

`exists_phaseZeros` has five binders.  `hsign` and `hz` were discharged at this
pencil in `CubicPhaseSign`, and `hΦc`, `hΦm` are discharged above, so the
theorem applies here with no analytic hypothesis left standing.  What the
remaining plumbing does is choose `M` large enough for two reasons at once: past
`cubic_weighted_dominance`'s own threshold, and past `1`, which is what
`eq:phase-derivative-bound`'s uniform `κ = 3/2` costs.

**The subarc is chosen after `M`, not before it.**  That is the quantifier order
`thm:main` needs, and it is available only because the phase bound is uniform:
were `κ` produced by compactness on the given subarc it would move with the
subarc, and the windows `h/M` of `eq:retained-range` shrink the subarc as `M`
grows. -/

/-- **The count on one subarc, with the dominance bound taken as given.**  Every
binder of `ClauseThree.exists_phaseZeros` is discharged at this pencil except the
`eq:dominance-bound` estimate itself, which is what `thm:weighted-dominance`
supplies and which enters here as `hdom`.  Isolating it this way is what lets the
same count be run against a different family of deleted windows. -/
theorem cubic_phaseZeros_of_dominance {u v : ℝ} (huv : u ≤ v)
    (hsubR : Set.Icc u v ⊆ cubicRetained) {M : ℕ} (hM1 : 1 ≤ M)
    (hdom : ∀ θ ∈ Set.Icc u v,
      ftRemainder cubicQ witB 1 (fun θ' => cubicZ (cubicTau θ') θ') cubicTau M θ
        ≤ ftPrincipalAmp cubicQ witB 1 (fun θ' => cubicZ (cubicTau θ') θ') cubicTau θ / 2)
    (P : Polynomial ℝ) (hP : P.map (algebraMap ℝ ℂ) = ftCoeffPoly cubicQ witB 1 M) :
    ∃ (ψ : ℝ → ℝ) (Z : Finset ℂ),
      (∀ θ : ℝ, ftAmp cubicQ witB 1 ((cubicZ (cubicTau θ) θ : ℝ) : ℂ)
          (ftPrincipal cubicTau θ)
        = ((ftPrincipalAmp cubicQ witB 1 (fun θ' => cubicZ (cubicTau θ') θ')
            cubicTau θ : ℝ) : ℂ) * Complex.exp ((ψ θ : ℂ) * Complex.I)) ∧
      (((((M : ℝ) + 1) * v - ψ v) - (((M : ℝ) + 1) * u - ψ u)) / Real.pi - 2 : ℝ)
          ≤ (Z.card : ℝ) ∧
      (∀ w ∈ Z, (P.map (algebraMap ℝ ℂ)).IsRoot w) ∧
      (∀ w ∈ Z, w ∈ Complex.ofReal ''
        (Set.Icc (cubicZ (cubicTau u) u) (cubicZ (cubicTau v) v))) ∧
      ((((M : ℝ) - 1 / 2) * (v - u) / Real.pi - 2 : ℝ) ≤ (Z.card : ℝ)) := by
  obtain ⟨ψ, hpolar, hΦc, hΦm, hvar⟩ := cubic_phase_binders huv hsubR
  have hzmono : StrictMonoOn (fun θ => cubicZ (cubicTau θ) θ) (Set.Icc u v) :=
    cubicZ_strictMonoOn.mono fun θ hθ => ⟨(hsubR hθ).1.1.le, (hsubR hθ).1.2.le⟩
  have hsign : ∀ θ ∈ Set.Icc u v, ∀ k : ℤ,
      ((M : ℝ) + 1) * θ - ψ θ = (k : ℝ) * Real.pi →
        0 < stripSign k * P.eval (cubicZ (cubicTau θ) θ) := fun θ hθ k hphase =>
    sign_at_phase_point_of_ftDominance hP (cubicTau_pos θ)
      (cubicAmp_ne_zero (hsubR hθ)) (hpolar θ) (hdom θ hθ) hphase
  obtain ⟨Z, hZ1, hZ2, hZ3⟩ :=
    exists_phaseZeros P huv (hΦc M) (hΦm M hM1) hzmono hsign
  refine ⟨ψ, Z, hpolar, hZ1, hZ2, hZ3, le_trans ?_ hZ1⟩
  -- `Φ(v) - Φ(u) ≥ (M - 1/2)(v - u)`, the derivative bound integrated
  have hMR : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM1
  have hkey : ((M : ℝ) - 1 / 2) * (v - u)
      ≤ ((M : ℝ) + 1) * v - ψ v - (((M : ℝ) + 1) * u - ψ u) := by nlinarith [huv, hvar]
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  have hdiv : ((M : ℝ) - 1 / 2) * (v - u) / Real.pi
      ≤ (((M : ℝ) + 1) * v - ψ v - (((M : ℝ) + 1) * u - ψ u)) / Real.pi :=
    div_le_div_of_nonneg_right hkey hπ.le
  linarith

/-- **`prop:angular-discrepancy` at the cubic pencil, with no analytic binder
assumed.**  Past one threshold in `M`, on every compact subarc of the retained
range of `eq:retained-range` that misses the deleted window, the weight's
coefficient polynomial has at least `(Φ(v) - Φ(u))/π - 2` real zeros in the
spectral interval the subarc carries -- and, `eq:phase-derivative-bound`
integrated, at least `(M - 1/2)(v - u)/π - 2` of them, which is the form a count
over several components adds up. -/
theorem cubic_exists_phaseZeros :
    ∃ h > (0 : ℝ), ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
      ∀ u v : ℝ, u ≤ v → Set.Icc u v ⊆ Set.Ioo 0 Real.pi →
        h / M ≤ u → v ≤ Real.pi - h / M →
        (∀ θ ∈ Set.Icc u v, θ ∉ cubicTheta M) →
        ∀ P : Polynomial ℝ, P.map (algebraMap ℝ ℂ) = ftCoeffPoly cubicQ witB 1 M →
        ∃ (ψ : ℝ → ℝ) (Z : Finset ℂ),
          (∀ θ : ℝ, ftAmp cubicQ witB 1 ((cubicZ (cubicTau θ) θ : ℝ) : ℂ)
              (ftPrincipal cubicTau θ)
            = ((ftPrincipalAmp cubicQ witB 1 (fun θ' => cubicZ (cubicTau θ') θ')
                cubicTau θ : ℝ) : ℂ) * Complex.exp ((ψ θ : ℂ) * Complex.I)) ∧
          (((((M : ℝ) + 1) * v - ψ v) - (((M : ℝ) + 1) * u - ψ u)) / Real.pi - 2 : ℝ)
              ≤ (Z.card : ℝ) ∧
          (∀ w ∈ Z, (P.map (algebraMap ℝ ℂ)).IsRoot w) ∧
          (∀ w ∈ Z, w ∈ Complex.ofReal ''
            (Set.Icc (cubicZ (cubicTau u) u) (cubicZ (cubicTau v) v))) ∧
          ((((M : ℝ) - 1 / 2) * (v - u) / Real.pi - 2 : ℝ) ≤ (Z.card : ℝ)) := by
  obtain ⟨h, hh, M₀, hdomAll⟩ := cubic_weighted_dominance
  refine ⟨h, hh, max M₀ 1, fun M hM u v huv hsub hu hv hwin P hP => ?_⟩
  have hM₀ : M₀ ≤ M := le_trans (le_max_left _ _) hM
  have hM1 : 1 ≤ M := le_trans (le_max_right _ _) hM
  have hsubR : Set.Icc u v ⊆ cubicRetained := by
    intro θ hθ
    refine ⟨hsub hθ, ?_⟩
    intro hhalf
    refine hwin θ hθ ?_
    rw [mem_cubicTheta, hhalf]
    simp
  have hdom : ∀ θ ∈ Set.Icc u v,
      ftRemainder cubicQ witB 1 (fun θ' => cubicZ (cubicTau θ') θ') cubicTau M θ
        ≤ ftPrincipalAmp cubicQ witB 1 (fun θ' => cubicZ (cubicTau θ') θ') cubicTau θ / 2 :=
    fun θ hθ => hdomAll M hM₀ θ (le_trans hu hθ.1) (le_trans hθ.2 hv) (hwin θ hθ)
  exact cubic_phaseZeros_of_dominance huv hsubR hM1 hdom P hP

end ForgacsTran
