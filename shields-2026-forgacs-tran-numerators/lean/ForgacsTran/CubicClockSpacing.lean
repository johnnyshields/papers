/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import ForgacsTran.ConsequencesComposition.ClockSpacing
import ForgacsTran.CubicPhaseDerivative

/-!
# `prop:local-strong-clock` at the cubic pencil, with the branch side discharged

`ft_local_strong_clock_on_FM` reaches `eq:local-strong-clock` for the zeros of
`F_M` themselves, and takes everything it needs as a binder.  Roughly half of
those binders are about the **branch** — the phase and its derivative, the
monotonicity of `Φ_M`, the positivity of `τ` and of `|W|`, the realness of the
coefficient polynomial — and at the cubic pencil all of them are theorems rather
than hypotheses.  `cubic_local_strong_clock` supplies them.

## Main statements

* `cubic_local_strong_clock` — `eq:local-strong-clock` at the cubic pencil, with
  every branch-side and every regularity input produced from the closed-form
  branch, and only the remainder left as a binder.
* `cubicTauDeriv2`, `cubicGammaDeriv2`, `cubicAmpLogDeriv2`, `cubicAmpDeriv2` and
  their `hasDerivAt`/`continuousAt` lemmas — the second-derivative layer, which
  is what supplies `κ_2`.

## Implementation notes

**Nothing is left.**  `CubicInteriorRemainder.cubic_local_strong_clock_closed`
discharges every binder of this theorem, the remainder's included: the value side
from the contour bound, the derivative side from
`DominanceFT.ftCoeff_re_sub_principal_eq_contour_re` differentiated through
`PoleExpansion.hasDerivAt_ftContourRem_comp`.  This theorem is the shape with the
remainder still a binder, kept because it is the one the general branch will be
instantiated at.

**Measured.**  `scripts/check_cubic_strong_clock.py` runs this pencil on
`[1.75, 2.55]`: the quantization `eq:local-phase-quantization` holds to `2.6e-31`
at `M = 40`, and the spacing residual times `(M+1)^3` settles at about `1.70`
across `M = 24..136` with a fitted log-log slope of `-3.008`.  The same script
measures `max|ψ''| = 0.0512` there, which is the `κ_2` the second-derivative
layer produces rather than assumes, and `max|ψ'| = 0.776`, inside the `3/2` used
here.  `scripts/check_cubic_strong_clock_threshold.py` locates the thresholds in
`M` that the closed form needs and exhibits a witness above them.

**Containment.**  The conclusion relates the coefficient polynomial to two of its
zero angles.  No binder mentions both: `hdec` names the polynomial and the
remainder but no zero, and the window binders `hlo`, `hhi` name only the phase.
The two zeros are produced by `exists_two_consecutive_phase_zeros` from the sign
change of `cos Φ_M + e`.

Sorry-free.

## References

Formalizes `../shields-2026-forgacs-tran-numerators.tex`, «Local phase
quantization and strong-clock spacing» (`subsec:strong-clock`,
`prop:local-strong-clock`, `eq:local-phase-quantization`,
`eq:local-strong-clock`, `eq:C1-interior-remainder`,
`eq:phase-derivative-bound`).

## Tags

strong clock, phase quantization, zero spacing, cubic pencil
-/

namespace ForgacsTran

open Real Set

/-! ### The branch, the amplitude and the phase, differentiated a second time

`prop:local-strong-clock`'s `O(M^{-3})` term consumes a bound on `ψ''`, and
`hasDerivAt_cubicPsi` gives `ψ' = Im(W'/W)` with `W'/W = γ'L(γ)` for the fixed
rational `L` of `cubicAmpLogDeriv`.  So `ψ''` is `Im(γ''L(γ) + (γ')^2L'(γ))`,
and every ingredient is elementary at this pencil: `cubicTau_closed_form` makes
`τ = 1/(2\cos((π-θ)/3))`, so `τ''` is a trigonometric quotient and `γ''`,
`L'(γ)` and `W''` follow by the product, quotient and chain rules.

**Differs from the paper's route.**  `subsec:strong-clock` gets `ψ''` bounded by
declaring `W` real-analytic and nonvanishing on `𝒥_0` and appealing to
compactness, which is the right move for a general pencil where `τ` is only
implicitly defined.  Here `τ` is in closed form, so the second derivative is
written down rather than inferred, and no compactness argument is needed —
`cubicAmpLogDeriv2` is an explicit function and the bound on any subarc is a
bound on it.  The paper's route is the general one; this one is available only
because the pencil is concrete. -/

/-- The branch radius's second derivative.  Kept in the `\sin`/`\cos` form the
quotient rule produces — `(\cos^2 + 2\sin^2)/(18\cos^3)` — rather than reduced to
`(2 - \cos^2)/(18\cos^3)`, so that no Pythagorean rewrite stands between the
statement and its proof. -/
noncomputable def cubicTauDeriv2 (θ : ℝ) : ℝ :=
  (Real.cos ((Real.pi - θ) / 3) ^ 2 + 2 * Real.sin ((Real.pi - θ) / 3) ^ 2)
    / (18 * Real.cos ((Real.pi - θ) / 3) ^ 3)

/-- The branch point's second derivative, `γ'' = e^{iθ}(τ'' + 2iτ' - τ)`. -/
noncomputable def cubicGammaDeriv2 (θ : ℝ) : ℂ :=
  Complex.exp ((θ : ℂ) * Complex.I)
    * (((cubicTauDeriv2 θ : ℝ) : ℂ)
        + 2 * ((cubicTauDeriv θ : ℝ) : ℂ) * Complex.I - ((cubicTau θ : ℝ) : ℂ))

/-- The derivative of `W'/W`, which is `γ''L(γ) + (γ')^2L'(γ)` with

`L'(t) = -1/t² + 6(1-3t²)/(3t²+1)² + 2/(1-t)² + 4/(2t+1)²`

the derivative of the `L` of `cubicAmpLogDeriv`.  Its imaginary part **is**
`ψ''`, by `hasDerivAt_cubicPsi`. -/
noncomputable def cubicAmpLogDeriv2 (θ : ℝ) : ℂ :=
  cubicGammaDeriv2 θ * (1 / ftPrincipal cubicTau θ
      + 6 * ftPrincipal cubicTau θ / (3 * ftPrincipal cubicTau θ ^ 2 + 1)
      + 2 / (1 - ftPrincipal cubicTau θ)
      - 2 / (2 * ftPrincipal cubicTau θ + 1))
    + cubicGammaDeriv θ ^ 2 * (-(1 / ftPrincipal cubicTau θ ^ 2)
      + 6 * (1 - 3 * ftPrincipal cubicTau θ ^ 2)
          / (3 * ftPrincipal cubicTau θ ^ 2 + 1) ^ 2
      + 2 / (1 - ftPrincipal cubicTau θ) ^ 2
      + 4 / (2 * ftPrincipal cubicTau θ + 1) ^ 2)

/-- The amplitude's second derivative, `W'' = (L' + L^2)W` where `L = W'/W`. -/
noncomputable def cubicAmpDeriv2 (θ : ℝ) : ℂ :=
  (cubicAmpLogDeriv2 θ + cubicAmpLogDeriv θ ^ 2) * cubicAmp θ

theorem hasDerivAt_cubicTauDeriv {θ : ℝ} (hθ : θ ∈ Icc 0 π) :
    HasDerivAt cubicTauDeriv (cubicTauDeriv2 θ) θ := by
  have hc : 0 < Real.cos ((π - θ) / 3) := cos_third_pos hθ
  have hu : HasDerivAt (fun t : ℝ => (π - t) / 3) (-1 / 3 : ℝ) θ := by
    have h0 : HasDerivAt (fun t : ℝ => π - t) (-1 : ℝ) θ := by
      simpa using (hasDerivAt_id θ).const_sub π
    simpa using h0.div_const 3
  have hsin : HasDerivAt (fun t : ℝ => Real.sin ((π - t) / 3))
      (Real.cos ((π - θ) / 3) * (-1 / 3)) θ := hu.sin
  have hcos : HasDerivAt (fun t : ℝ => Real.cos ((π - t) / 3))
      (-Real.sin ((π - θ) / 3) * (-1 / 3)) θ := hu.cos
  have hDne : (6 : ℝ) * Real.cos ((π - θ) / 3) ^ 2 ≠ 0 := by positivity
  have hq := hsin.neg.div ((hcos.pow 2).const_mul 6) hDne
  refine hq.congr_deriv ?_
  simp only [Pi.neg_apply, Pi.pow_apply]
  rw [cubicTauDeriv2]
  field_simp
  ring

theorem continuousAt_cubicTauDeriv2 {θ : ℝ} (hθ : θ ∈ Icc 0 π) :
    ContinuousAt cubicTauDeriv2 θ := by
  have hc : 0 < Real.cos ((π - θ) / 3) := cos_third_pos hθ
  have hne : (18 : ℝ) * Real.cos ((π - θ) / 3) ^ 3 ≠ 0 := by positivity
  exact ContinuousAt.div (by fun_prop) (by fun_prop) hne

theorem hasDerivAt_cubicGammaDeriv {θ : ℝ} (hθ : θ ∈ Ioo 0 π) :
    HasDerivAt cubicGammaDeriv (cubicGammaDeriv2 θ) θ := by
  have hτ : HasDerivAt (fun t : ℝ => ((cubicTau t : ℝ) : ℂ))
      ((cubicTauDeriv θ : ℝ) : ℂ) θ := (hasDerivAt_cubicTau hθ).ofReal_comp
  have hd : HasDerivAt (fun t : ℝ => ((cubicTauDeriv t : ℝ) : ℂ))
      ((cubicTauDeriv2 θ : ℝ) : ℂ) θ :=
    (hasDerivAt_cubicTauDeriv ⟨hθ.1.le, hθ.2.le⟩).ofReal_comp
  have hE : HasDerivAt (fun t : ℝ => Complex.exp (((t : ℝ) : ℂ) * Complex.I))
      (Complex.exp (((θ : ℝ) : ℂ) * Complex.I) * Complex.I) θ := by
    have h : HasDerivAt (fun w : ℂ => Complex.exp (w * Complex.I))
        (Complex.exp (((θ : ℝ) : ℂ) * Complex.I) * Complex.I) (((θ : ℝ) : ℂ)) := by
      simpa using ((hasDerivAt_id (((θ : ℝ) : ℂ))).mul_const Complex.I).cexp
    exact h.comp_ofReal
  have hmul := hE.mul (hd.add (hτ.mul_const Complex.I))
  refine hmul.congr_deriv ?_
  simp only [Pi.add_apply]
  rw [cubicGammaDeriv2]
  linear_combination (Complex.exp (((θ : ℝ) : ℂ) * Complex.I)
    * ((cubicTau θ : ℝ) : ℂ)) * Complex.I_sq

theorem continuousAt_cubicGammaDeriv2 {θ : ℝ} (hθ : θ ∈ Ioo 0 π) :
    ContinuousAt cubicGammaDeriv2 θ := by
  have hτ : ContinuousAt (fun t : ℝ => ((cubicTau t : ℝ) : ℂ)) θ :=
    Complex.continuous_ofReal.continuousAt.comp (hasDerivAt_cubicTau hθ).continuousAt
  have hd : ContinuousAt (fun t : ℝ => ((cubicTauDeriv t : ℝ) : ℂ)) θ :=
    Complex.continuous_ofReal.continuousAt.comp
      (continuousAt_cubicTauDeriv ⟨hθ.1.le, hθ.2.le⟩)
  have hd2 : ContinuousAt (fun t : ℝ => ((cubicTauDeriv2 t : ℝ) : ℂ)) θ :=
    Complex.continuous_ofReal.continuousAt.comp
      (continuousAt_cubicTauDeriv2 ⟨hθ.1.le, hθ.2.le⟩)
  have hE : ContinuousAt (fun t : ℝ => Complex.exp ((t : ℂ) * Complex.I)) θ := by fun_prop
  exact hE.mul ((hd2.add ((continuousAt_const.mul hd).mul continuousAt_const)).sub hτ)

/-- `L'(γ)γ'`, the derivative of the rational cofactor of `cubicAmpLogDeriv`
along the branch.  Split off so that the algebra of the quotient rule is done
once, on the cofactor alone, and the product rule above it is a bare `ring`. -/
theorem hasDerivAt_cubicAmpCofactor {θ : ℝ} (hθ : θ ∈ cubicRetained) :
    HasDerivAt (fun t => 1 / ftPrincipal cubicTau t
        + 6 * ftPrincipal cubicTau t / (3 * ftPrincipal cubicTau t ^ 2 + 1)
        + 2 / (1 - ftPrincipal cubicTau t)
        - 2 / (2 * ftPrincipal cubicTau t + 1))
      (cubicGammaDeriv θ * (-(1 / ftPrincipal cubicTau θ ^ 2)
        + 6 * (1 - 3 * ftPrincipal cubicTau θ ^ 2)
            / (3 * ftPrincipal cubicTau θ ^ 2 + 1) ^ 2
        + 2 / (1 - ftPrincipal cubicTau θ) ^ 2
        + 4 / (2 * ftPrincipal cubicTau θ + 1) ^ 2)) θ := by
  have hg := hasDerivAt_ftPrincipal_cubicTau hθ.1
  have h0 := ftPrincipal_cubicTau_ne_zero θ
  have h1 := one_sub_ftPrincipal_cubicTau_ne_zero hθ.1
  have h2 := two_mul_ftPrincipal_cubicTau_add_one_ne_zero hθ.1
  have h3 := three_mul_sq_ftPrincipal_add_one_ne_zero hθ.1 hθ.2
  have hb1 := (hasDerivAt_const θ (1 : ℂ)).div hg h0
  have hb2 := (hg.const_mul (6 : ℂ)).div
    (((hg.pow 2).const_mul (3 : ℂ)).add_const 1) h3
  have hb3 := (hasDerivAt_const θ (2 : ℂ)).div
    ((hasDerivAt_const θ (1 : ℂ)).sub hg) h1
  have hb4 := (hasDerivAt_const θ (2 : ℂ)).div
    ((hg.const_mul (2 : ℂ)).add_const 1) h2
  refine (((hb1.add hb2).add hb3).sub hb4).congr_deriv ?_
  simp only [Pi.sub_apply, Pi.pow_apply]
  field_simp
  ring

theorem hasDerivAt_cubicAmpLogDeriv {θ : ℝ} (hθ : θ ∈ cubicRetained) :
    HasDerivAt cubicAmpLogDeriv (cubicAmpLogDeriv2 θ) θ := by
  refine ((hasDerivAt_cubicGammaDeriv hθ.1).mul (hasDerivAt_cubicAmpCofactor hθ)).congr_deriv ?_
  rw [cubicAmpLogDeriv2]
  ring

theorem continuousAt_cubicAmpLogDeriv2 {θ : ℝ} (hθ : θ ∈ cubicRetained) :
    ContinuousAt cubicAmpLogDeriv2 θ := by
  have hg : ContinuousAt (ftPrincipal cubicTau) θ :=
    (hasDerivAt_ftPrincipal_cubicTau hθ.1).continuousAt
  have h0 := ftPrincipal_cubicTau_ne_zero θ
  have h1 := one_sub_ftPrincipal_cubicTau_ne_zero hθ.1
  have h2 := two_mul_ftPrincipal_cubicTau_add_one_ne_zero hθ.1
  have h3 := three_mul_sq_ftPrincipal_add_one_ne_zero hθ.1 hθ.2
  have hd3 : (3 * ftPrincipal cubicTau θ ^ 2 + 1) ^ 2 ≠ 0 := pow_ne_zero 2 h3
  have hd1 : (1 - ftPrincipal cubicTau θ) ^ 2 ≠ 0 := pow_ne_zero 2 h1
  have hd2 : (2 * ftPrincipal cubicTau θ + 1) ^ 2 ≠ 0 := pow_ne_zero 2 h2
  have hd0 : ftPrincipal cubicTau θ ^ 2 ≠ 0 := pow_ne_zero 2 h0
  refine ContinuousAt.add ?_ ?_
  · refine (continuousAt_cubicGammaDeriv2 hθ.1).mul ?_
    refine ContinuousAt.sub (ContinuousAt.add (ContinuousAt.add ?_ ?_) ?_) ?_
    · exact continuousAt_const.div hg h0
    · exact (continuousAt_const.mul hg).div
        ((continuousAt_const.mul (hg.pow 2)).add continuousAt_const) h3
    · exact continuousAt_const.div (continuousAt_const.sub hg) h1
    · exact continuousAt_const.div ((continuousAt_const.mul hg).add continuousAt_const) h2
  · refine ((continuousAt_cubicGammaDeriv hθ.1).pow 2).mul ?_
    refine ContinuousAt.add (ContinuousAt.add (ContinuousAt.add ?_ ?_) ?_) ?_
    · exact (continuousAt_const.div (hg.pow 2) hd0).neg
    · exact (continuousAt_const.mul (continuousAt_const.sub
        (continuousAt_const.mul (hg.pow 2)))).div
        (((continuousAt_const.mul (hg.pow 2)).add continuousAt_const).pow 2) hd3
    · exact continuousAt_const.div ((continuousAt_const.sub hg).pow 2) hd1
    · exact continuousAt_const.div
        (((continuousAt_const.mul hg).add continuousAt_const).pow 2) hd2

/-- The branch point's derivative never vanishes: `γ' = e^{iθ}(τ' + iτ)` has
imaginary part `τ > 0` in its second factor, whatever `τ'` does. -/
theorem cubicGammaDeriv_ne_zero (θ : ℝ) : cubicGammaDeriv θ ≠ 0 := by
  refine mul_ne_zero (Complex.exp_ne_zero _) ?_
  intro h
  have him := congrArg Complex.im h
  simp [Complex.add_im, Complex.mul_im] at him
  exact absurd him (cubicTau_pos θ).ne'

/-- **The arc's `C²` regularity with `γ' ≠ 0`, in the binder shape
`PhaseVariation.linear_phase_variation_components_regular` consumes.**  Its `hd`,
`hd2`, `hc2` and `hreg` at the witness pencil, on the open arc, packaged so the
general statement can be instantiated here without re-deriving any of them.

`hKvar` and `hbranch` — the variation of `arg γ'` and the finite critical set per
viewing angle — are *not* here; those are the two prerequisites that remain. -/
theorem cubic_branch_C2_regular :
    (∀ s ∈ Ioo 0 π, HasDerivAt (ftPrincipal cubicTau) (cubicGammaDeriv s) s) ∧
      (∀ s ∈ Ioo 0 π, HasDerivAt cubicGammaDeriv (cubicGammaDeriv2 s) s) ∧
      ContinuousOn cubicGammaDeriv2 (Ioo 0 π) ∧
      (∀ s : ℝ, cubicGammaDeriv s ≠ 0) :=
  ⟨fun _ hs => hasDerivAt_ftPrincipal_cubicTau hs,
   fun _ hs => hasDerivAt_cubicGammaDeriv hs,
   fun _ hs => (continuousAt_cubicGammaDeriv2 hs).continuousWithinAt,
   cubicGammaDeriv_ne_zero⟩

theorem hasDerivAt_cubicAmpDeriv {θ : ℝ} (hθ : θ ∈ cubicRetained) :
    HasDerivAt (fun θ' => cubicAmpLogDeriv θ' * cubicAmp θ') (cubicAmpDeriv2 θ) θ := by
  have h := (hasDerivAt_cubicAmpLogDeriv hθ).mul (hasDerivAt_cubicAmp hθ.1 hθ.2)
  refine h.congr_deriv ?_
  rw [cubicAmpDeriv2]
  ring

/-- **The `C^2` input `exists_phase_taylor_bound` consumes, in closed form.**  The
combination `Im(W''/W - (W'/W)^2)` — which is `ψ''` — collapses to
`Im(cubicAmpLogDeriv2)`, because `W'' = (L' + L^2)W` by construction.  This is
what makes the continuity requirement a statement about one explicit function
rather than about a quotient of three. -/
theorem cubicPhaseCurvature_eq {θ : ℝ} (hθ : θ ∈ cubicRetained) :
    (cubicAmpDeriv2 θ / cubicAmp θ
        - (cubicAmpLogDeriv θ * cubicAmp θ / cubicAmp θ) ^ 2).im
      = (cubicAmpLogDeriv2 θ).im := by
  have hne := cubicAmp_ne_zero hθ
  have hrw : cubicAmpDeriv2 θ / cubicAmp θ
      - (cubicAmpLogDeriv θ * cubicAmp θ / cubicAmp θ) ^ 2 = cubicAmpLogDeriv2 θ := by
    rw [cubicAmpDeriv2, mul_div_assoc, div_self hne, mul_one, mul_div_assoc,
      div_self hne, mul_one]
    ring
  rw [hrw]


/-- **`eq:local-strong-clock`'s `κ_2` at the witness, at subarc scope.**  One
Taylor constant for `[a,b]`, carrying no `M` — which is what lets a caller hoist
it above the `∀ M` and keep the `O(M^{-3})` rate
(`ConsequencesComposition.exists_absorbing_constant` for why the position
matters). -/
theorem exists_cubic_taylor_bound {a b : ℝ} (hsub : Icc a b ⊆ cubicRetained) :
    ∃ κ₂ ≥ (0 : ℝ), ∀ θa ∈ Icc a b, ∀ θb ∈ Icc a b, θa ≤ θb →
      |cubicPsi a θb - cubicPsi a θa
          - (cubicAmpLogDeriv θa * cubicAmp θa / cubicAmp θa).im * (θb - θa)|
        ≤ κ₂ * (θb - θa) ^ 2 := by
  have hlog : ∀ θ ∈ Icc a b,
      (cubicAmpLogDeriv θ * cubicAmp θ / cubicAmp θ).im = (cubicAmpLogDeriv θ).im :=
    fun θ hθ => by rw [mul_div_assoc, div_self (cubicAmp_ne_zero (hsub hθ)), mul_one]
  have hcont : ContinuousOn (fun θ =>
      (cubicAmpDeriv2 θ / cubicAmp θ
        - (cubicAmpLogDeriv θ * cubicAmp θ / cubicAmp θ) ^ 2).im) (Icc a b) := by
    refine ContinuousOn.congr (f := fun θ => (cubicAmpLogDeriv2 θ).im) ?_ ?_
    · exact fun θ hθ => (Complex.continuous_im.continuousAt.comp
        (continuousAt_cubicAmpLogDeriv2 (hsub hθ))).continuousWithinAt
    · exact fun θ hθ => cubicPhaseCurvature_eq (hsub hθ)
  exact exists_phase_taylor_bound (ψ := cubicPsi a) (W := cubicAmp)
    (dW := fun θ => cubicAmpLogDeriv θ * cubicAmp θ) (ddW := cubicAmpDeriv2)
    (fun θ hθ => by rw [hlog θ hθ]; exact hasDerivAt_cubicPsi hsub hθ)
    (fun θ hθ => hasDerivAt_cubicAmp (hsub hθ).1 (hsub hθ).2)
    (fun θ hθ => hasDerivAt_cubicAmpDeriv (hsub hθ))
    (fun θ hθ => cubicAmp_ne_zero (hsub hθ)) hcont

/-- **`eq:local-strong-clock` at the cubic pencil.**  Two consecutive zeros of
`F_M` in `z(𝒥)`, ordered, with the spacing law between their angles — and with
every branch-side binder of `ft_local_strong_clock_on_FM` discharged:

* the phase is `cubicPsi a`, and `hasDerivAt_cubicPsi` differentiates it to
  `Im(W'/W)`, so `hψd` is a theorem here rather than a hypothesis;
* `abs_im_cubicAmpLogDeriv_le_of_mem` is `eq:phase-derivative-bound` at the
  uniform `κ = 3/2`, which gives `hdψ`, `hΦpos` and `hLκ` at once;
* `Φ_M` is strictly increasing because its derivative is `M + 1 - ψ' ≥ M - 1/2`;
* `hasDerivAt_cubicAmp` gives `hWd`, `cubicAmp_ne_zero` gives `hW0`,
  `cubicTau_pos` gives `hτ`, and `exists_real_ftCoeffPoly_of_real` gives
  `hPmap`.

* the amplitude's second derivative is `cubicAmpDeriv2`, so `hdWd` and `hcont`
  are theorems too — `cubicPhaseCurvature_eq` collapses the `C^2` combination
  `Im(W''/W - (W'/W)^2)` to `Im(cubicAmpLogDeriv2)`, which is `ψ''`.

What remains is the remainder alone; see the module docstring for it, and for the
measurement that it is not empty. -/
theorem cubic_local_strong_clock {M : ℕ} (hM : 2 ≤ M)
    {a b u₀ δ C Ce κ₂ : ℝ} {e de : ℝ → ℝ} (hκ₂0 : 0 ≤ κ₂)
    (htay : ∀ θa ∈ Icc a b, ∀ θb ∈ Icc a b, θa ≤ θb →
      |cubicPsi a θb - cubicPsi a θa
          - (cubicAmpLogDeriv θa * cubicAmp θa / cubicAmp θa).im * (θb - θa)|
        ≤ κ₂ * (θb - θa) ^ 2)
    (hab : a ≤ b) (hsub : Icc a b ⊆ cubicRetained)
    (hcos : Real.cos u₀ = 0) (hδ : 0 < δ) (hδ4 : δ ≤ π / 4)
    -- the window carries a half turn of the phase
    (hlo : ((M : ℝ) + 1) * a - cubicPsi a a ≤ u₀ - δ)
    (hhi : u₀ + π + δ ≤ ((M : ℝ) + 1) * b - cubicPsi a b)
    -- `eq:principal-decomposition`, normalized, with its `C^0` and `C^1` bounds
    (hdec : ∀ θ ∈ Icc a b,
      ((((cubicTau θ : ℝ) : ℂ)) ^ (M + 1)
            * (ftCoeffPoly cubicQ witB 1 M).eval ((cubicZ (cubicTau θ) θ : ℝ) : ℂ)).re
          / (2 * ftPrincipalAmp cubicQ witB 1
              (fun θ' => cubicZ (cubicTau θ') θ') cubicTau θ)
        = Real.cos (((M : ℝ) + 1) * θ - cubicPsi a θ) + e θ)
    (heb : ∀ θ ∈ Icc a b, |e θ| < Real.sin δ)
    (hCnn : 0 ≤ C) (hCeb : ∀ θ ∈ Icc a b, |e θ| ≤ C)
    (hed : ∀ θ ∈ Icc a b, HasDerivAt e (de θ) θ)
    (hdeb : ∀ θ ∈ Icc a b, |de θ| ≤ Ce)
    (hCe : Ce < Real.sqrt 2 / 2 * ((M : ℝ) - 1 / 2)) :
    ∃ θk ∈ Icc a b, ∃ θk1 ∈ Icc a b, θk < θk1 ∧
      (ftCoeffPoly cubicQ witB 1 M).eval ((cubicZ (cubicTau θk) θk : ℝ) : ℂ) = 0 ∧
      (ftCoeffPoly cubicQ witB 1 M).eval ((cubicZ (cubicTau θk1) θk1 : ℝ) : ℂ) = 0 ∧
      θk1 - θk ≤ (π + 2 * (π / 2 * C)) / (((M : ℝ) + 1) - 3 / 2) ∧
        |(θk1 - θk) - π / ((M : ℝ) + 1)
            - π * (cubicAmpLogDeriv θk * cubicAmp θk / cubicAmp θk).im
                / ((M : ℝ) + 1) ^ 2|
          ≤ (2 * (π / 2 * C)
                + κ₂ * ((π + 2 * (π / 2 * C)) / (((M : ℝ) + 1) - 3 / 2)) ^ 2)
              / (((M : ℝ) + 1) - 3 / 2)
            + π * (3 / 2) ^ 2 / (((M : ℝ) + 1) ^ 2 * (((M : ℝ) + 1) - 3 / 2)) := by
  have hMR : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  -- `W'/W` reduces to the closed-form logarithmic derivative
  have hlog : ∀ θ ∈ Icc a b,
      (cubicAmpLogDeriv θ * cubicAmp θ / cubicAmp θ).im = (cubicAmpLogDeriv θ).im := by
    intro θ hθ
    rw [mul_div_assoc, div_self (cubicAmp_ne_zero (hsub hθ)), mul_one]
  -- `eq:phase-derivative-bound`, at the uniform `κ = 3/2`
  have hdψ : ∀ θ ∈ Icc a b,
      |(cubicAmpLogDeriv θ * cubicAmp θ / cubicAmp θ).im| ≤ 3 / 2 := by
    intro θ hθ
    rw [hlog θ hθ]
    exact abs_im_cubicAmpLogDeriv_le_of_mem (hsub hθ)
  have hψd : ∀ θ ∈ Icc a b,
      HasDerivAt (cubicPsi a)
        ((cubicAmpLogDeriv θ * cubicAmp θ / cubicAmp θ).im) θ := by
    intro θ hθ
    rw [hlog θ hθ]
    exact hasDerivAt_cubicPsi hsub hθ
  -- `Φ_M` and its derivative
  have hΦd : ∀ θ ∈ Icc a b,
      HasDerivAt (fun θ' => ((M : ℝ) + 1) * θ' - cubicPsi a θ')
        (((M : ℝ) + 1) - (cubicAmpLogDeriv θ).im) θ := by
    intro θ hθ
    have hlin : HasDerivAt (fun θ' : ℝ => ((M : ℝ) + 1) * θ') ((M : ℝ) + 1) θ := by
      simpa using (hasDerivAt_id θ).const_mul (((M : ℝ) + 1))
    exact hlin.sub (hasDerivAt_cubicPsi hsub hθ)
  have hΦpos : ∀ θ ∈ Icc a b,
      0 < ((M : ℝ) + 1) - (cubicAmpLogDeriv θ).im := by
    intro θ hθ
    have := abs_le.1 (abs_im_cubicAmpLogDeriv_le_of_mem (hsub hθ))
    linarith
  have hmono : StrictMonoOn (fun θ' => ((M : ℝ) + 1) * θ' - cubicPsi a θ') (Icc a b) := by
    refine strictMonoOn_of_deriv_pos (convex_Icc a b)
      (fun θ hθ => (hΦd θ hθ).continuousAt.continuousWithinAt) (fun θ hθ => ?_)
    rw [interior_Icc] at hθ
    have hθ' : θ ∈ Icc a b := ⟨hθ.1.le, hθ.2.le⟩
    rw [(hΦd θ hθ').deriv]
    exact hΦpos θ hθ'
  -- the branch's own positivity, and the real model of `F_M`
  obtain ⟨P, hP⟩ :=
    exists_real_ftCoeffPoly_of_real hasRealCoeffs_cubicQ hasRealCoeffs_witB 1 M
  -- the `C²` regularity, in closed form rather than assumed
  have hcont : ContinuousOn (fun θ =>
      (cubicAmpDeriv2 θ / cubicAmp θ
        - (cubicAmpLogDeriv θ * cubicAmp θ / cubicAmp θ) ^ 2).im) (Icc a b) := by
    refine ContinuousOn.congr (f := fun θ => (cubicAmpLogDeriv2 θ).im) ?_ ?_
    · exact fun θ hθ => (Complex.continuous_im.continuousAt.comp
        (continuousAt_cubicAmpLogDeriv2 (hsub hθ))).continuousWithinAt
    · exact fun θ hθ => cubicPhaseCurvature_eq (hsub hθ)
  have hWpos : ∀ θ ∈ Icc a b,
      0 < ftPrincipalAmp cubicQ witB 1 (fun θ' => cubicZ (cubicTau θ') θ') cubicTau θ := by
    intro θ hθ
    rw [ftPrincipalAmp_cubic_eq]
    exact norm_pos_iff.2 (cubicAmp_ne_zero (hsub hθ))
  exact ft_local_strong_clock_on_FM_of (Q := cubicQ) (B := witB) (r := 1) (M := M)
    (z := fun θ => cubicZ (cubicTau θ) θ) (τ := cubicTau) (ψ := cubicPsi a)
    (Φ := fun θ => ((M : ℝ) + 1) * θ - cubicPsi a θ)
    (dΦ := fun θ => ((M : ℝ) + 1) - (cubicAmpLogDeriv θ).im)
    (e := e) (de := de) (W := cubicAmp)
    (dW := fun θ => cubicAmpLogDeriv θ * cubicAmp θ)
    (L := (M : ℝ) + 1) (κ := 3 / 2) (κ₂ := κ₂) (P := P)
    (fun _ => rfl) rfl hab hcos hδ hδ4 hmono hΦd hed hΦpos hdeb
    (fun θ hθ => by
      have := abs_le.1 (abs_im_cubicAmpLogDeriv_le_of_mem (hsub hθ))
      have hs : Real.sqrt 2 / 2 * ((M : ℝ) - 1 / 2)
          ≤ Real.sqrt 2 / 2 * (((M : ℝ) + 1) - (cubicAmpLogDeriv θ).im) := by
        have h2 : (0 : ℝ) ≤ Real.sqrt 2 / 2 := by positivity
        nlinarith
      linarith)
    heb hlo hhi hP (fun θ _ => cubicTau_pos θ) hWpos hdec
    (by norm_num) hκ₂0 hCnn (by linarith) hψd hdψ htay hCeb

end ForgacsTran
