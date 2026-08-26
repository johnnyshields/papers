/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import ForgacsTran.FTBranchTauDeriv
import ForgacsTran.FTBranchRegularity

/-!
# Second-order regularity of the Forgács–Tran branch

`eq:local-strong-clock`'s `O(M^{-3})` term consumes a bound on `ψ''`, and `ψ` is
`arg W` along the branch, so the chain that reaches it starts at `τ''`.  The
first-order half is `FTBranchRegularity.hasDerivAt_ftTau`: the branch equation
`∑_k θ_k(τ,θ) = rθ + lπ` is solved for `τ` because its `τ`-partial is strictly
negative.  Differentiating that solution once more needs the **second** partials
of the angle sum, which is what this module builds.

## Main statements

* `ftAngleDeriv2Tau`, `hasDerivAt_ftAngleDerivTau_tau` — `∂²θ_k/∂τ²`.

## Implementation notes

**The angle's own partials are closed forms, and that is what makes the second
order elementary.**  `FTBranchTauDeriv.hasDerivAt_ftAngle_tau` gives
`∂θ_k/∂τ = -\sin^2θ_k · a_k/(τ^2\sin θ)`, in which the only `τ`-dependence
beyond the explicit `τ^2` is through `θ_k` itself.  So the second partial is the
quotient rule applied once, with `∂θ_k/∂τ` substituted back into itself — no new
implicit-function step, and no appeal to a general smoothness theorem for
implicitly defined functions.

## References

Formalizes `../shields-2026-forgacs-tran-numerators.tex`, «Spectral geometry,
residues, and the principal amplitude» (`sec:geometry`, `thm:FT-geometry`), in
service of «Local phase quantization and strong-clock spacing»
(`subsec:strong-clock`, `prop:local-strong-clock`,
`eq:phase-derivative-bound`), via `Forgacs2017RationalDenominator` Lemma 2.

## Tags

branch regularity, second derivative, angle sum, viewing angle
-/

namespace ForgacsTran

open Real Set

/-- `∂²θ_k/∂τ²`.  The quotient rule on `∂θ_k/∂τ = -\sin^2θ_k a/(τ^2\sin s)`,
with `∂θ_k/∂τ` substituted back into itself. -/
noncomputable def ftAngleDeriv2Tau (a τ s : ℝ) : ℝ :=
  a * Real.sin (ftAngle a τ s) ^ 2
      * (2 * τ * Real.sin s
        + 2 * a * Real.sin (ftAngle a τ s) * Real.cos (ftAngle a τ s))
    / (τ ^ 4 * Real.sin s ^ 2)

/-- **The angle's second `τ`-partial.**  The smallest genuine step toward `τ''`:
the `τ`-partial of `∂θ_k/∂τ`, with no implicit-function argument beyond the one
`FTBranchRegularity` already ran. -/
theorem hasDerivAt_ftAngleDerivTau_tau {a τ s : ℝ} (ha : 0 < a) (hτ : 0 < τ)
    (hs : s ∈ Ioo 0 π) :
    HasDerivAt (fun u => -(Real.sin (ftAngle a u s) ^ 2 * a / (u ^ 2 * Real.sin s)))
      (ftAngleDeriv2Tau a τ s) τ := by
  have hsin : 0 < Real.sin s := sin_pos_of_pos_of_lt_pi hs.1 hs.2
  have hτ' : τ ≠ 0 := hτ.ne'
  have hy := hasDerivAt_ftAngle_tau ha hτ hs
  -- `sin^2 θ_k` through the chain rule
  have hsq : HasDerivAt (fun u => Real.sin (ftAngle a u s) ^ 2)
      (2 * Real.sin (ftAngle a τ s) ^ 1
        * (Real.cos (ftAngle a τ s)
          * -(Real.sin (ftAngle a τ s) ^ 2 * a / (τ ^ 2 * Real.sin s)))) τ :=
    (hy.sin).pow 2
  -- the explicit denominator
  have hden : HasDerivAt (fun u : ℝ => u ^ 2 * Real.sin s)
      (2 * τ ^ 1 * Real.sin s) τ := by
    simpa using (hasDerivAt_pow 2 τ).mul_const (Real.sin s)
  have hne : τ ^ 2 * Real.sin s ≠ 0 := by positivity
  have hquot := ((hsq.mul_const a).div hden hne).neg
  refine hquot.congr_deriv ?_
  rw [ftAngleDeriv2Tau]
  field_simp
  ring


/-- `∂²θ_k/∂τ∂θ` in the clean form `(∂θ_k/∂τ)·\cos(2θ_k-θ)/\sin θ`.  The two
terms of the product rule combine by the cosine addition formula, which is why
this partial has a closed form the other three do not. -/
noncomputable def ftAngleDeriv2AngleTau (a τ s : ℝ) : ℝ :=
  -(Real.sin (ftAngle a τ s) ^ 2 * a / (τ ^ 2 * Real.sin s))
    * Real.cos (2 * ftAngle a τ s - s) / Real.sin s

/-- **`∂θ_k/∂θ` differentiated in `τ`.** -/
theorem hasDerivAt_ftAngleDerivAngle_tau {a τ s : ℝ} (ha : 0 < a) (hτ : 0 < τ)
    (hs : s ∈ Ioo 0 π) :
    HasDerivAt
      (fun u => Real.sin (ftAngle a u s) * Real.cos (ftAngle a u s - s) / Real.sin s)
      (ftAngleDeriv2AngleTau a τ s) τ := by
  have hsin : 0 < Real.sin s := sin_pos_of_pos_of_lt_pi hs.1 hs.2
  have hy := hasDerivAt_ftAngle_tau ha hτ hs
  have h1 := hy.sin
  have h2 := (hy.sub_const s).cos
  refine ((h1.mul h2).div_const (Real.sin s)).congr_deriv ?_
  rw [ftAngleDeriv2AngleTau,
    show (2 : ℝ) * ftAngle a τ s - s = ftAngle a τ s + (ftAngle a τ s - s) by ring,
    Real.cos_add]
  field_simp
  ring

/-- `∂²θ_k/∂θ∂τ`, the mixed partial taken the other way: `∂θ_k/∂τ`
differentiated in the angle. -/
noncomputable def ftAngleDeriv2TauAngle (a τ s : ℝ) : ℝ :=
  -(a / τ ^ 2)
    * ((2 * Real.sin (ftAngle a τ s) * Real.cos (ftAngle a τ s)
            * (Real.sin (ftAngle a τ s) * Real.cos (ftAngle a τ s - s) / Real.sin s)
            * Real.sin s
          - Real.sin (ftAngle a τ s) ^ 2 * Real.cos s) / Real.sin s ^ 2)

/-- **`∂θ_k/∂τ` differentiated in the angle.** -/
theorem hasDerivAt_ftAngleDerivTau_angle {a τ s : ℝ} (ha : 0 < a) (hτ : 0 < τ)
    (hs : s ∈ Ioo 0 π) :
    HasDerivAt
      (fun t => -(Real.sin (ftAngle a τ t) ^ 2 * a / (τ ^ 2 * Real.sin t)))
      (ftAngleDeriv2TauAngle a τ s) s := by
  have hsin : 0 < Real.sin s := sin_pos_of_pos_of_lt_pi hs.1 hs.2
  have hτ' : τ ≠ 0 := hτ.ne'
  have hy := hasDerivAt_ftAngle ha hτ hs
  have hsq := (hy.sin).pow 2
  have hne : τ ^ 2 * Real.sin s ≠ 0 := by positivity
  have hden : HasDerivAt (fun t : ℝ => τ ^ 2 * Real.sin t) (τ ^ 2 * Real.cos s) s :=
    (Real.hasDerivAt_sin s).const_mul (τ ^ 2)
  refine (((hsq.mul_const a).div hden hne).neg).congr_deriv ?_
  simp only [Pi.pow_apply]
  rw [ftAngleDeriv2TauAngle]
  field_simp
  ring

/-- `∂²θ_k/∂θ²`. -/
noncomputable def ftAngleDeriv2Angle (a τ s : ℝ) : ℝ :=
  ((Real.cos (ftAngle a τ s)
        * (Real.sin (ftAngle a τ s) * Real.cos (ftAngle a τ s - s) / Real.sin s)
        * Real.cos (ftAngle a τ s - s)
      + Real.sin (ftAngle a τ s)
        * (-Real.sin (ftAngle a τ s - s)
          * (Real.sin (ftAngle a τ s) * Real.cos (ftAngle a τ s - s) / Real.sin s - 1)))
      * Real.sin s
    - Real.sin (ftAngle a τ s) * Real.cos (ftAngle a τ s - s) * Real.cos s)
    / Real.sin s ^ 2

/-- **`∂θ_k/∂θ` differentiated in the angle.** -/
theorem hasDerivAt_ftAngleDerivAngle_angle {a τ s : ℝ} (ha : 0 < a) (hτ : 0 < τ)
    (hs : s ∈ Ioo 0 π) :
    HasDerivAt
      (fun t => Real.sin (ftAngle a τ t) * Real.cos (ftAngle a τ t - t) / Real.sin t)
      (ftAngleDeriv2Angle a τ s) s := by
  have hsin : 0 < Real.sin s := sin_pos_of_pos_of_lt_pi hs.1 hs.2
  have hne : Real.sin s ≠ 0 := hsin.ne'
  have hy := hasDerivAt_ftAngle ha hτ hs
  have h1 := hy.sin
  have h2 := (hy.sub (hasDerivAt_id s)).cos
  refine ((h1.mul h2).div (Real.hasDerivAt_sin s) hne).congr_deriv ?_
  simp only [Pi.sub_apply, Pi.mul_apply, id_eq]
  rw [ftAngleDeriv2Angle]


/-! ### The branch angle along a moving radius

`FTBranchRegularity.hasDerivAt_ftTau` reaches `τ'` by a hand-rolled mean value
argument in `τ` with a squeeze on the intermediate point, and that route
deliberately avoids the chain rule — which is why it does not reach `τ''`.  What
`τ''` needs is the total derivative of `θ ↦ θ_k(τ(θ), θ)`, and the theorem below
supplies it.

**No two-variable chain rule is formed, and none is needed.**  `ftAngle` is
`ftArccot ∘ g` with `g(τ,θ) = \cosθ/\sinθ - a/(τ\sinθ)`, so with the radius a
function of the angle, `θ ↦ g(u(θ),θ)` is an ordinary *one-variable* composite
built by the usual quotient and product rules.  The only work is reconciling the
raw output, which is in `g`, against the two partials, which are in `\sinθ_k`
and `\cos(θ_k-θ)`; `1 + g^2 = 1/\sin^2θ_k` and `ftAngle_spec`'s
`a\sinθ_k = τ\sin(θ_k-θ)` do it, and the last step is the sine addition
formula. -/

/-- **The branch angle's total derivative along a moving radius.**  With `u` any
differentiable positive radius, `θ ↦ θ_k(u(θ),θ)` differentiates to
`(∂θ_k/∂τ)u' + ∂θ_k/∂θ` — the two partials `FTBranchTauDeriv` and
`FTBranchDeriv` already supply, combined.  Taking `u = ftTau a r l` is what puts
`τ''` in reach. -/
theorem hasDerivAt_ftAngle_comp {a : ℝ} {u : ℝ → ℝ} {u' θ : ℝ}
    (ha : 0 < a) (hu : HasDerivAt u u' θ) (hupos : 0 < u θ) (hθ : θ ∈ Ioo 0 π) :
    HasDerivAt (fun t => ftAngle a (u t) t)
      (-(Real.sin (ftAngle a (u θ) θ) ^ 2 * a / (u θ ^ 2 * Real.sin θ)) * u'
        + Real.sin (ftAngle a (u θ) θ) * Real.cos (ftAngle a (u θ) θ - θ)
            / Real.sin θ) θ := by
  have hsin : 0 < Real.sin θ := sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
  have hsin' : Real.sin θ ≠ 0 := hsin.ne'
  have hu0 : u θ ≠ 0 := hupos.ne'
  have hymem := ftAngle_mem_Ioo ha hupos hθ
  have hsy : 0 < Real.sin (ftAngle a (u θ) θ) :=
    sin_pos_of_pos_of_lt_pi (lt_trans hθ.1 hymem.1) hymem.2
  set y := ftAngle a (u θ) θ with hy
  set g : ℝ → ℝ := fun t => Real.cos t / Real.sin t - a / (u t * Real.sin t) with hgdef
  have hgs : Real.cos y = g θ * Real.sin y := cos_ftArccot _
  have hone : 1 + g θ ^ 2 = 1 / Real.sin y ^ 2 := by
    have hgval : g θ = Real.cos y / Real.sin y := by
      rw [eq_div_iff hsy.ne']; exact hgs.symm
    rw [hgval]
    field_simp
    linear_combination (Real.sin_sq_add_cos_sq y)
  have hspec : a * Real.sin y = u θ * Real.sin (y - θ) := ftAngle_spec hu0 hθ
  have hsiny : Real.sin y
      = Real.sin (y - θ) * Real.cos θ + Real.cos (y - θ) * Real.sin θ := by
    have h := Real.sin_add (y - θ) θ
    rw [show y - θ + θ = y by ring] at h
    exact h
  have hden : HasDerivAt (fun t => u t * Real.sin t)
      (u' * Real.sin θ + u θ * Real.cos θ) θ := hu.mul (Real.hasDerivAt_sin θ)
  have hdenne : u θ * Real.sin θ ≠ 0 := mul_ne_zero hu0 hsin'
  have h1 : HasDerivAt (fun t : ℝ => Real.cos t / Real.sin t)
      ((-Real.sin θ * Real.sin θ - Real.cos θ * Real.cos θ) / Real.sin θ ^ 2) θ :=
    (Real.hasDerivAt_cos θ).div (Real.hasDerivAt_sin θ) hsin'
  have h2 : HasDerivAt (fun t => a / (u t * Real.sin t))
      ((0 * (u θ * Real.sin θ) - a * (u' * Real.sin θ + u θ * Real.cos θ))
        / (u θ * Real.sin θ) ^ 2) θ :=
    (hasDerivAt_const θ a).div hden hdenne
  have hcomp := (hasDerivAt_ftArccot (g θ)).comp θ (h1.sub h2)
  have hfun : (ftArccot ∘ g) = fun t => ftAngle a (u t) t := rfl
  rw [hfun] at hcomp
  refine hcomp.congr_deriv ?_
  rw [hone]
  field_simp
  linear_combination (Real.sin y * u θ ^ 2) * Real.sin_sq_add_cos_sq θ
    - (u θ * Real.cos θ) * hspec + (u θ ^ 2) * hsiny


/-! ### The partials along a moving radius

With `hasDerivAt_ftAngle_comp` in hand each of the two first partials
differentiates along the branch by ordinary combinators, and the result is the
two-variable chain rule written in the four partials above: `∂/∂τ · u' + ∂/∂θ`.
Nothing new is proved here — what is checked is that the combinator output really
does decompose that way, which is the step a `HasFDerivAt` would have supplied. -/

/-- **`∂θ_k/∂θ` along a moving radius**, decomposed as `∂²θ_k/∂τ∂θ · u' + ∂²θ_k/∂θ²`. -/
theorem hasDerivAt_ftAngleDerivAngle_comp {a : ℝ} {u : ℝ → ℝ} {u' θ : ℝ}
    (ha : 0 < a) (hu : HasDerivAt u u' θ) (hupos : 0 < u θ) (hθ : θ ∈ Ioo 0 π) :
    HasDerivAt
      (fun t => Real.sin (ftAngle a (u t) t)
        * Real.cos (ftAngle a (u t) t - t) / Real.sin t)
      (ftAngleDeriv2AngleTau a (u θ) θ * u' + ftAngleDeriv2Angle a (u θ) θ) θ := by
  have hsin : 0 < Real.sin θ := sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
  have hne : Real.sin θ ≠ 0 := hsin.ne'
  have hy := hasDerivAt_ftAngle_comp ha hu hupos hθ
  have h1 := hy.sin
  have h2 := (hy.sub (hasDerivAt_id θ)).cos
  refine ((h1.mul h2).div (Real.hasDerivAt_sin θ) hne).congr_deriv ?_
  simp only [Pi.sub_apply, Pi.mul_apply, id_eq]
  rw [ftAngleDeriv2AngleTau, ftAngleDeriv2Angle,
    show (2 : ℝ) * ftAngle a (u θ) θ - θ
      = ftAngle a (u θ) θ + (ftAngle a (u θ) θ - θ) by ring, Real.cos_add]
  field_simp
  ring

/-- **`∂θ_k/∂τ` along a moving radius**, decomposed as `∂²θ_k/∂τ² · u' + ∂²θ_k/∂θ∂τ`. -/
theorem hasDerivAt_ftAngleDerivTau_comp {a : ℝ} {u : ℝ → ℝ} {u' θ : ℝ}
    (ha : 0 < a) (hu : HasDerivAt u u' θ) (hupos : 0 < u θ) (hθ : θ ∈ Ioo 0 π) :
    HasDerivAt
      (fun t => -(Real.sin (ftAngle a (u t) t) ^ 2 * a / (u t ^ 2 * Real.sin t)))
      (ftAngleDeriv2Tau a (u θ) θ * u' + ftAngleDeriv2TauAngle a (u θ) θ) θ := by
  have hsin : 0 < Real.sin θ := sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
  have hu0 : u θ ≠ 0 := hupos.ne'
  have hy := hasDerivAt_ftAngle_comp ha hu hupos hθ
  have hsq := (hy.sin).pow 2
  have hne : u θ ^ 2 * Real.sin θ ≠ 0 := by positivity
  refine (((hsq.mul_const a).div ((hu.pow 2).mul (Real.hasDerivAt_sin θ)) hne).neg).congr_deriv ?_
  simp only [Pi.pow_apply, Pi.mul_apply]
  rw [ftAngleDeriv2Tau, ftAngleDeriv2TauAngle]
  field_simp
  ring


/-! ### `τ''`

The angle sum's two partials differentiate along the branch summand by summand,
and the quotient rule closes `ftTauDeriv`.  This is the second derivative of the
implicitly defined branch radius, and it is what `ψ''` — and through it
`eq:local-strong-clock`'s `O(M^{-3})` term — is built on. -/

theorem hasDerivAt_ftAngleSumDerivAngle_comp {n : ℕ} {a : Fin n → ℝ} {u : ℝ → ℝ}
    {u' θ : ℝ} (ha : ∀ k, 0 < a k) (hu : HasDerivAt u u' θ) (hupos : 0 < u θ)
    (hθ : θ ∈ Ioo 0 π) :
    HasDerivAt (fun t => ftAngleSumDerivAngle a (u t) t)
      ((∑ k, ftAngleDeriv2AngleTau (a k) (u θ) θ) * u'
        + ∑ k, ftAngleDeriv2Angle (a k) (u θ) θ) θ := by
  refine (HasDerivAt.fun_sum fun k _ =>
    hasDerivAt_ftAngleDerivAngle_comp (ha k) hu hupos hθ).congr_deriv ?_
  rw [Finset.sum_add_distrib, ← Finset.sum_mul]

theorem hasDerivAt_ftAngleSumDerivTau_comp {n : ℕ} {a : Fin n → ℝ} {u : ℝ → ℝ}
    {u' θ : ℝ} (ha : ∀ k, 0 < a k) (hu : HasDerivAt u u' θ) (hupos : 0 < u θ)
    (hθ : θ ∈ Ioo 0 π) :
    HasDerivAt (fun t => ftAngleSumDerivTau a (u t) t)
      ((∑ k, ftAngleDeriv2Tau (a k) (u θ) θ) * u'
        + ∑ k, ftAngleDeriv2TauAngle (a k) (u θ) θ) θ := by
  refine (HasDerivAt.fun_sum fun k _ =>
    hasDerivAt_ftAngleDerivTau_comp (ha k) hu hupos hθ).congr_deriv ?_
  rw [Finset.sum_add_distrib, ← Finset.sum_mul]

/-- `τ''`, by the quotient rule on `ftTauDeriv`. -/
noncomputable def ftTauDeriv2 {n : ℕ} (a : Fin n → ℝ) (r l : ℕ) (θ : ℝ) : ℝ :=
  (-((∑ k, ftAngleDeriv2AngleTau (a k) (ftTau a r l θ) θ) * ftTauDeriv a r l θ
        + ∑ k, ftAngleDeriv2Angle (a k) (ftTau a r l θ) θ)
      * ftAngleSumDerivTau a (ftTau a r l θ) θ
    - -(ftAngleSumDerivAngle a (ftTau a r l θ) θ - r)
      * ((∑ k, ftAngleDeriv2Tau (a k) (ftTau a r l θ) θ) * ftTauDeriv a r l θ
        + ∑ k, ftAngleDeriv2TauAngle (a k) (ftTau a r l θ) θ))
    / ftAngleSumDerivTau a (ftTau a r l θ) θ ^ 2

/-- **The branch radius is twice differentiable on the viewing arc.**  The
statement `FTBranchRegularity` could not reach, because its mean-value route to
`τ'` deliberately avoids the chain rule; `hasDerivAt_ftAngle_comp` supplies the
chain rule and the four partials supply the coefficients. -/
theorem hasDerivAt_ftTauDeriv {n r l : ℕ} {a : Fin n → ℝ} (hn : 0 < n)
    (ha : ∀ k, 0 < a k) (hr : 1 ≤ r) {θ₀ : ℝ} (hθ₀ : θ₀ ∈ Ioo 0 (π / r))
    (hb : ∀ θ ∈ Ioo 0 (π / r), FTBranchAt a r l θ) :
    HasDerivAt (ftTauDeriv a r l) (ftTauDeriv2 a r l θ₀) θ₀ := by
  have hθπ : θ₀ ∈ Ioo 0 π := ftArc_subset hr hθ₀
  have hT := hasDerivAt_ftTau hn ha hr hθ₀ hb
  have hτ : 0 < ftTau a r l θ₀ := ftTau_pos (hb θ₀ hθ₀)
  have hG := hasDerivAt_ftAngleSumDerivAngle_comp ha hT hτ hθπ
  have hH := hasDerivAt_ftAngleSumDerivTau_comp ha hT hτ hθπ
  have hne : ftAngleSumDerivTau a (ftTau a r l θ₀) θ₀ ≠ 0 :=
    (ftAngleSumDerivTau_neg hn ha hτ hθπ).ne
  refine ((((hG.sub_const ((r : ℝ))).neg).div hH hne)).congr_deriv ?_
  simp only [Pi.neg_apply]
  rw [ftTauDeriv2]

/-- **The branch radius is twice differentiable, on the principal branch, with no
hypothesis beyond the admissible class.** -/
theorem hasDerivAt_ftTauDeriv_principal {n r : ℕ} {a : Fin n → ℝ} (hn : 0 < n)
    (ha : ∀ k, 0 < a k) (hr : 1 ≤ r) (hnr : 2 ≤ n ∨ 2 ≤ r) {θ₀ : ℝ}
    (hθ₀ : θ₀ ∈ Ioo 0 (π / r)) :
    HasDerivAt (ftTauDeriv a r (n - 1)) (ftTauDeriv2 a r (n - 1) θ₀) θ₀ :=
  hasDerivAt_ftTauDeriv hn ha hr hθ₀ fun _θ hθ => ftBranchAt_of_arc_principal hn ha hr hnr hθ


/-! ### The branch point in `C²`

`γ = τe^{iθ}`, so once `τ` is twice differentiable so is `γ`, with
`γ' = e^{iθ}(τ' + iτ)` and `γ'' = e^{iθ}(τ'' + 2iτ' - τ)`.  These are the general
forms of what `CubicClockSpacing` carries at the witness pencil. -/

/-- `γ' = e^{iθ}(τ' + iτ)` at the general branch. -/
noncomputable def ftGammaDeriv {n : ℕ} (a : Fin n → ℝ) (r l : ℕ) (θ : ℝ) : ℂ :=
  Complex.exp ((θ : ℂ) * Complex.I)
    * (((ftTauDeriv a r l θ : ℝ) : ℂ) + ((ftTau a r l θ : ℝ) : ℂ) * Complex.I)

/-- `γ'' = e^{iθ}(τ'' + 2iτ' - τ)`. -/
noncomputable def ftGammaDeriv2 {n : ℕ} (a : Fin n → ℝ) (r l : ℕ) (θ : ℝ) : ℂ :=
  Complex.exp ((θ : ℂ) * Complex.I)
    * (((ftTauDeriv2 a r l θ : ℝ) : ℂ)
      + 2 * ((ftTauDeriv a r l θ : ℝ) : ℂ) * Complex.I - ((ftTau a r l θ : ℝ) : ℂ))

private theorem hasDerivAt_expI (θ : ℝ) :
    HasDerivAt (fun t : ℝ => Complex.exp (((t : ℝ) : ℂ) * Complex.I))
      (Complex.exp (((θ : ℝ) : ℂ) * Complex.I) * Complex.I) θ := by
  have h : HasDerivAt (fun w : ℂ => Complex.exp (w * Complex.I))
      (Complex.exp (((θ : ℝ) : ℂ) * Complex.I) * Complex.I) (((θ : ℝ) : ℂ)) := by
    simpa using ((hasDerivAt_id (((θ : ℝ) : ℂ))).mul_const Complex.I).cexp
  exact h.comp_ofReal

/-- **The branch point is differentiable**, in the spelling `ftPrincipal` unfolds
to, so that no import of the dominance tree is needed to state it.

**Not a duplicate of `FTBranchRegularity.hasDerivAt_ftBranchPoint`.**  That one
is the `e^{-iθ}` member `t₋ = τe^{-iθ}`; this is the `e^{+iθ}` member, which is
what `ftPrincipal` is and what the amplitude `W` is evaluated at.  Both members
of the pair are used — the dominance binders ask for simplicity at each — so the
two statements are the two halves of one fact, not one fact written twice. -/
theorem hasDerivAt_ftBranchGamma {n r l : ℕ} {a : Fin n → ℝ} (hn : 0 < n)
    (ha : ∀ k, 0 < a k) (hr : 1 ≤ r) {θ₀ : ℝ} (hθ₀ : θ₀ ∈ Ioo 0 (π / r))
    (hb : ∀ θ ∈ Ioo 0 (π / r), FTBranchAt a r l θ) :
    HasDerivAt (fun t : ℝ => ((ftTau a r l t : ℝ) : ℂ)
      * Complex.exp (((t : ℝ) : ℂ) * Complex.I)) (ftGammaDeriv a r l θ₀) θ₀ := by
  have hτ : HasDerivAt (fun t : ℝ => ((ftTau a r l t : ℝ) : ℂ))
      ((ftTauDeriv a r l θ₀ : ℝ) : ℂ) θ₀ :=
    (hasDerivAt_ftTau hn ha hr hθ₀ hb).ofReal_comp
  refine (hτ.mul (hasDerivAt_expI θ₀)).congr_deriv ?_
  rw [ftGammaDeriv]
  ring

theorem hasDerivAt_ftGammaDeriv {n r l : ℕ} {a : Fin n → ℝ} (hn : 0 < n)
    (ha : ∀ k, 0 < a k) (hr : 1 ≤ r) {θ₀ : ℝ} (hθ₀ : θ₀ ∈ Ioo 0 (π / r))
    (hb : ∀ θ ∈ Ioo 0 (π / r), FTBranchAt a r l θ) :
    HasDerivAt (ftGammaDeriv a r l) (ftGammaDeriv2 a r l θ₀) θ₀ := by
  have hτ : HasDerivAt (fun t : ℝ => ((ftTau a r l t : ℝ) : ℂ))
      ((ftTauDeriv a r l θ₀ : ℝ) : ℂ) θ₀ :=
    (hasDerivAt_ftTau hn ha hr hθ₀ hb).ofReal_comp
  have hd : HasDerivAt (fun t : ℝ => ((ftTauDeriv a r l t : ℝ) : ℂ))
      ((ftTauDeriv2 a r l θ₀ : ℝ) : ℂ) θ₀ :=
    (hasDerivAt_ftTauDeriv hn ha hr hθ₀ hb).ofReal_comp
  refine ((hasDerivAt_expI θ₀).mul (hd.add (hτ.mul_const Complex.I))).congr_deriv ?_
  simp only [Pi.add_apply]
  rw [ftGammaDeriv2]
  linear_combination (Complex.exp (((θ₀ : ℝ) : ℂ) * Complex.I)
    * ((ftTau a r l θ₀ : ℝ) : ℂ)) * Complex.I_sq

end ForgacsTran
