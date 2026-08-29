/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import ForgacsTran.BranchCurvature
import ForgacsTran.PencilIndex
import ForgacsTran.BranchTangentSum
import ForgacsTran.PhaseTangency
import ForgacsTran.InteriorSupply
import ForgacsTran.BranchAmplitude
import ForgacsTran.BranchSupply

/-!
# The branch angles' derivatives sum to `r`

`BranchTangentSum.sum_sq_cot_lt_of_branch` proves the curvature target for **any** weights
summing to `r`.  The weights the pencil supplies are the branch angles' derivatives, so what
connects that theorem to the pencil is the fact below: differentiating the branch equation
`∑_k θ_k = rθ + lπ` gives `∑_k θ_k' = r`.

This is the first step of the assembly that turns `PhaseTangency`'s `hcurv` binder into a
theorem.  The remaining steps are the identity

    (∑_k a_k sin²θ_k) · (v'' + v) / sin θ  =  2 [ r cot θ - ∑_k (θ_k')² cot θ_k ],
    v = 1/τ,   and   K = τ² + 2τ'² - ττ'' = τ³ (v'' + v),

which is where the second derivative of the branch equation enters — and which needs no
second derivative of a branch angle, because it is the *summed* first-order relation that
gets differentiated.

## Main statements

* `sum_ftBranchAngleDeriv` — `∑_k θ_k' = r`.
* `ftInvIm`, `ftInvImDeriv`, `ftInvImDeriv2` — the chart coordinate `R = 1/(τ sin θ)` and
  its two derivatives.
* `ftInvIm_deriv2_add_two_cot` — `R'' + 2 cot θ · R' = K/(τ³ sin θ)`, which is where the
  curvature sits in the chart.
* `cot_ftBranchAngle`, `ftBranchAngleDeriv_chart` — the branch angles are affine in `R`, and
  that identity differentiated.

## References

* `../shields-2026-forgacs-tran-numerators.tex`, `thm:FT-geometry`.
* `Forgacs2017RationalDenominator`, Lemma 2.
* `../scripts/check_branch_convexity.py`, blocks X7 and X11.

## Tags

branch angles, angle sum, derivative, curvature
-/

namespace ForgacsTran

open Real Set

/-- The derivative of the `k`-th branch angle, as `hasDerivAt_ftBranchAngle` states it. -/
noncomputable def ftBranchAngleDeriv {n : ℕ} (a : Fin n → ℝ) (r l : ℕ) (k : Fin n)
    (θ : ℝ) : ℝ :=
  -(Real.sin (ftBranchAngle a r l k θ) ^ 2 * a k / (ftTau a r l θ ^ 2 * Real.sin θ))
      * ftTauDeriv a r l θ
    + Real.sin (ftBranchAngle a r l k θ) * Real.cos (ftBranchAngle a r l k θ - θ)
      / Real.sin θ

theorem hasDerivAt_ftBranchAngle' {n r l : ℕ} {a : Fin n → ℝ} (hn : 0 < n)
    (ha : ∀ k, 0 < a k) (hr : 1 ≤ r) {θ₀ : ℝ} (hθ₀ : θ₀ ∈ Ioo 0 (π / r))
    (hb : ∀ θ ∈ Ioo 0 (π / r), FTBranchAt a r l θ) (k : Fin n) :
    HasDerivAt (ftBranchAngle a r l k) (ftBranchAngleDeriv a r l k θ₀) θ₀ :=
  hasDerivAt_ftBranchAngle hn ha hr hθ₀ hb k

/-- **`∑_k θ_k' = r`.**  The branch equation `∑_k θ_k = rθ + lπ` holds on the whole arc, and
the arc is open, so differentiating it is legitimate; the left side differentiates termwise.

This is the weight identity `sum_sq_cot_lt_of_branch` consumes: the pencil's weights are
these derivatives, and what that theorem asks of them is exactly that they sum to `r`. -/
theorem sum_ftBranchAngleDeriv {n r l : ℕ} {a : Fin n → ℝ} (hn : 0 < n)
    (ha : ∀ k, 0 < a k) (hr : 1 ≤ r) {θ₀ : ℝ} (hθ₀ : θ₀ ∈ Ioo 0 (π / r))
    (hb : ∀ θ ∈ Ioo 0 (π / r), FTBranchAt a r l θ) :
    ∑ k, ftBranchAngleDeriv a r l k θ₀ = r := by
  classical
  have hd : HasDerivAt (fun θ => ∑ k, ftBranchAngle a r l k θ)
      (∑ k, ftBranchAngleDeriv a r l k θ₀) θ₀ :=
    HasDerivAt.fun_sum fun k _ => hasDerivAt_ftBranchAngle' hn ha hr hθ₀ hb k
  have heq : (fun θ => ∑ k, ftBranchAngle a r l k θ)
      =ᶠ[nhds θ₀] fun θ => (r : ℝ) * θ + l * π := by
    filter_upwards [isOpen_Ioo.mem_nhds hθ₀] with x hx
    have := ftAngleSum_ftTau (hb x hx)
    rw [ftAngleSum] at this
    exact this
  have h0 : HasDerivAt (fun θ : ℝ => (r : ℝ) * θ + l * π) (r : ℝ) θ₀ := by
    simpa using ((hasDerivAt_id θ₀).const_mul (r : ℝ)).add_const ((l : ℝ) * π)
  exact hd.unique (h0.congr_of_eventuallyEq heq)

/-! ### The chart coordinate `R = 1/(τ sin θ)`, and where the curvature sits in it

`cot θ_k = cot θ - a_k R` is the branch angle's definition read as a chart: each angle is an
affine function of one scalar `R`, with only `a_k` varying.  Differentiating that twice is
what produces the curvature, and the combination it produces is

    R'' + 2 cot θ · R'  =  K / (τ³ sin θ),      K = τ² + 2τ'² - ττ''.

**This merges P5 and P6 of the assembly into one identity** — the detour through `v = 1/τ`,
where `K = τ³(v'' + v)` and `R'' + 2 cot θ R' = (v'' + v)/sin θ`, is not needed: the two
compose to the statement above, whose proof is one `field` over
`2N² - N'τ sin θ - 2Nτ cos θ = K sin²θ` with `N = τ' sin θ + τ cos θ`. -/

/-- `R = 1/(τ sin θ) = 1/Im γ`, the chart coordinate in which the branch angles are affine. -/
noncomputable def ftInvIm {n : ℕ} (a : Fin n → ℝ) (r l : ℕ) (θ : ℝ) : ℝ :=
  1 / (ftTau a r l θ * Real.sin θ)

/-- `R'`. -/
noncomputable def ftInvImDeriv {n : ℕ} (a : Fin n → ℝ) (r l : ℕ) (θ : ℝ) : ℝ :=
  -(ftTauDeriv a r l θ * Real.sin θ + ftTau a r l θ * Real.cos θ)
    / (ftTau a r l θ ^ 2 * Real.sin θ ^ 2)

/-- `R''`, with `N = τ' sin θ + τ cos θ` and `N' = τ'' sin θ + 2τ' cos θ - τ sin θ`. -/
noncomputable def ftInvImDeriv2 {n : ℕ} (a : Fin n → ℝ) (r l : ℕ) (θ : ℝ) : ℝ :=
  (2 * (ftTauDeriv a r l θ * Real.sin θ + ftTau a r l θ * Real.cos θ) ^ 2
      - (ftTauDeriv2 a r l θ * Real.sin θ + 2 * ftTauDeriv a r l θ * Real.cos θ
          - ftTau a r l θ * Real.sin θ) * (ftTau a r l θ * Real.sin θ))
    / (ftTau a r l θ ^ 3 * Real.sin θ ^ 3)

section Chart

variable {n r l : ℕ} {a : Fin n → ℝ}

theorem hasDerivAt_ftInvIm (hn : 0 < n) (ha : ∀ k, 0 < a k) (hr : 1 ≤ r) {θ₀ : ℝ}
    (hθ₀ : θ₀ ∈ Ioo 0 (π / r)) (hb : ∀ θ ∈ Ioo 0 (π / r), FTBranchAt a r l θ) :
    HasDerivAt (ftInvIm a r l) (ftInvImDeriv a r l θ₀) θ₀ := by
  have hθπ : θ₀ ∈ Ioo 0 π := ftArc_subset hr hθ₀
  have hs : 0 < Real.sin θ₀ := Real.sin_pos_of_pos_of_lt_pi hθπ.1 hθπ.2
  have hτ : 0 < ftTau a r l θ₀ := ftTau_pos (hb θ₀ hθ₀)
  have hden : HasDerivAt (fun t => ftTau a r l t * Real.sin t)
      (ftTauDeriv a r l θ₀ * Real.sin θ₀ + ftTau a r l θ₀ * Real.cos θ₀) θ₀ :=
    (hasDerivAt_ftTau hn ha hr hθ₀ hb).mul (Real.hasDerivAt_sin θ₀)
  have hne : ftTau a r l θ₀ * Real.sin θ₀ ≠ 0 := (mul_pos hτ hs).ne'
  refine ((hasDerivAt_const θ₀ (1 : ℝ)).div hden hne).congr_deriv ?_
  rw [ftInvImDeriv]
  field

theorem hasDerivAt_ftInvImDeriv (hn : 0 < n) (ha : ∀ k, 0 < a k) (hr : 1 ≤ r) {θ₀ : ℝ}
    (hθ₀ : θ₀ ∈ Ioo 0 (π / r)) (hb : ∀ θ ∈ Ioo 0 (π / r), FTBranchAt a r l θ) :
    HasDerivAt (ftInvImDeriv a r l) (ftInvImDeriv2 a r l θ₀) θ₀ := by
  have hθπ : θ₀ ∈ Ioo 0 π := ftArc_subset hr hθ₀
  have hs : 0 < Real.sin θ₀ := Real.sin_pos_of_pos_of_lt_pi hθπ.1 hθπ.2
  have hτ : 0 < ftTau a r l θ₀ := ftTau_pos (hb θ₀ hθ₀)
  have hτd := hasDerivAt_ftTau hn ha hr hθ₀ hb
  have hτd2 := hasDerivAt_ftTauDeriv hn ha hr hθ₀ hb
  have hN : HasDerivAt (fun t => -(ftTauDeriv a r l t * Real.sin t + ftTau a r l t * Real.cos t))
      (-(ftTauDeriv2 a r l θ₀ * Real.sin θ₀ + 2 * ftTauDeriv a r l θ₀ * Real.cos θ₀
        - ftTau a r l θ₀ * Real.sin θ₀)) θ₀ := by
    refine ((hτd2.mul (Real.hasDerivAt_sin θ₀)).add
      (hτd.mul (Real.hasDerivAt_cos θ₀))).neg.congr_deriv ?_
    ring
  have hD : HasDerivAt (fun t => ftTau a r l t ^ 2 * Real.sin t ^ 2)
      (2 * ftTau a r l θ₀ * ftTauDeriv a r l θ₀ * Real.sin θ₀ ^ 2
        + ftTau a r l θ₀ ^ 2 * (2 * Real.sin θ₀ * Real.cos θ₀)) θ₀ := by
    refine ((hτd.pow 2).mul ((Real.hasDerivAt_sin θ₀).pow 2)).congr_deriv ?_
    simp only [Pi.pow_apply]
    push_cast
    ring
  have hDne : ftTau a r l θ₀ ^ 2 * Real.sin θ₀ ^ 2 ≠ 0 := by positivity
  refine (hN.div hD hDne).congr_deriv ?_
  rw [ftInvImDeriv2]
  field

/-- **The curvature, in the chart.**  `K = τ² + 2τ'² - ττ''` is exactly what the combination
`R'' + 2 cot θ · R'` sees, and nothing else about the branch enters. -/
theorem ftInvIm_deriv2_add_two_cot (hr : 1 ≤ r) {θ₀ : ℝ}
    (hθ₀ : θ₀ ∈ Ioo 0 (π / r)) (hb : ∀ θ ∈ Ioo 0 (π / r), FTBranchAt a r l θ) :
    ftInvImDeriv2 a r l θ₀
        + 2 * (Real.cos θ₀ / Real.sin θ₀) * ftInvImDeriv a r l θ₀
      = (ftTau a r l θ₀ ^ 2 + 2 * ftTauDeriv a r l θ₀ ^ 2
          - ftTau a r l θ₀ * ftTauDeriv2 a r l θ₀)
        / (ftTau a r l θ₀ ^ 3 * Real.sin θ₀) := by
  have hθπ : θ₀ ∈ Ioo 0 π := ftArc_subset hr hθ₀
  have hs : 0 < Real.sin θ₀ := Real.sin_pos_of_pos_of_lt_pi hθπ.1 hθπ.2
  have hτ : 0 < ftTau a r l θ₀ := ftTau_pos (hb θ₀ hθ₀)
  rw [ftInvImDeriv2, ftInvImDeriv]
  field

end Chart

/-! ### The branch angles are affine in the chart

`cot θ_k = cot θ - a_k R` is `ftAngle`'s own definition read as a chart, and differentiating
it once gives `θ_k'/sin²θ_k = 1/sin²θ + a_k R'`.

**No second derivative of a branch angle is needed anywhere.**  The step that looked as
though it wanted `θ_k''` — differentiating the per-angle relation twice — is avoided by
differentiating the *summed* first-order relation instead: with `P = ∑_k sin²θ_k` and
`A = ∑_k a_k sin²θ_k`, summing the display above against `sin²θ_k` gives
`r = P/sin²θ + R'·A`, and one derivative of *that* involves only `θ_k'`, since
`d/dθ sin²θ_k = sin(2θ_k)·θ_k'`.  The tree carries `θ_k'` (`hasDerivAt_ftBranchAngle`) and
carries no `θ_k''`; it does not need one. -/

section Affine

variable {n r l : ℕ} {a : Fin n → ℝ}

private theorem hasDerivAt_cot_comp {f : ℝ → ℝ} {f' θ₀ : ℝ} (hf : HasDerivAt f f' θ₀)
    (hs : Real.sin (f θ₀) ≠ 0) :
    HasDerivAt (fun t => Real.cos (f t) / Real.sin (f t))
      (-f' / Real.sin (f θ₀) ^ 2) θ₀ := by
  have hc : HasDerivAt (fun t => Real.cos (f t)) (-Real.sin (f θ₀) * f') θ₀ := hf.cos
  have hsn : HasDerivAt (fun t => Real.sin (f t)) (Real.cos (f θ₀) * f') θ₀ := hf.sin
  refine (hc.div hsn hs).congr_deriv ?_
  field_simp
  linear_combination (-f') * Real.sin_sq_add_cos_sq (f θ₀)

/-- **The chart identity.**  `ftAngle` is `arccot` of `cot θ - a/(τ sin θ)`, so the branch
angles are affine in `R = 1/(τ sin θ)` with only `a_k` varying. -/
theorem cot_ftBranchAngle (ha : ∀ k, 0 < a k) (hr : 1 ≤ r) {θ : ℝ}
    (hθ : θ ∈ Ioo 0 (π / r)) (hb : FTBranchAt a r l θ) (k : Fin n) :
    Real.cos (ftBranchAngle a r l k θ) / Real.sin (ftBranchAngle a r l k θ)
      = Real.cos θ / Real.sin θ - a k * ftInvIm a r l θ := by
  have hθπ : θ ∈ Ioo 0 π := ftArc_subset hr hθ
  have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθπ.1 hθπ.2
  have hτ : 0 < ftTau a r l θ := ftTau_pos hb
  have hmem := ftAngle_mem_Ioo (ha k) hτ hθπ
  have hsk : 0 < Real.sin (ftBranchAngle a r l k θ) :=
    Real.sin_pos_of_pos_of_lt_pi (lt_trans hθπ.1 hmem.1) hmem.2
  have hcos : Real.cos (ftBranchAngle a r l k θ)
      = (Real.cos θ / Real.sin θ - a k / (ftTau a r l θ * Real.sin θ))
        * Real.sin (ftBranchAngle a r l k θ) := cos_ftArccot _
  rw [ftInvIm, hcos]
  field_simp

/-- **The chart identity, differentiated.**  `θ_k'/sin²θ_k = 1/sin²θ + a_k R'`. -/
theorem ftBranchAngleDeriv_chart (hn : 0 < n) (ha : ∀ k, 0 < a k) (hr : 1 ≤ r) {θ₀ : ℝ}
    (hθ₀ : θ₀ ∈ Ioo 0 (π / r)) (hb : ∀ θ ∈ Ioo 0 (π / r), FTBranchAt a r l θ) (k : Fin n) :
    ftBranchAngleDeriv a r l k θ₀ / Real.sin (ftBranchAngle a r l k θ₀) ^ 2
      = 1 / Real.sin θ₀ ^ 2 + a k * ftInvImDeriv a r l θ₀ := by
  have hθπ : θ₀ ∈ Ioo 0 π := ftArc_subset hr hθ₀
  have hs : 0 < Real.sin θ₀ := Real.sin_pos_of_pos_of_lt_pi hθπ.1 hθπ.2
  have hτ : 0 < ftTau a r l θ₀ := ftTau_pos (hb θ₀ hθ₀)
  have hmem := ftAngle_mem_Ioo (ha k) hτ hθπ
  have hsk : 0 < Real.sin (ftBranchAngle a r l k θ₀) :=
    Real.sin_pos_of_pos_of_lt_pi (lt_trans hθπ.1 hmem.1) hmem.2
  -- the left side
  have hL : HasDerivAt (fun t => Real.cos (ftBranchAngle a r l k t)
      / Real.sin (ftBranchAngle a r l k t))
      (-(ftBranchAngleDeriv a r l k θ₀) / Real.sin (ftBranchAngle a r l k θ₀) ^ 2) θ₀ :=
    hasDerivAt_cot_comp (hasDerivAt_ftBranchAngle' hn ha hr hθ₀ hb k) hsk.ne'
  -- the right side
  have hR : HasDerivAt (fun t => Real.cos t / Real.sin t - a k * ftInvIm a r l t)
      (-1 / Real.sin θ₀ ^ 2 - a k * ftInvImDeriv a r l θ₀) θ₀ := by
    have h1 : HasDerivAt (fun t : ℝ => Real.cos t / Real.sin t)
        (-1 / Real.sin θ₀ ^ 2) θ₀ := by
      have := hasDerivAt_cot_comp (f := fun t : ℝ => t) (hasDerivAt_id θ₀) hs.ne'
      simpa using this
    exact h1.sub ((hasDerivAt_ftInvIm hn ha hr hθ₀ hb).const_mul (a k))
  have heq : (fun t => Real.cos (ftBranchAngle a r l k t)
      / Real.sin (ftBranchAngle a r l k t))
      =ᶠ[nhds θ₀] fun t => Real.cos t / Real.sin t - a k * ftInvIm a r l t := by
    filter_upwards [isOpen_Ioo.mem_nhds hθ₀] with x hx
    exact cot_ftBranchAngle ha hr hx (hb x hx) k
  have := hL.unique (hR.congr_of_eventuallyEq heq)
  have hsk2 : Real.sin (ftBranchAngle a r l k θ₀) ^ 2 ≠ 0 := by positivity
  field_simp at this ⊢
  linarith [this]

end Affine

/-! ### The assembly

`P = ∑_k sin²θ_k` and `A = ∑_k a_k sin²θ_k`.  Multiplying the chart derivative through by
`sin²θ_k` and summing against `∑_k θ_k' = r` gives

    r = P/sin²θ + R'·A,

a **first-order** relation.  One derivative of it involves only `θ_k'`, because
`d/dθ sin²θ_k = sin(2θ_k)·θ_k'` — no `θ_k''` anywhere.  Combining with the first relation
again to eliminate `R'A` leaves

    A·(R'' + 2 cot θ · R')  =  2 [ r cot θ - ∑_k (θ_k')² cot θ_k ],

where the cross terms do not have to be estimated: `P'/sin²θ + R'A'` collapses **exactly** to
`2∑_k (θ_k')² cot θ_k`, because the factor `1/sin²θ + a_k R'` it carries is `θ_k'/sin²θ_k` by
the chart derivative itself.  With `ftInvIm_deriv2_add_two_cot` the left side is
`A·K/(τ³ sin θ)`, and `BranchTangentSum.sum_sq_cot_lt_of_branch_of_pos` makes the right side
positive. -/

section Assembly

variable {n r l : ℕ} {a : Fin n → ℝ}

/-- `P = ∑_k sin²θ_k`. -/
noncomputable def ftAngleSinSq (a : Fin n → ℝ) (r l : ℕ) (θ : ℝ) : ℝ :=
  ∑ k, Real.sin (ftBranchAngle a r l k θ) ^ 2

/-- `A = ∑_k a_k sin²θ_k`, the denominator of the assembly. -/
noncomputable def ftAngleSinSqWeighted (a : Fin n → ℝ) (r l : ℕ) (θ : ℝ) : ℝ :=
  ∑ k, a k * Real.sin (ftBranchAngle a r l k θ) ^ 2

/-- **`A > 0`.**  Every `a_k` is positive and no branch angle is `0` or `π`, so nothing is
divided by zero in the assembly. -/
theorem ftAngleSinSqWeighted_pos (hn : 0 < n) (ha : ∀ k, 0 < a k) (hr : 1 ≤ r) {θ : ℝ}
    (hθ : θ ∈ Ioo 0 (π / r)) (hb : FTBranchAt a r l θ) :
    0 < ftAngleSinSqWeighted a r l θ := by
  have hθπ : θ ∈ Ioo 0 π := ftArc_subset hr hθ
  have hτ : 0 < ftTau a r l θ := ftTau_pos hb
  refine Finset.sum_pos (fun k _ => ?_) ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  have hmem := ftAngle_mem_Ioo (ha k) hτ hθπ
  have hsk : 0 < Real.sin (ftBranchAngle a r l k θ) :=
    Real.sin_pos_of_pos_of_lt_pi (lt_trans hθπ.1 hmem.1) hmem.2
  have := ha k
  positivity

theorem hasDerivAt_ftAngleSinSq (hn : 0 < n) (ha : ∀ k, 0 < a k) (hr : 1 ≤ r) {θ₀ : ℝ}
    (hθ₀ : θ₀ ∈ Ioo 0 (π / r)) (hb : ∀ θ ∈ Ioo 0 (π / r), FTBranchAt a r l θ) :
    HasDerivAt (ftAngleSinSq a r l)
      (∑ k, 2 * Real.sin (ftBranchAngle a r l k θ₀)
        * (Real.cos (ftBranchAngle a r l k θ₀) * ftBranchAngleDeriv a r l k θ₀)) θ₀ := by
  refine HasDerivAt.fun_sum fun k _ => ?_
  have h := ((hasDerivAt_ftBranchAngle' hn ha hr hθ₀ hb k).sin).pow 2
  refine h.congr_deriv ?_
  push_cast
  ring

theorem hasDerivAt_ftAngleSinSqWeighted (hn : 0 < n) (ha : ∀ k, 0 < a k) (hr : 1 ≤ r)
    {θ₀ : ℝ} (hθ₀ : θ₀ ∈ Ioo 0 (π / r)) (hb : ∀ θ ∈ Ioo 0 (π / r), FTBranchAt a r l θ) :
    HasDerivAt (ftAngleSinSqWeighted a r l)
      (∑ k, a k * (2 * Real.sin (ftBranchAngle a r l k θ₀)
        * (Real.cos (ftBranchAngle a r l k θ₀) * ftBranchAngleDeriv a r l k θ₀))) θ₀ := by
  refine HasDerivAt.fun_sum fun k _ => ?_
  have h := (((hasDerivAt_ftBranchAngle' hn ha hr hθ₀ hb k).sin).pow 2).const_mul (a k)
  refine h.congr_deriv ?_
  push_cast
  ring

/-- **The first-order relation.**  `r = P/sin²θ + R'·A`, the chart derivative summed. -/
theorem branch_chart_sum (hn : 0 < n) (ha : ∀ k, 0 < a k) (hr : 1 ≤ r) {θ : ℝ}
    (hθ : θ ∈ Ioo 0 (π / r)) (hb : ∀ s ∈ Ioo 0 (π / r), FTBranchAt a r l s) :
    (r : ℝ) = ftAngleSinSq a r l θ / Real.sin θ ^ 2
      + ftInvImDeriv a r l θ * ftAngleSinSqWeighted a r l θ := by
  have hθπ : θ ∈ Ioo 0 π := ftArc_subset hr hθ
  have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθπ.1 hθπ.2
  have hτ : 0 < ftTau a r l θ := ftTau_pos (hb θ hθ)
  have hpt : ∀ k, ftBranchAngleDeriv a r l k θ
      = Real.sin (ftBranchAngle a r l k θ) ^ 2 / Real.sin θ ^ 2
        + ftInvImDeriv a r l θ * (a k * Real.sin (ftBranchAngle a r l k θ) ^ 2) := by
    intro k
    have hmem := ftAngle_mem_Ioo (ha k) hτ hθπ
    have hsk : 0 < Real.sin (ftBranchAngle a r l k θ) :=
      Real.sin_pos_of_pos_of_lt_pi (lt_trans hθπ.1 hmem.1) hmem.2
    have h := ftBranchAngleDeriv_chart hn ha hr hθ hb k
    field_simp at h ⊢
    linarith [h]
  rw [← sum_ftBranchAngleDeriv hn ha hr hθ hb, Finset.sum_congr rfl (fun k _ => hpt k),
    Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.mul_sum]
  rfl

/-- **The assembly identity.**  `A·(R'' + 2 cot θ · R') = 2[r cot θ - ∑_k (θ_k')² cot θ_k]`.
The cross terms collapse exactly rather than being bounded. -/
theorem branch_chart_second (hn : 0 < n) (ha : ∀ k, 0 < a k) (hr : 1 ≤ r) {θ : ℝ}
    (hθ : θ ∈ Ioo 0 (π / r)) (hb : ∀ s ∈ Ioo 0 (π / r), FTBranchAt a r l s) :
    ftAngleSinSqWeighted a r l θ
        * (ftInvImDeriv2 a r l θ + 2 * (Real.cos θ / Real.sin θ) * ftInvImDeriv a r l θ)
      = 2 * ((r : ℝ) * (Real.cos θ / Real.sin θ)
        - ∑ k, ftBranchAngleDeriv a r l k θ ^ 2
          * (Real.cos (ftBranchAngle a r l k θ) / Real.sin (ftBranchAngle a r l k θ))) := by
  classical
  have hθπ : θ ∈ Ioo 0 π := ftArc_subset hr hθ
  have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθπ.1 hθπ.2
  have hτ : 0 < ftTau a r l θ := ftTau_pos (hb θ hθ)
  have hS1 := branch_chart_sum hn ha hr hθ hb
  set dP := ∑ k, 2 * Real.sin (ftBranchAngle a r l k θ)
      * (Real.cos (ftBranchAngle a r l k θ) * ftBranchAngleDeriv a r l k θ) with hdPdef
  set dA := ∑ k, a k * (2 * Real.sin (ftBranchAngle a r l k θ)
      * (Real.cos (ftBranchAngle a r l k θ) * ftBranchAngleDeriv a r l k θ)) with hdAdef
  -- the first-order relation is constant on the arc, so its derivative vanishes
  have hFd : HasDerivAt
      (fun s => ftAngleSinSq a r l s / Real.sin s ^ 2
        + ftInvImDeriv a r l s * ftAngleSinSqWeighted a r l s)
      (dP / Real.sin θ ^ 2 - 2 * ftAngleSinSq a r l θ * Real.cos θ / Real.sin θ ^ 3
        + (ftInvImDeriv2 a r l θ * ftAngleSinSqWeighted a r l θ
          + ftInvImDeriv a r l θ * dA)) θ := by
    have h1 : HasDerivAt (fun s => ftAngleSinSq a r l s / Real.sin s ^ 2)
        ((dP * Real.sin θ ^ 2 - ftAngleSinSq a r l θ * (2 * Real.sin θ ^ 1 * Real.cos θ))
          / (Real.sin θ ^ 2) ^ 2) θ :=
      (hasDerivAt_ftAngleSinSq hn ha hr hθ hb).div ((Real.hasDerivAt_sin θ).pow 2)
        (by positivity)
    have h2 : HasDerivAt (fun s => ftInvImDeriv a r l s * ftAngleSinSqWeighted a r l s)
        (ftInvImDeriv2 a r l θ * ftAngleSinSqWeighted a r l θ
          + ftInvImDeriv a r l θ * dA) θ :=
      (hasDerivAt_ftInvImDeriv hn ha hr hθ hb).mul
        (hasDerivAt_ftAngleSinSqWeighted hn ha hr hθ hb)
    refine (h1.add h2).congr_deriv ?_
    field_simp
  have hF0 : HasDerivAt
      (fun s => ftAngleSinSq a r l s / Real.sin s ^ 2
        + ftInvImDeriv a r l s * ftAngleSinSqWeighted a r l s) 0 θ := by
    refine (hasDerivAt_const θ ((r : ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [isOpen_Ioo.mem_nhds hθ] with x hx
    exact (branch_chart_sum hn ha hr hx hb).symm
  have hzero := hFd.unique hF0
  -- the cross terms collapse exactly
  have hcollapse : dP / Real.sin θ ^ 2 + ftInvImDeriv a r l θ * dA
      = 2 * ∑ k, ftBranchAngleDeriv a r l k θ ^ 2
        * (Real.cos (ftBranchAngle a r l k θ) / Real.sin (ftBranchAngle a r l k θ)) := by
    rw [hdPdef, hdAdef, Finset.sum_div, Finset.mul_sum, ← Finset.sum_add_distrib,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hmem := ftAngle_mem_Ioo (ha k) hτ hθπ
    have hsk : (0 : ℝ) < Real.sin (ftBranchAngle a r l k θ) :=
      Real.sin_pos_of_pos_of_lt_pi (lt_trans hθπ.1 hmem.1) hmem.2
    have h := ftBranchAngleDeriv_chart hn ha hr hθ hb k
    -- substitute the derivative in its division-free form, so the cancellation of
    -- `sin θ_k` is one `field_simp` rather than something `ring` has to guess
    have hd : ftBranchAngleDeriv a r l k θ
        = Real.sin (ftBranchAngle a r l k θ) ^ 2
          * (1 / Real.sin θ ^ 2 + a k * ftInvImDeriv a r l θ) := by
      field_simp at h ⊢
      linarith [h]
    rw [hd]
    field_simp
  linear_combination hzero - 2 * (Real.cos θ / Real.sin θ) * hS1 - hcollapse

/-- **The signed curvature of the principal branch is positive.**  The assembly identity puts
`K` over the positive `A`, and `BranchTangentSum.sum_sq_cot_lt_of_branch_of_pos` makes the
numerator positive: the branch angles reflect to `φ_k = π - θ_k` summing to `π - rθ`, and
their derivatives sum to `r`. -/
theorem ftCurvature_pos {n r : ℕ} {a : Fin n → ℝ} (hn : 0 < n) (ha : ∀ k, 0 < a k)
    (hr : 1 ≤ r) (hnr : 2 ≤ n ∨ 2 ≤ r) {θ : ℝ} (hθ : θ ∈ Ioo 0 (π / r)) :
    0 < ftTau a r (n - 1) θ ^ 2 + 2 * ftTauDeriv a r (n - 1) θ ^ 2
      - ftTau a r (n - 1) θ * ftTauDeriv2 a r (n - 1) θ := by
  classical
  have hθπ : θ ∈ Ioo 0 π := ftArc_subset hr hθ
  have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθπ.1 hθπ.2
  have hb : ∀ s ∈ Ioo (0 : ℝ) (π / r), FTBranchAt a r (n - 1) s :=
    fun s hs' => ftBranchAt_of_arc_principal hn ha hr hnr hs'
  have hτ : 0 < ftTau a r (n - 1) θ := ftTau_pos (hb θ hθ)
  have hA : 0 < ftAngleSinSqWeighted a r (n - 1) θ :=
    ftAngleSinSqWeighted_pos hn ha hr hθ (hb θ hθ)
  -- the reflected angles and their derivatives feed the combinatorial core
  have hlt : ∑ k, ftBranchAngleDeriv a r (n - 1) k θ ^ 2
      * (Real.cos (ftBranchAngle a r (n - 1) k θ)
        / Real.sin (ftBranchAngle a r (n - 1) k θ))
      < (r : ℝ) * (Real.cos θ / Real.sin θ) := by
    have hsum : ∑ k, (π - ftBranchAngle a r (n - 1) k θ) = π - (r : ℝ) * θ := by
      have h := ftAngleSum_ftTau (hb θ hθ)
      rw [ftAngleSum] at h
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      have hbr : ∑ k, ftBranchAngle a r (n - 1) k θ = (r : ℝ) * θ + ((n : ℝ) - 1) * π := by
        rw [show (∑ k, ftBranchAngle a r (n - 1) k θ)
            = ∑ k, ftAngle (a k) (ftTau a r (n - 1) θ) θ from rfl, h,
          cast_pred_eq_sub_one hn]
      rw [hbr]; ring
    have hres := sum_sq_cot_lt_of_branch_of_pos (φ := fun k => π - ftBranchAngle a r (n-1) k θ)
      (w := fun k => ftBranchAngleDeriv a r (n - 1) k θ) hr hnr hθ
      (fun k => by
        have hlt := ftAngle_lt_pi (a k) (ftTau a r (n - 1) θ) θ
        simp only [ftBranchAngle]
        linarith) hsum
      (sum_ftBranchAngleDeriv hn ha hr hθ hb)
    simpa using hres
  have hid := branch_chart_second hn ha hr hθ hb
  rw [ftInvIm_deriv2_add_two_cot hr hθ hb] at hid
  have hnum : 0 < 2 * ((r : ℝ) * (Real.cos θ / Real.sin θ)
      - ∑ k, ftBranchAngleDeriv a r (n - 1) k θ ^ 2
        * (Real.cos (ftBranchAngle a r (n - 1) k θ)
          / Real.sin (ftBranchAngle a r (n - 1) k θ))) := by linarith
  rw [← hid] at hnum
  have hden : 0 < ftTau a r (n - 1) θ ^ 3 * Real.sin θ := by positivity
  have hX : 0 < (ftTau a r (n - 1) θ ^ 2 + 2 * ftTauDeriv a r (n - 1) θ ^ 2
      - ftTau a r (n - 1) θ * ftTauDeriv2 a r (n - 1) θ)
      / (ftTau a r (n - 1) θ ^ 3 * Real.sin θ) := by
    rcases mul_pos_iff.1 hnum with ⟨_, h⟩ | ⟨h, _⟩
    · exact h
    · exact absurd h (not_lt.2 hA.le)
  rcases div_pos_iff.1 hX with ⟨h, _⟩ | ⟨_, h⟩
  · exact h
  · exact absurd h (not_lt.2 hden.le)

/-- **`PhaseTangency`'s `hcurv`, discharged at the general principal pencil.** -/
theorem wedge_ftGammaDeriv2_ftGammaDeriv_ne_zero {n r : ℕ} {a : Fin n → ℝ} (hn : 0 < n)
    (ha : ∀ k, 0 < a k) (hr : 1 ≤ r) (hnr : 2 ≤ n ∨ 2 ≤ r) {θ : ℝ}
    (hθ : θ ∈ Ioo 0 (π / r)) :
    wedge (ftGammaDeriv2 a r (n - 1) θ) (ftGammaDeriv a r (n - 1) θ) ≠ 0 := by
  rw [wedge_ftGammaDeriv2_ftGammaDeriv]
  exact (ftCurvature_pos hn ha hr hnr hθ).ne'


/-! ### `hstate` and `hcurv` both discharged, at the pencil's own branch

`PhaseTangency`'s three `hcurv` binders are about an **arbitrary** `C²` arc and cannot be
removed: `not_finite_tangency_zeros_of_line` exhibits an arc where the conclusion fails.
What `ftCurvature_pos` discharges is `hcurv` **at the pencil**, and the statement that carries
that is the specialization below — the phase-variation bound at the principal branch, with no
`hstate` and no `hcurv` left to supply. -/

/-- The branch point's tangent never vanishes: `γ' = e^{iθ}(τ' + iτ)` and `τ > 0`. -/
theorem ftGammaDeriv_ne_zero {n r l : ℕ} {a : Fin n → ℝ} {θ : ℝ}
    (hb : FTBranchAt a r l θ) : ftGammaDeriv a r l θ ≠ 0 := by
  rw [ftGammaDeriv]
  refine mul_ne_zero (Complex.exp_ne_zero _) ?_
  intro h
  have him := congrArg Complex.im h
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
    Complex.I_im, mul_one, Complex.I_re, mul_zero, add_zero, zero_add, Complex.zero_im] at him
  exact absurd him (ftTau_pos hb).ne'

/-- **`cor:linear-phase-variation` at one zero of `B`, on the pencil's own branch, with
nothing left to assume.**  The regularity is the tree's own `C²` package for the branch, the
injectivity is `InteriorSupply.injOn_ftPrincipal`, and the curvature is `ftCurvature_pos`.

`hfree` is what the composition already carries: the amplitude does not vanish on a retained
block, and an amplitude zero is exactly a parameter where `B ∘ γ` vanishes. -/
theorem sum_eVariationOn_ftBranch {n r : ℕ} {a : Fin n → ℝ} (hn : 0 < n) (ha : ∀ k, 0 < a k)
    (hr : 1 ≤ r) (hnr : 2 ≤ n ∨ 2 ≤ r) {u v Kγ : ℝ} {β : ℂ} {m : ℕ} {Lb Rb : Fin m → ℝ}
    (huv : u ≤ v) (hsub : Icc u v ⊆ Ioo 0 (π / r)) (hKγ : 0 ≤ Kγ)
    (hKvar : eVariationOn (polarAngle (ftGammaDeriv a r (n - 1))
        (ftGammaDeriv2 a r (n - 1)) 0 u) (Icc u v) ≤ ENNReal.ofReal Kγ)
    (hJ : ∀ i, Icc (Lb i) (Rb i) ⊆ Icc u v)
    (hord : ∀ i j : Fin m, i < j → Rb i ≤ Lb j)
    (hfree : ∀ i, ∀ x ∈ Icc (Lb i) (Rb i), ftPrincipal (ftTau a r (n - 1)) x ≠ β) :
    ∃ ψ : Fin m → ℝ → ℝ,
      (∀ i, ψ i = polarAngle (ftPrincipal (ftTau a r (n - 1)))
            (ftGammaDeriv a r (n - 1)) β u
          ∨ ψ i = polarAngle (ftPrincipal (ftTau a r (n - 1)))
            (ftGammaDeriv a r (n - 1)) β v) ∧
      ∑ i, eVariationOn (ψ i) (Icc (Lb i) (Rb i)) ≤ ENNReal.ofReal (Kγ + π) := by
  have hb : ∀ s ∈ Ioo (0 : ℝ) (π / r), FTBranchAt a r (n - 1) s :=
    fun s hs => ftBranchAt_of_arc_principal hn ha hr hnr hs
  have harc : Icc u v ⊆ Ioo 0 π := fun s hs => ftArc_subset hr (hsub hs)
  refine sum_eVariationOn_of_curvature (γ := ftPrincipal (ftTau a r (n - 1)))
    (dγ := ftGammaDeriv a r (n - 1)) (d2γ := ftGammaDeriv2 a r (n - 1))
    (U := Ioo 0 (π / r)) huv isOpen_Ioo hsub
    (fun s hs => hasDerivAt_ftBranchGamma hn ha hr hs hb)
    (fun s hs => hasDerivAt_ftGammaDeriv hn ha hr hs hb)
    (fun s hs => (continuousAt_ftGammaDeriv2 hn ha hr hs hb).continuousWithinAt)
    (fun s hs => ftGammaDeriv_ne_zero (hb s (hsub hs))) hKγ hKvar
    (fun s hs => wedge_ftGammaDeriv2_ftGammaDeriv_ne_zero hn ha hr hnr (hsub hs))
    (injOn_ftPrincipal harc (fun s hs => ftTau_pos (hb s (hsub hs)))) hJ hord hfree

/-- **`BranchSupply.RootBranchState` at the general principal pencil.**  The state is
produced rather than assumed: `exists_phaseState_of_curvature` builds it from the arc's `C²`
package, its injectivity and its curvature, and `ftCurvature_pos` supplies the last of those
for every admissible `Q` and `r`.

This is the group `RootBranchState` was carrying at witness pencils only. -/
theorem exists_rootBranchState_ftBranch {n r : ℕ} {a : Fin n → ℝ} (hn : 0 < n)
    (ha : ∀ k, 0 < a k) (hr : 1 ≤ r) (hnr : 2 ≤ n ∨ 2 ≤ r) {u v : ℝ} {β : ℂ}
    {m : ℕ} {Lb Rb : Fin m → ℝ}
    (huv : u ≤ v) (hsub : Icc u v ⊆ Ioo 0 (π / r))
    (hJ : ∀ i, Icc (Lb i) (Rb i) ⊆ Icc u v)
    (hfree : ∀ i, ∀ x ∈ Icc (Lb i) (Rb i), ftPrincipal (ftTau a r (n - 1)) x ≠ β) :
    ∃ ψ : Fin m → ℝ → ℝ,
      RootBranchState (ftPrincipal (ftTau a r (n - 1))) (ftGammaDeriv a r (n - 1))
        (ftGammaDeriv2 a r (n - 1)) β u v Lb Rb ψ := by
  have hb : ∀ s ∈ Ioo (0 : ℝ) (π / r), FTBranchAt a r (n - 1) s :=
    fun s hs => ftBranchAt_of_arc_principal hn ha hr hnr hs
  have harc : Icc u v ⊆ Ioo 0 π := fun s hs => ftArc_subset hr (hsub hs)
  obtain ⟨ψ, -, hstate⟩ := exists_phaseState_of_curvature
    (γ := ftPrincipal (ftTau a r (n - 1))) (dγ := ftGammaDeriv a r (n - 1))
    (d2γ := ftGammaDeriv2 a r (n - 1)) (U := Ioo 0 (π / r)) (β := β)
    huv isOpen_Ioo hsub
    (fun s hs => hasDerivAt_ftBranchGamma hn ha hr hs hb)
    (fun s hs => hasDerivAt_ftGammaDeriv hn ha hr hs hb)
    (fun s hs => (continuousAt_ftGammaDeriv2 hn ha hr hs hb).continuousWithinAt)
    (fun s hs => ftGammaDeriv_ne_zero (hb s (hsub hs)))
    (fun s hs => wedge_ftGammaDeriv2_ftGammaDeriv_ne_zero hn ha hr hnr (hsub hs))
    (injOn_ftPrincipal harc (fun s hs => ftTau_pos (hb s (hsub hs)))) hJ hfree
  exact ⟨ψ, hstate⟩

/-! ### `hKvar` at a general pencil

The curvature closes this one immediately.  `Im(γ''/γ')` is `wedge (γ'') (γ')/‖γ'‖²`, so
`ftCurvature_pos` makes it **positive**: the tangent angle is strictly increasing, and its
variation over any subinterval is just its increment.  And the increment is bounded with
nothing further to prove, because `γ' = e^{iθ}(τ' + iτ)` has positive imaginary part in the
rotating frame: the lift minus `θ` has positive sine throughout, so it cannot move by `π`
without passing a point where the sine is negative.

    Var_{[u,v]} arg γ'  =  (v - u) + (ω(v) - ω(u))  <  (v - u) + π  ≤  π/r + π,

a constant of the pencil, free of the interval and hence of `M` — which is what
`κ₁ = 𝒦_γ + π` needs. -/

private theorem im_div_eq_wedge (z w : ℂ) : (z / w).im = wedge z w / Complex.normSq w := by
  rw [Complex.div_im, wedge]
  ring

/-- **`𝒦_γ ≤ π/r + π` at the general principal pencil.**  The tangent angle is monotone by
`ftCurvature_pos`, so its variation is its increment; and the increment is under `π` past the
parameter's own, because the tangent's argument in the rotating frame keeps a positive sine. -/
theorem eVariationOn_polarAngle_tangent_ftBranch {n r : ℕ} {a : Fin n → ℝ} (hn : 0 < n)
    (ha : ∀ k, 0 < a k) (hr : 1 ≤ r) (hnr : 2 ≤ n ∨ 2 ≤ r) {u v : ℝ}
    (huv : u ≤ v) (hsub : Icc u v ⊆ Ioo 0 (π / r)) :
    eVariationOn (polarAngle (ftGammaDeriv a r (n - 1)) (ftGammaDeriv2 a r (n - 1)) 0 u)
      (Icc u v) ≤ ENNReal.ofReal (π / r + π) := by
  classical
  have hπ : (0 : ℝ) < π := Real.pi_pos
  have hb : ∀ s ∈ Ioo (0 : ℝ) (π / r), FTBranchAt a r (n - 1) s :=
    fun s hs => ftBranchAt_of_arc_principal hn ha hr hnr hs
  have hreg : ∀ s ∈ Icc u v, ftGammaDeriv a r (n - 1) s ≠ 0 :=
    fun s hs => ftGammaDeriv_ne_zero (hb s (hsub hs))
  have hd2 : ∀ s ∈ Ioo (0 : ℝ) (π / r),
      HasDerivAt (ftGammaDeriv a r (n - 1)) (ftGammaDeriv2 a r (n - 1) s) s :=
    fun s hs => hasDerivAt_ftGammaDeriv hn ha hr hs hb
  have hc2 : ContinuousOn (ftGammaDeriv2 a r (n - 1)) (Ioo 0 (π / r)) :=
    fun s hs => (continuousAt_ftGammaDeriv2 hn ha hr hs hb).continuousWithinAt
  set f := polarAngle (ftGammaDeriv a r (n - 1)) (ftGammaDeriv2 a r (n - 1)) 0 u with hfdef
  have hderiv : ∀ s ∈ Icc u v, HasDerivAt f
      ((ftGammaDeriv2 a r (n - 1) s / ftGammaDeriv a r (n - 1) s).im) s := fun s hs => by
    have h := hasDerivAt_polarAngle (γ := ftGammaDeriv a r (n - 1))
      (dγ := ftGammaDeriv2 a r (n - 1)) (β := 0) isOpen_Ioo hsub hd2 hc2 hreg hs
    rwa [sub_zero] at h
  have hdpos : ∀ s ∈ Icc u v,
      0 < (ftGammaDeriv2 a r (n - 1) s / ftGammaDeriv a r (n - 1) s).im := by
    intro s hs
    rw [im_div_eq_wedge, wedge_ftGammaDeriv2_ftGammaDeriv]
    have h1 := ftCurvature_pos hn ha hr hnr (hsub hs)
    have h2 : 0 < Complex.normSq (ftGammaDeriv a r (n - 1) s) :=
      Complex.normSq_pos.2 (hreg s hs)
    positivity
  -- the lift is monotone, so its variation is its increment
  have hmono : MonotoneOn f (Icc u v) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc u v)
      (fun s hs => (hderiv s hs).continuousAt.continuousWithinAt)
      (fun s hs => by
        rw [interior_Icc] at hs
        exact (hderiv s (Ioo_subset_Icc_self hs)).differentiableAt.differentiableWithinAt)
      (fun s hs => ?_)
    rw [interior_Icc] at hs
    rw [(hderiv s (Ioo_subset_Icc_self hs)).deriv]
    exact (hdpos s (Ioo_subset_Icc_self hs)).le
  have hvar : eVariationOn f (Icc u v) = ENNReal.ofReal (f v - f u) := by
    have h := hmono.eVariationOn_eq (Set.left_mem_Icc.2 huv) (Set.right_mem_Icc.2 huv)
    rwa [Set.inter_self] at h
  -- the increment: the lift minus the parameter keeps a positive sine
  have hsin : ∀ s ∈ Icc u v, 0 < Real.sin (f s - s) := by
    intro s hs
    have hpol := polar_decomposition (γ := ftGammaDeriv a r (n - 1))
      (dγ := ftGammaDeriv2 a r (n - 1)) (β := 0) huv isOpen_Ioo hsub hd2 hc2 hreg hs
    rw [sub_zero, ftGammaDeriv] at hpol
    have hρ : 0 < polarModulus (ftGammaDeriv a r (n - 1)) (ftGammaDeriv2 a r (n - 1)) 0 u s :=
      polarModulus_pos _ _ _ _ _
    have hτ : 0 < ftTau a r (n - 1) s := ftTau_pos (hb s (hsub hs))
    have hkey : (polarModulus (ftGammaDeriv a r (n - 1)) (ftGammaDeriv2 a r (n - 1)) 0 u s)
        * Real.sin (f s - s) = ftTau a r (n - 1) s := by
      have hmul : ((polarModulus (ftGammaDeriv a r (n - 1)) (ftGammaDeriv2 a r (n - 1)) 0 u s
            : ℝ) : ℂ) * Complex.exp (((f s - s : ℝ) : ℂ) * Complex.I)
          = ((ftTauDeriv a r (n - 1) s : ℝ) : ℂ)
            + ((ftTau a r (n - 1) s : ℝ) : ℂ) * Complex.I := by
        have hexp : Complex.exp (((s : ℝ) : ℂ) * Complex.I) ≠ 0 := Complex.exp_ne_zero _
        rw [Complex.ofReal_sub, sub_mul, Complex.exp_sub]
        field_simp
        rw [← hpol]
        ring
      have := congrArg Complex.im hmul
      simpa [← Complex.ofReal_sub, Complex.exp_ofReal_mul_I_im,
        Complex.exp_ofReal_mul_I_re] using this
    nlinarith [hkey, hτ, hρ]
  have hω : f v - v - (f u - u) < π := by
    by_contra hcon
    push Not at hcon
    have hcont : ContinuousOn (fun s => f s - s) (Icc u v) := fun s hs =>
      ((hderiv s hs).continuousAt.sub continuousAt_id).continuousWithinAt
    have hmem : f u - u + π ∈ Icc (f u - u) (f v - v) := ⟨by linarith [hπ], by linarith⟩
    obtain ⟨s, hs, hval⟩ := intermediate_value_Icc huv hcont hmem
    have h1 := hsin s hs
    rw [show f s - s = f u - u + π from hval, Real.sin_add_pi] at h1
    linarith [hsin u (Set.left_mem_Icc.2 huv)]
  have hbound : f v - f u ≤ π / r + π := by
    have h1 : u ∈ Ioo (0 : ℝ) (π / r) := hsub (Set.left_mem_Icc.2 huv)
    have h2 : v ∈ Ioo (0 : ℝ) (π / r) := hsub (Set.right_mem_Icc.2 huv)
    linarith [h1.1, h2.2]
  rw [hvar]
  exact ENNReal.ofReal_le_ofReal hbound

/-! ### What the curvature says about `τ''`

`ftCurvature_pos` is `0 < τ² + 2τ'² - ττ''`, so dividing by `τ > 0` bounds the second
derivative **from above**, at every admissible pencil and everywhere on the open arc:

    τ'' < τ + 2τ'²/τ.

The matching lower bound is *not* free.  It is equivalent to an upper bound on the curvature
against the speed — `K < (r+1)(τ² + τ'²)`, i.e. `Im(γ''/γ') < r + 1` — and that is stated
below as a hypothesis rather than proved, because it is exactly what is missing.  In the
tangent-angle reading it is `∑_j ψ_j' > 0` summed over the **real** roots `c_j` of
`E = tQ' - rQ`, where `ψ_j = arg(γ - c_j)`; `E` has only real roots because `E = Q·g` with
`g = (n-r) + ∑_k a_k/(t - a_k)` mapping the upper half plane strictly into the lower one.

Both statements are on the **open** arc.  Neither says anything at a collision, and neither
may be evaluated there: `ftTauDeriv2 a r l 0` is junk from a vanishing denominator. -/

/-- **`τ'' < τ + 2τ'²/τ`.**  The curvature, divided by `τ`. -/
theorem ftTauDeriv2_lt {n r : ℕ} {a : Fin n → ℝ} (hn : 0 < n) (ha : ∀ k, 0 < a k)
    (hr : 1 ≤ r) (hnr : 2 ≤ n ∨ 2 ≤ r) {θ : ℝ} (hθ : θ ∈ Ioo 0 (π / r)) :
    ftTauDeriv2 a r (n - 1) θ
      < ftTau a r (n - 1) θ + 2 * ftTauDeriv a r (n - 1) θ ^ 2 / ftTau a r (n - 1) θ := by
  have hτ : 0 < ftTau a r (n - 1) θ :=
    ftTau_pos (ftBranchAt_of_arc_principal hn ha hr hnr hθ)
  have hK := ftCurvature_pos hn ha hr hnr hθ
  have h2 : ftTau a r (n - 1) θ
      + 2 * ftTauDeriv a r (n - 1) θ ^ 2 / ftTau a r (n - 1) θ
      = (ftTau a r (n - 1) θ ^ 2 + 2 * ftTauDeriv a r (n - 1) θ ^ 2)
        / ftTau a r (n - 1) θ := by
    field_simp
  rw [h2, lt_div_iff₀ hτ]
  nlinarith [hK]

/-- **The matching lower bound, conditional on the one fact that is missing.**  `hbound` is
`Im(γ''/γ') < r + 1` written against the speed; it is measured at every pencil sampled in
`../scripts/check_branch_convexity.py` and is not proved. -/
theorem ftTauDeriv2_gt_of_curvature_lt {n r : ℕ} {a : Fin n → ℝ} (hn : 0 < n)
    (ha : ∀ k, 0 < a k) (hr : 1 ≤ r) (hnr : 2 ≤ n ∨ 2 ≤ r) {θ : ℝ}
    (hθ : θ ∈ Ioo 0 (π / r))
    (hbound : ftTau a r (n - 1) θ ^ 2 + 2 * ftTauDeriv a r (n - 1) θ ^ 2
        - ftTau a r (n - 1) θ * ftTauDeriv2 a r (n - 1) θ
      < ((r : ℝ) + 1) * (ftTau a r (n - 1) θ ^ 2 + ftTauDeriv a r (n - 1) θ ^ 2)) :
    -(r : ℝ) * ftTau a r (n - 1) θ
        - ((r : ℝ) - 1) * ftTauDeriv a r (n - 1) θ ^ 2 / ftTau a r (n - 1) θ
      < ftTauDeriv2 a r (n - 1) θ := by
  have hτ : 0 < ftTau a r (n - 1) θ :=
    ftTau_pos (ftBranchAt_of_arc_principal hn ha hr hnr hθ)
  have h2 : -(r : ℝ) * ftTau a r (n - 1) θ
      - ((r : ℝ) - 1) * ftTauDeriv a r (n - 1) θ ^ 2 / ftTau a r (n - 1) θ
      = (-(r : ℝ) * ftTau a r (n - 1) θ ^ 2
        - ((r : ℝ) - 1) * ftTauDeriv a r (n - 1) θ ^ 2) / ftTau a r (n - 1) θ := by
    field_simp
  rw [h2, div_lt_iff₀ hτ]
  nlinarith [hbound]

end Assembly

end ForgacsTran
