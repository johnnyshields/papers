/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import ForgacsTran.FTBranchFunction
import ForgacsTran.FTBranchMonotone
import ForgacsTran.FTBranchValue

/-!
# Regularity of the branch in `θ`

`Forgacs2017RationalDenominator` Lemma 2 asserts that the branch is analytic on a
neighbourhood of `(0, π/r)`.  This module proves it is differentiable there, in
the form the rest of the tree consumes.

## Main statements

* `hasDerivAt_ftTau` — `τ(θ)` is differentiable, with
  `τ'(θ) = -(∂_θ Σ - r)/∂_τ Σ`.
* `hasDerivAt_ftBranchPoint` — the branch point `t₊(θ) = τ(θ) e^{-iθ}` is
  differentiable, with derivative `(τ'(θ) - i τ(θ)) e^{-iθ}`.
* the `_principal` corollaries — the same three at `l = n - 1`, with solvability
  discharged by `ftBranchAt_of_arc_principal`, so they are unconditional facts
  about a pencil with positive zeros.

## Implementation notes

**Analyticity is not formalized.**  `Forgacs2017RationalDenominator` Lemma 2
states the `θ_k` analytic on a neighbourhood of `(0, π/r)`; what is proved here
is differentiability on `(0, π/r)`, which is what every consumer in this tree
uses.  Mathlib carries no implicit function theorem in the analytic category —
`Analysis/Calculus/Implicit.lean` and `ImplicitFunction/{Bivariate,ProdDomain}`
give `HasStrictFDerivAt`, `ImplicitContDiff` gives `ContDiff`, and
`InverseFunctionTheorem/Analytic` is one-variable — so the stronger clause would
have to be built, and nothing here would consume it.

**Differs from the paper's route.**  The paper invokes the complex implicit
function theorem in `n + 1` variables and then continues analytically.  Here the
angle system has already been reduced to the single scalar equation
`Σ(τ, θ) = rθ + lπ`, so only the one-variable statement is needed, and it is
proved directly: the mean value theorem in `τ` converts the equation into
`-(Σ(τ₀, θ) - rθ - lπ) = ∂_τΣ(ξ_θ, θ)·(τ(θ) - τ₀)`, and the slope of `τ` is read
off as `θ → θ₀` using the continuity of `τ` and the joint continuity of `∂_τΣ`.
No Fréchet derivative and no implicit function theorem is used.

Sorry-free.

## References

Formalizes `Forgacs2017RationalDenominator` Lemmas 2--5, the branch
`thm:FT-geometry` imports.

## Tags

regularity, continuity, branch radius
-/

namespace ForgacsTran

open Real Set Filter Topology

/-- `τ'(θ) = -(∂_θΣ - r)/∂_τΣ`, the quotient of partials the branch equation
delivers. -/
noncomputable def ftTauDeriv {n : ℕ} (a : Fin n → ℝ) (r l : ℕ) (θ : ℝ) : ℝ :=
  -(ftAngleSumDerivAngle a (ftTau a r l θ) θ - r) / ftAngleSumDerivTau a (ftTau a r l θ) θ

/-- **`τ(θ)` is differentiable on the viewing arc.** -/
theorem hasDerivAt_ftTau {n r l : ℕ} {a : Fin n → ℝ} (hn : 0 < n) (ha : ∀ k, 0 < a k)
    (hr : 1 ≤ r) {θ₀ : ℝ} (hθ₀ : θ₀ ∈ Ioo 0 (π / r))
    (hb : ∀ θ ∈ Ioo 0 (π / r), FTBranchAt a r l θ) :
    HasDerivAt (ftTau a r l) (ftTauDeriv a r l θ₀) θ₀ := by
  rw [ftTauDeriv]
  set T := ftTau a r l with hTdef
  set τ₀ := T θ₀ with hτ₀def
  have hθ₀π : θ₀ ∈ Ioo 0 π := ftArc_subset hr hθ₀
  have hτ₀ : 0 < τ₀ := ftTau_pos (hb θ₀ hθ₀)
  have hDt₀ : ftAngleSumDerivTau a τ₀ θ₀ < 0 := ftAngleSumDerivTau_neg hn ha hτ₀ hθ₀π
  set Fθ : ℝ → ℝ := fun s => ftAngleSum a τ₀ s - ((r : ℝ) * s + l * π) with hFθdef
  have hFθ₀ : Fθ θ₀ = 0 := by
    change ftAngleSum a τ₀ θ₀ - ((r : ℝ) * θ₀ + l * π) = 0
    rw [ftAngleSum_ftTau (hb θ₀ hθ₀)]
    ring
  have hFθderiv : HasDerivAt Fθ (ftAngleSumDerivAngle a τ₀ θ₀ - r) θ₀ := by
    have h1 := hasDerivAt_ftAngleSum_angle ha hτ₀ hθ₀π
    have h2 : HasDerivAt (fun s : ℝ => (r : ℝ) * s + (l : ℝ) * π) ((r : ℝ)) θ₀ := by
      simpa using ((hasDerivAt_id θ₀).const_mul ((r : ℝ))).add_const ((l : ℝ) * π)
    exact h1.sub h2
  have hTcont : ContinuousAt T θ₀ := continuousAt_ftTau hn ha hr hθ₀ hb
  -- the mean value theorem in `τ`, at every angle of the arc
  have hmvt : ∀ θ : ℝ, ∃ ξ : ℝ, θ ∈ Ioo 0 (π / r) →
      (ξ ∈ uIcc τ₀ (T θ) ∧ -(Fθ θ) = ftAngleSumDerivTau a ξ θ * (T θ - τ₀)) := by
    intro θ
    by_cases hθ : θ ∈ Ioo 0 (π / r)
    · have hθπ : θ ∈ Ioo 0 π := ftArc_subset hr hθ
      have hTθ : 0 < T θ := ftTau_pos (hb θ hθ)
      have hd : ∀ u ∈ uIcc τ₀ (T θ),
          HasDerivAt (fun v => ftAngleSum a v θ - ((r : ℝ) * θ + (l : ℝ) * π))
            (ftAngleSumDerivTau a u θ) u := by
        intro u hu
        have hu0 : 0 < u := by
          rcases Set.mem_uIcc.1 hu with ⟨h1, _⟩ | ⟨h1, _⟩
          · exact lt_of_lt_of_le hτ₀ h1
          · exact lt_of_lt_of_le hTθ h1
        exact (hasDerivAt_ftAngleSum_tau ha hu0 hθπ).sub_const _
      obtain ⟨ξ, hξ1, hξ2⟩ :=
        exists_hasDerivAt_eq_sub_uIcc _ (fun v => ftAngleSumDerivTau a v θ) hd
      refine ⟨ξ, fun _ => ⟨hξ1, ?_⟩⟩
      rw [ftAngleSum_ftTau (hb θ hθ)] at hξ2
      change -(ftAngleSum a τ₀ θ - ((r : ℝ) * θ + (l : ℝ) * π)) = _
      linarith [hξ2]
    · exact ⟨τ₀, fun h => absurd h hθ⟩
  choose ξ hξ using hmvt
  have huicc : ∀ {x y z : ℝ}, z ∈ uIcc x y → min x y ≤ z ∧ z ≤ max x y := by
    intro x y z hz
    rcases Set.mem_uIcc.1 hz with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨le_trans (min_le_left _ _) h1, le_trans h2 (le_max_right _ _)⟩
    · exact ⟨le_trans (min_le_right _ _) h1, le_trans h2 (le_max_left _ _)⟩
  have harc : ∀ᶠ θ in 𝓝[≠] θ₀, θ ∈ Ioo 0 (π / r) :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds (isOpen_Ioo.mem_nhds hθ₀)
  have hTtend : Tendsto T (𝓝[≠] θ₀) (𝓝 τ₀) :=
    hTcont.tendsto.mono_left nhdsWithin_le_nhds
  have hξtend : Tendsto ξ (𝓝[≠] θ₀) (𝓝 τ₀) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
      (g := fun θ => min τ₀ (T θ)) (h := fun θ => max τ₀ (T θ)) ?_ ?_ ?_ ?_
    · simpa [min_self] using (tendsto_const_nhds (x := τ₀)).min hTtend
    · simpa [max_self] using (tendsto_const_nhds (x := τ₀)).max hTtend
    · filter_upwards [harc] with θ hθ using (huicc (hξ θ hθ).1).1
    · filter_upwards [harc] with θ hθ using (huicc (hξ θ hθ).1).2
  have hDtcont : ContinuousAt (fun p : ℝ × ℝ => ftAngleSumDerivTau a p.1 p.2) (τ₀, θ₀) :=
    (continuousOn_ftAngleSumDerivTau a).continuousAt
      ((isOpen_Ioi.prod isOpen_Ioo).mem_nhds ⟨hτ₀, hθ₀π⟩)
  have hprod : Tendsto (fun θ : ℝ => (ξ θ, θ)) (𝓝[≠] θ₀) (𝓝 (τ₀, θ₀)) := by
    refine Filter.Tendsto.prodMk_nhds hξtend ?_
    exact (tendsto_id : Tendsto id (𝓝 θ₀) (𝓝 θ₀)).mono_left nhdsWithin_le_nhds
  -- stated on the composition and beta-reduced afterwards: unifying the two forms
  -- directly sends the elaborator down a `whnf` path that does not terminate in
  -- any reasonable budget
  have hDttend : Tendsto ((fun p : ℝ × ℝ => ftAngleSumDerivTau a p.1 p.2) ∘ (fun θ : ℝ => (ξ θ, θ)))
      (𝓝[≠] θ₀) (𝓝 (ftAngleSumDerivTau a τ₀ θ₀)) := hDtcont.tendsto.comp hprod
  simp only [Function.comp_def] at hDttend
  have hne : ∀ᶠ θ in 𝓝[≠] θ₀, ftAngleSumDerivTau a (ξ θ) θ ≠ 0 := by
    filter_upwards [hDttend.eventually (eventually_lt_nhds hDt₀)] with θ h using ne_of_lt h
  have heq : ∀ᶠ θ in 𝓝[≠] θ₀,
      -(slope Fθ θ₀ θ) / ftAngleSumDerivTau a (ξ θ) θ = slope T θ₀ θ := by
    filter_upwards [harc, hne, self_mem_nhdsWithin] with θ hθ hne' hθne
    have hd := (hξ θ hθ).2
    have hsub : θ - θ₀ ≠ 0 := sub_ne_zero.2 hθne
    rw [slope_def_field, slope_def_field, hFθ₀, sub_zero]
    field_simp
    linarith [hd]
  rw [hasDerivAt_iff_tendsto_slope]
  refine Tendsto.congr' heq ?_
  exact (hFθderiv.tendsto_slope.neg).div hDttend (ne_of_lt hDt₀)

/-- The branch point `t₊(θ) = τ(θ) e^{-iθ}` of `thm:FT-geometry`. -/
noncomputable def ftBranchPoint {n : ℕ} (a : Fin n → ℝ) (r l : ℕ) (θ : ℝ) : ℂ :=
  ftArcPoint (ftTau a r l θ) θ

/-- **The branch point is differentiable on the viewing arc**, with
`t₊'(θ) = (τ'(θ) - i τ(θ)) e^{-iθ}`.  This is the hypothesis the endpoint and
dominance statements carry. -/
theorem hasDerivAt_ftBranchPoint {n r l : ℕ} {a : Fin n → ℝ} (hn : 0 < n) (ha : ∀ k, 0 < a k)
    (hr : 1 ≤ r) {θ₀ : ℝ} (hθ₀ : θ₀ ∈ Ioo 0 (π / r))
    (hb : ∀ θ ∈ Ioo 0 (π / r), FTBranchAt a r l θ) :
    HasDerivAt (ftBranchPoint a r l)
      (((ftTauDeriv a r l θ₀ : ℂ) - (ftTau a r l θ₀ : ℂ) * Complex.I)
        * Complex.exp (-(θ₀ : ℂ) * Complex.I)) θ₀ := by
  have h1 : HasDerivAt (fun θ : ℝ => ((ftTau a r l θ : ℝ) : ℂ))
      ((ftTauDeriv a r l θ₀ : ℝ) : ℂ) θ₀ :=
    (hasDerivAt_ftTau hn ha hr hθ₀ hb).ofReal_comp
  have h0 : HasDerivAt (fun θ : ℝ => ((θ : ℝ) : ℂ)) 1 θ₀ := by
    simpa using (hasDerivAt_id θ₀).ofReal_comp
  have h2 : HasDerivAt (fun θ : ℝ => -((θ : ℝ) : ℂ) * Complex.I) (-Complex.I) θ₀ := by
    simpa using h0.neg.mul_const Complex.I
  have h3 : HasDerivAt (fun θ : ℝ => Complex.exp (-((θ : ℝ) : ℂ) * Complex.I))
      (Complex.exp (-(θ₀ : ℂ) * Complex.I) * -Complex.I) θ₀ := h2.cexp
  refine (h1.mul h3).congr_deriv ?_
  ring

/-- **The branch angles are differentiable**, with the chain rule in the form the
two partials give it: `dθ_k/dθ = (∂θ_k/∂τ)·τ'(θ) + ∂θ_k/∂θ`. -/
theorem hasDerivAt_ftBranchAngle {n r l : ℕ} {a : Fin n → ℝ} (hn : 0 < n) (ha : ∀ k, 0 < a k)
    (hr : 1 ≤ r) {θ₀ : ℝ} (hθ₀ : θ₀ ∈ Ioo 0 (π / r))
    (hb : ∀ θ ∈ Ioo 0 (π / r), FTBranchAt a r l θ) (k : Fin n) :
    HasDerivAt (ftBranchAngle a r l k)
      (-(Real.sin (ftBranchAngle a r l k θ₀) ^ 2 * a k
            / (ftTau a r l θ₀ ^ 2 * Real.sin θ₀)) * ftTauDeriv a r l θ₀
        + Real.sin (ftBranchAngle a r l k θ₀)
            * Real.cos (ftBranchAngle a r l k θ₀ - θ₀) / Real.sin θ₀) θ₀ := by
  have hθ₀π : θ₀ ∈ Ioo 0 π := ftArc_subset hr hθ₀
  have hsin : 0 < Real.sin θ₀ := sin_pos_of_pos_of_lt_pi hθ₀π.1 hθ₀π.2
  have hsin' : Real.sin θ₀ ≠ 0 := hsin.ne'
  have hτ₀ : 0 < ftTau a r l θ₀ := ftTau_pos (hb θ₀ hθ₀)
  have hτ₀' : ftTau a r l θ₀ ≠ 0 := hτ₀.ne'
  have hymem : ftBranchAngle a r l k θ₀ ∈ Ioo θ₀ π := ftAngle_mem_Ioo (ha k) hτ₀ hθ₀π
  have hsy : 0 < Real.sin (ftBranchAngle a r l k θ₀) :=
    sin_pos_of_pos_of_lt_pi (lt_trans hθ₀π.1 hymem.1) hymem.2
  have hspec : a k * Real.sin (ftBranchAngle a r l k θ₀)
      = ftTau a r l θ₀ * Real.sin (ftBranchAngle a r l k θ₀ - θ₀) :=
    ftAngle_spec hτ₀' hθ₀π
  have hkey : Real.sin (ftBranchAngle a r l k θ₀) * (ftTau a r l θ₀ - a k * Real.cos θ₀)
      = ftTau a r l θ₀ * Real.sin θ₀ * Real.cos (ftBranchAngle a r l k θ₀ - θ₀) := by
    rw [Real.cos_sub]
    rw [Real.sin_sub] at hspec
    linear_combination (-Real.cos θ₀) * hspec
      + (-(ftTau a r l θ₀ * Real.sin (ftBranchAngle a r l k θ₀)))
        * (Real.sin_sq_add_cos_sq θ₀)
  have hgs : Real.cos (ftBranchAngle a r l k θ₀)
      = (Real.cos θ₀ / Real.sin θ₀ - a k / (ftTau a r l θ₀ * Real.sin θ₀))
        * Real.sin (ftBranchAngle a r l k θ₀) := cos_ftArccot _
  have hone : 1 + (Real.cos θ₀ / Real.sin θ₀ - a k / (ftTau a r l θ₀ * Real.sin θ₀)) ^ 2
      = 1 / Real.sin (ftBranchAngle a r l k θ₀) ^ 2 := by
    have hval : Real.cos θ₀ / Real.sin θ₀ - a k / (ftTau a r l θ₀ * Real.sin θ₀)
        = Real.cos (ftBranchAngle a r l k θ₀) / Real.sin (ftBranchAngle a r l k θ₀) := by
      rw [eq_div_iff hsy.ne']
      exact hgs.symm
    rw [hval]
    field_simp
    linear_combination (Real.sin_sq_add_cos_sq (ftBranchAngle a r l k θ₀))
  have hT := hasDerivAt_ftTau hn ha hr hθ₀ hb
  have hcs : HasDerivAt (fun θ : ℝ => Real.cos θ / Real.sin θ)
      ((-Real.sin θ₀ * Real.sin θ₀ - Real.cos θ₀ * Real.cos θ₀) / Real.sin θ₀ ^ 2) θ₀ :=
    (Real.hasDerivAt_cos θ₀).div (Real.hasDerivAt_sin θ₀) hsin'
  have hTs : HasDerivAt (fun θ : ℝ => ftTau a r l θ * Real.sin θ)
      (ftTauDeriv a r l θ₀ * Real.sin θ₀ + ftTau a r l θ₀ * Real.cos θ₀) θ₀ :=
    hT.mul (Real.hasDerivAt_sin θ₀)
  have hden : ftTau a r l θ₀ * Real.sin θ₀ ≠ 0 := mul_ne_zero hτ₀' hsin'
  have hq : HasDerivAt (fun θ : ℝ => a k / (ftTau a r l θ * Real.sin θ))
      ((0 * (ftTau a r l θ₀ * Real.sin θ₀)
        - a k * (ftTauDeriv a r l θ₀ * Real.sin θ₀ + ftTau a r l θ₀ * Real.cos θ₀))
        / (ftTau a r l θ₀ * Real.sin θ₀) ^ 2) θ₀ :=
    (hasDerivAt_const θ₀ (a k)).div hTs hden
  have hH : HasDerivAt (fun θ : ℝ => Real.cos θ / Real.sin θ - a k / (ftTau a r l θ * Real.sin θ))
      ((-Real.sin θ₀ * Real.sin θ₀ - Real.cos θ₀ * Real.cos θ₀) / Real.sin θ₀ ^ 2
        - (0 * (ftTau a r l θ₀ * Real.sin θ₀)
          - a k * (ftTauDeriv a r l θ₀ * Real.sin θ₀ + ftTau a r l θ₀ * Real.cos θ₀))
          / (ftTau a r l θ₀ * Real.sin θ₀) ^ 2) θ₀ := hcs.fun_sub hq
  have hcomp := (hasDerivAt_ftArccot
    (Real.cos θ₀ / Real.sin θ₀ - a k / (ftTau a r l θ₀ * Real.sin θ₀))).comp θ₀ hH
  have hfun : (ftArccot ∘ fun θ : ℝ =>
      Real.cos θ / Real.sin θ - a k / (ftTau a r l θ * Real.sin θ))
      = ftBranchAngle a r l k := rfl
  rw [hfun] at hcomp
  refine hcomp.congr_deriv ?_
  have hA : (-Real.sin θ₀ * Real.sin θ₀ - Real.cos θ₀ * Real.cos θ₀) / Real.sin θ₀ ^ 2
      = -(1 / Real.sin θ₀ ^ 2) := by
    field_simp
    linear_combination -(Real.sin_sq_add_cos_sq θ₀)
  have hB : (0 * (ftTau a r l θ₀ * Real.sin θ₀)
        - a k * (ftTauDeriv a r l θ₀ * Real.sin θ₀ + ftTau a r l θ₀ * Real.cos θ₀))
        / (ftTau a r l θ₀ * Real.sin θ₀) ^ 2
      = -(a k * (ftTauDeriv a r l θ₀ * Real.sin θ₀ + ftTau a r l θ₀ * Real.cos θ₀)
          / (ftTau a r l θ₀ ^ 2 * Real.sin θ₀ ^ 2)) := by
    field
  rw [hone, hA, hB, one_div_one_div]
  field_simp
  linear_combination (ftTau a r l θ₀) * hkey

/-- `τ` is differentiable across the whole viewing arc. -/
theorem differentiableOn_ftTau {n r l : ℕ} {a : Fin n → ℝ} (hn : 0 < n) (ha : ∀ k, 0 < a k)
    (hr : 1 ≤ r) (hb : ∀ θ ∈ Ioo 0 (π / r), FTBranchAt a r l θ) :
    DifferentiableOn ℝ (ftTau a r l) (Ioo 0 (π / r)) := fun _θ hθ =>
  ((hasDerivAt_ftTau hn ha hr hθ hb).differentiableAt).differentiableWithinAt

/-- **`Forgacs2017RationalDenominator` Lemma 3, read off the derivative.**  The
two partials have the same sign, so `τ'(θ) < 0`.  This is the
same content as `ftTau_strictAnti`, now available pointwise. -/
theorem ftTauDeriv_neg {n r l : ℕ} {a : Fin n → ℝ} (hn : 0 < n) (ha : ∀ k, 0 < a k)
    (hr : 1 ≤ r) (hne : ¬(r = 1 ∧ n = 2)) (hl : l = n - 1)
    {θ₀ : ℝ} (hθ₀ : θ₀ ∈ Ioo 0 (π / r)) (hb : FTBranchAt a r l θ₀) :
    ftTauDeriv a r l θ₀ < 0 := by
  have hθ₀π : θ₀ ∈ Ioo 0 π := ftArc_subset hr hθ₀
  have hτ₀ : 0 < ftTau a r l θ₀ := ftTau_pos hb
  have hDt : ftAngleSumDerivTau a (ftTau a r l θ₀) θ₀ < 0 :=
    ftAngleSumDerivTau_neg hn ha hτ₀ hθ₀π
  have hbr : ftAngleSum a (ftTau a r l θ₀) θ₀ = r * θ₀ + ((n - 1 : ℕ) : ℝ) * π := by
    rw [ftAngleSum_ftTau hb, hl]
  have hDa : ftAngleSumDerivAngle a (ftTau a r l θ₀) θ₀ - r < 0 :=
    deriv_ftAngleSum_sub_neg hn ha hr hne hτ₀ hθ₀.1 hθ₀.2 hbr
  rw [ftTauDeriv]
  exact div_neg_of_pos_of_neg (by linarith) hDt

/-! ### The principal branch, `l = n - 1`

At the index `Forgacs2017RationalDenominator` Remark 4 selects, solvability holds
across the whole arc, so the statements above lose their last hypothesis. -/

theorem continuousAt_ftTau_principal {n r : ℕ} {a : Fin n → ℝ} (hn : 0 < n) (ha : ∀ k, 0 < a k)
    (hr : 1 ≤ r) (hnr : 2 ≤ n ∨ 2 ≤ r) {θ₀ : ℝ} (hθ₀ : θ₀ ∈ Ioo 0 (π / r)) :
    ContinuousAt (ftTau a r (n - 1)) θ₀ :=
  continuousAt_ftTau hn ha hr hθ₀ fun _θ hθ => ftBranchAt_of_arc_principal hn ha hr hnr hθ

/-- **`τ(θ)` is differentiable on the viewing arc**, with no hypothesis beyond a
pencil with positive zeros. -/
theorem hasDerivAt_ftTau_principal {n r : ℕ} {a : Fin n → ℝ} (hn : 0 < n) (ha : ∀ k, 0 < a k)
    (hr : 1 ≤ r) (hnr : 2 ≤ n ∨ 2 ≤ r) {θ₀ : ℝ} (hθ₀ : θ₀ ∈ Ioo 0 (π / r)) :
    HasDerivAt (ftTau a r (n - 1)) (ftTauDeriv a r (n - 1) θ₀) θ₀ :=
  hasDerivAt_ftTau hn ha hr hθ₀ fun _θ hθ => ftBranchAt_of_arc_principal hn ha hr hnr hθ

theorem differentiableOn_ftTau_principal {n r : ℕ} {a : Fin n → ℝ} (hn : 0 < n)
    (ha : ∀ k, 0 < a k) (hr : 1 ≤ r) (hnr : 2 ≤ n ∨ 2 ≤ r) :
    DifferentiableOn ℝ (ftTau a r (n - 1)) (Ioo 0 (π / r)) :=
  differentiableOn_ftTau hn ha hr fun _θ hθ => ftBranchAt_of_arc_principal hn ha hr hnr hθ

/-- **The branch point is differentiable on the viewing arc**, with no hypothesis
beyond a pencil with positive zeros.  This is the form the endpoint and
dominance statements consume. -/
theorem hasDerivAt_ftBranchPoint_principal {n r : ℕ} {a : Fin n → ℝ} (hn : 0 < n)
    (ha : ∀ k, 0 < a k) (hr : 1 ≤ r) (hnr : 2 ≤ n ∨ 2 ≤ r) {θ₀ : ℝ}
    (hθ₀ : θ₀ ∈ Ioo 0 (π / r)) :
    HasDerivAt (ftBranchPoint a r (n - 1))
      (((ftTauDeriv a r (n - 1) θ₀ : ℂ) - (ftTau a r (n - 1) θ₀ : ℂ) * Complex.I)
        * Complex.exp (-(θ₀ : ℂ) * Complex.I)) θ₀ :=
  hasDerivAt_ftBranchPoint hn ha hr hθ₀ fun _θ hθ => ftBranchAt_of_arc_principal hn ha hr hnr hθ

/-- **The branch angles are differentiable on the viewing arc**, with no
hypothesis beyond a pencil with positive zeros. -/
theorem hasDerivAt_ftBranchAngle_principal {n r : ℕ} {a : Fin n → ℝ} (hn : 0 < n)
    (ha : ∀ k, 0 < a k) (hr : 1 ≤ r) (hnr : 2 ≤ n ∨ 2 ≤ r) {θ₀ : ℝ}
    (hθ₀ : θ₀ ∈ Ioo 0 (π / r)) (k : Fin n) :
    HasDerivAt (ftBranchAngle a r (n - 1) k)
      (-(Real.sin (ftBranchAngle a r (n - 1) k θ₀) ^ 2 * a k
            / (ftTau a r (n - 1) θ₀ ^ 2 * Real.sin θ₀)) * ftTauDeriv a r (n - 1) θ₀
        + Real.sin (ftBranchAngle a r (n - 1) k θ₀)
            * Real.cos (ftBranchAngle a r (n - 1) k θ₀ - θ₀) / Real.sin θ₀) θ₀ :=
  hasDerivAt_ftBranchAngle hn ha hr hθ₀
    (fun _θ hθ => ftBranchAt_of_arc_principal hn ha hr hnr hθ) k

/-- `τ'(θ) < 0` on the whole arc. -/
theorem ftTauDeriv_neg_principal {n r : ℕ} {a : Fin n → ℝ} (hn : 0 < n) (ha : ∀ k, 0 < a k)
    (hr : 1 ≤ r) (hne : ¬(r = 1 ∧ n = 2)) (hnr : 2 ≤ n ∨ 2 ≤ r)
    {θ₀ : ℝ} (hθ₀ : θ₀ ∈ Ioo 0 (π / r)) :
    ftTauDeriv a r (n - 1) θ₀ < 0 :=
  ftTauDeriv_neg hn ha hr hne rfl hθ₀ (ftBranchAt_of_arc_principal hn ha hr hnr hθ₀)

end ForgacsTran
