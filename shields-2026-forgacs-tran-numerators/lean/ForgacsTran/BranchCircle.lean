/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import ForgacsTran.PhaseTangency

/-!
# The quadratic pencil: both branches are circles, and both curvatures are constant

`PhaseTangency.sum_eVariationOn_of_curvature` closes the phase-state binder against one
hypothesis — `wedge (γ'') (γ') ≠ 0`, the signed curvature, which
`wedge_ftGammaDeriv2_ftGammaDeriv` reads at the pencil's branch as `τ² + 2τ'² - ττ''`.
That hypothesis is open at a general pencil.  **At `n = 2` it is not**, for either admissible
index: at `r = 1` the branch is the circle of radius `√(a₀a₁)` centred at the origin, so
`τ' = τ'' = 0` and the curvature is `a₀a₁`; at `r = 2` it is the circle *through* the origin
of diameter the harmonic mean `2a₀a₁/(a₀+a₁)`, so `τ'' = -τ` and the curvature is
`8a₀²a₁²/(a₀+a₁)²`.  Both are constant and positive.

**Two zeros and `r = 1` is a whole two-parameter family, not one pencil.**  `Q(t)/t` is
`c(t - σ + p/t)` with `σ = a₀ + a₁` and `p = a₀a₁`, whose imaginary part on `τe^{iθ}` is
`c sin θ (τ - p/τ)`; it vanishes exactly at `τ² = p`, for every `θ`.  So the whole family is
covered at once, and the witness pencil `τ ≡ 1` is the member with `a₀a₁ = 1`.

**The proof needs no trigonometry beyond one reflection.**  `ftAngle_spec` gives
`a₀ sin θ₀ = τ sin(θ₀ - θ)`, and `τ² = a₀a₁` turns that into `a₁ sin(θ₀ - θ) = τ sin θ₀` —
which is `ftAngle_unique`'s hypothesis at `θ + π - θ₀`.  So `θ₁ = θ + π - θ₀`, the angle sum
is `θ + π`, and `ftTau_eq_of` forces the radius.  The derivatives then vanish because a
function constant on an open interval has derivative zero there, twice.

## Main statements

* `ftAngleSum_sqrt` — the branch equation is solved by `√(a₀a₁)` at every `θ`.
* `ftTau_eq_sqrt` — hence that is the branch radius.
* `ftTauDeriv_eq_zero`, `ftTauDeriv2_eq_zero` — the radius is constant, so both vanish.
* `wedge_ftGammaDeriv2_ftGammaDeriv_quadratic` — the curvature is `a₀a₁`.
* `wedge_ne_zero_quadratic` — `sum_eVariationOn_of_curvature`'s hypothesis, discharged.
* `ftAngleSum_quadRadiusTwo`, `ftTau_eq_quadRadiusTwo`, `ftTauDeriv_quadRadiusTwo`,
  `ftTauDeriv2_quadRadiusTwo` — the same chain at `r = 2`, where the radius is
  `2a₀a₁ cos θ/(a₀+a₁)` rather than constant.
* `wedge_ftGammaDeriv2_ftGammaDeriv_quadTwo`, `wedge_ne_zero_quadTwo` — the curvature there.

## References

* `../shields-2026-forgacs-tran-numerators.tex`, `thm:FT-geometry`.
* `Forgacs2017RationalDenominator`, Lemma 2.
* `../scripts/check_branch_convexity.py`, whose sweep records the constant curvature here.

## Tags

quadratic pencil, branch radius, circle, curvature
-/

namespace ForgacsTran

open Real Set

variable {a : Fin 2 → ℝ}

/-- **The branch equation at `n = 2`, `r = 1` is solved by the constant radius `√(a₀a₁)`.**
The second branch angle is the first one reflected through `(θ + π)/2`. -/
theorem ftAngleSum_sqrt (ha : ∀ k, 0 < a k) {θ : ℝ} (hθ : θ ∈ Ioo 0 π) :
    ftAngleSum a (Real.sqrt (a 0 * a 1)) θ = (1 : ℕ) * θ + (1 : ℕ) * π := by
  have hp : 0 < a 0 * a 1 := mul_pos (ha 0) (ha 1)
  set τ := Real.sqrt (a 0 * a 1) with hτdef
  have hτ : 0 < τ := Real.sqrt_pos.2 hp
  have hτ2 : τ ^ 2 = a 0 * a 1 := Real.sq_sqrt hp.le
  set θ₀ := ftAngle (a 0) τ θ with hθ₀def
  have hmem : θ₀ ∈ Ioo θ π := ftAngle_mem_Ioo (ha 0) hτ hθ
  have hspec : a 0 * Real.sin θ₀ = τ * Real.sin (θ₀ - θ) :=
    ftAngle_spec hτ.ne' hθ
  -- the reflected angle solves the second clause
  have hy : θ + π - θ₀ ∈ Ioo θ π := ⟨by linarith [hmem.2], by linarith [hmem.1]⟩
  have hsin1 : Real.sin (θ + π - θ₀) = Real.sin (θ₀ - θ) := by
    rw [show θ + π - θ₀ = π - (θ₀ - θ) by ring, Real.sin_pi_sub]
  have hsin2 : Real.sin (θ + π - θ₀ - θ) = Real.sin θ₀ := by
    rw [show θ + π - θ₀ - θ = π - θ₀ by ring, Real.sin_pi_sub]
  have hkey : a 1 * Real.sin (θ + π - θ₀) = τ * Real.sin (θ + π - θ₀ - θ) := by
    rw [hsin1, hsin2]
    -- multiply by `τ` and use `τ² = a₀a₁`; no trigonometry left
    refine mul_left_cancel₀ hτ.ne' ?_
    linear_combination (-(a 1)) * hspec + (-(Real.sin θ₀)) * hτ2
  have h2 := ftAngle_unique hτ hθ hy hkey
  rw [ftAngleSum, Fin.sum_univ_two, ← hθ₀def, ← h2]
  push_cast
  ring

/-- **The branch radius of the quadratic pencil at `r = 1`.** -/
theorem ftTau_eq_sqrt (ha : ∀ k, 0 < a k) {θ : ℝ} (hθ : θ ∈ Ioo 0 π) :
    ftTau a 1 1 θ = Real.sqrt (a 0 * a 1) :=
  (ftTau_eq_of (by norm_num) ha hθ (Real.sqrt_pos.2 (mul_pos (ha 0) (ha 1)))
    (ftAngleSum_sqrt ha hθ)).symm

private theorem arc_eq : Ioo (0 : ℝ) (π / (1 : ℕ)) = Ioo 0 π := by
  norm_num

/-- **`τ' = 0`.**  The radius is constant on the arc, and the arc is open. -/
theorem ftTauDeriv_eq_zero (ha : ∀ k, 0 < a k) {θ : ℝ} (hθ : θ ∈ Ioo 0 π) :
    ftTauDeriv a 1 1 θ = 0 := by
  have hb : ∀ s ∈ Ioo (0 : ℝ) (π / (1 : ℕ)), FTBranchAt a 1 1 s := by
    intro s hs
    exact ftBranchAt_of_arc_principal (by norm_num) ha le_rfl (Or.inl (by norm_num)) hs
  have hθ' : θ ∈ Ioo (0 : ℝ) (π / (1 : ℕ)) := by rw [arc_eq]; exact hθ
  have hd := hasDerivAt_ftTau (n := 2) (l := 1) (by norm_num) ha le_rfl hθ' hb
  have heq : ftTau a 1 1 =ᶠ[nhds θ] fun _ => Real.sqrt (a 0 * a 1) := by
    filter_upwards [isOpen_Ioo.mem_nhds hθ] with x hx using ftTau_eq_sqrt ha hx
  have h0 : HasDerivAt (ftTau a 1 1) 0 θ :=
    (hasDerivAt_const θ (Real.sqrt (a 0 * a 1))).congr_of_eventuallyEq heq
  exact hd.unique h0

/-- **`τ'' = 0`**, by the same argument one level up. -/
theorem ftTauDeriv2_eq_zero (ha : ∀ k, 0 < a k) {θ : ℝ} (hθ : θ ∈ Ioo 0 π) :
    ftTauDeriv2 a 1 1 θ = 0 := by
  have hb : ∀ s ∈ Ioo (0 : ℝ) (π / (1 : ℕ)), FTBranchAt a 1 1 s := by
    intro s hs
    exact ftBranchAt_of_arc_principal (by norm_num) ha le_rfl (Or.inl (by norm_num)) hs
  have hθ' : θ ∈ Ioo (0 : ℝ) (π / (1 : ℕ)) := by rw [arc_eq]; exact hθ
  have hd := hasDerivAt_ftTauDeriv (n := 2) (l := 1) (by norm_num) ha le_rfl hθ' hb
  have heq : ftTauDeriv a 1 1 =ᶠ[nhds θ] fun _ => (0 : ℝ) := by
    filter_upwards [isOpen_Ioo.mem_nhds hθ] with x hx using ftTauDeriv_eq_zero ha hx
  have h0 : HasDerivAt (ftTauDeriv a 1 1) 0 θ :=
    (hasDerivAt_const θ (0 : ℝ)).congr_of_eventuallyEq heq
  exact hd.unique h0

/-- **The signed curvature of the quadratic pencil's branch is `a₀a₁`.**  Constant, positive,
and equal to the square of the radius — the circle's own curvature numerator. -/
theorem wedge_ftGammaDeriv2_ftGammaDeriv_quadratic (ha : ∀ k, 0 < a k) {θ : ℝ}
    (hθ : θ ∈ Ioo 0 π) :
    wedge (ftGammaDeriv2 a 1 1 θ) (ftGammaDeriv a 1 1 θ) = a 0 * a 1 := by
  rw [wedge_ftGammaDeriv2_ftGammaDeriv, ftTau_eq_sqrt ha hθ, ftTauDeriv_eq_zero ha hθ,
    ftTauDeriv2_eq_zero ha hθ, Real.sq_sqrt (mul_pos (ha 0) (ha 1)).le]
  ring

/-- **`sum_eVariationOn_of_curvature`'s geometric hypothesis, discharged at `n = 2`, `r = 1`.**
Unconditional in `a₀`, `a₁` — the whole family, not one pencil. -/
theorem wedge_ne_zero_quadratic (ha : ∀ k, 0 < a k) {θ : ℝ} (hθ : θ ∈ Ioo 0 π) :
    wedge (ftGammaDeriv2 a 1 1 θ) (ftGammaDeriv a 1 1 θ) ≠ 0 := by
  rw [wedge_ftGammaDeriv2_ftGammaDeriv_quadratic ha hθ]
  exact (mul_pos (ha 0) (ha 1)).ne'

/-! ### The quadratic pencil at `r = 2`: a circle through the origin

`Q(t)/t²` is `c(1 - σ/t + p/t²)`, whose imaginary part on `τe^{iθ}` is
`c sin θ (σ/τ - 2p cos θ/τ²)`, vanishing exactly at `τ = 2p cos θ/σ`.  That is again a
circle — this one through the origin, of diameter the harmonic mean `2a₀a₁/(a₀+a₁)` — so
`τ'' = -τ` and the curvature is `2τ² + 2τ'² = 8p²/σ²`, constant and positive.

The reflection that carried `r = 1` becomes `θ₁ = 2θ + π - θ₀`, and the step that used
`τ² = a₀a₁` becomes one product-to-sum: `2 cos θ · sin(θ₀ - θ) = sin θ₀ + sin(θ₀ - 2θ)`.
`θ₀ > 2θ`, which the range check needs, falls out of the same identity rather than being
assumed. -/

/-- The radius of the `r = 2` branch. -/
noncomputable def quadRadiusTwo (a : Fin 2 → ℝ) (θ : ℝ) : ℝ :=
  2 * (a 0 * a 1) / (a 0 + a 1) * Real.cos θ

/-- **The branch equation at `n = 2`, `r = 2` is solved by `2a₀a₁cos θ/(a₀+a₁)`.** -/
theorem ftAngleSum_quadRadiusTwo (ha : ∀ k, 0 < a k) {θ : ℝ} (hθ : θ ∈ Ioo 0 (π / 2)) :
    ftAngleSum a (quadRadiusTwo a θ) θ = (2 : ℕ) * θ + (1 : ℕ) * π := by
  have hπ : (0 : ℝ) < π := Real.pi_pos
  have hθπ : θ ∈ Ioo 0 π := ⟨hθ.1, by linarith [hθ.2]⟩
  have hσ : 0 < a 0 + a 1 := by linarith [ha 0, ha 1]
  have hcθ : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1], hθ.2⟩
  set τ := quadRadiusTwo a θ with hτdef
  have hτ : 0 < τ := by
    rw [hτdef, quadRadiusTwo]
    have := ha 0; have := ha 1
    positivity
  have hτval : τ * (a 0 + a 1) = 2 * (a 0 * a 1) * Real.cos θ := by
    rw [hτdef, quadRadiusTwo]
    field_simp
  set θ₀ := ftAngle (a 0) τ θ with hθ₀def
  have hmem : θ₀ ∈ Ioo θ π := ftAngle_mem_Ioo (ha 0) hτ hθπ
  have hspec : a 0 * Real.sin θ₀ = τ * Real.sin (θ₀ - θ) := ftAngle_spec hτ.ne' hθπ
  -- one product-to-sum, and the second clause follows
  have hp2s : Real.sin θ₀ + Real.sin (θ₀ - 2 * θ) = 2 * Real.sin (θ₀ - θ) * Real.cos θ := by
    have h1 := Real.sin_add (θ₀ - θ) θ
    have h2 := Real.sin_sub (θ₀ - θ) θ
    rw [show θ₀ - θ + θ = θ₀ by ring] at h1
    rw [show θ₀ - θ - θ = θ₀ - 2 * θ by ring] at h2
    linarith
  have hkey : a 1 * Real.sin (θ₀ - 2 * θ) = a 0 * Real.sin θ₀ := by
    have h := (ha 0).ne'
    refine mul_left_cancel₀ h ?_
    linear_combination (a 0 * a 1) * hp2s - (a 0 + a 1) * hspec
      - Real.sin (θ₀ - θ) * hτval
  -- the same identity forces `θ₀ > 2θ`
  have hsin0 : 0 < Real.sin θ₀ := Real.sin_pos_of_pos_of_lt_pi (lt_trans hθ.1 hmem.1) hmem.2
  have hsinpos : 0 < Real.sin (θ₀ - 2 * θ) := by
    have h1 : 0 < a 0 * Real.sin θ₀ := mul_pos (ha 0) hsin0
    nlinarith [ha 1, hkey]
  have hgt : 2 * θ < θ₀ := by
    by_contra hcon
    push Not at hcon
    have hle : θ₀ - 2 * θ ≤ 0 := by linarith
    have hge : -(π / 2) < θ₀ - 2 * θ := by linarith [hmem.1, hθ.1, hθ.2]
    have : Real.sin (θ₀ - 2 * θ) ≤ 0 := by
      rcases eq_or_lt_of_le hle with heq | hlt
      · rw [heq]; simp
      · exact (Real.sin_neg_of_neg_of_neg_pi_lt hlt (by linarith [hπ])).le
    linarith
  -- the reflected angle solves the second clause
  have hy : 2 * θ + π - θ₀ ∈ Ioo θ π :=
    ⟨by linarith [hmem.2, hθ.1], by linarith [hgt]⟩
  have hsin1 : Real.sin (2 * θ + π - θ₀) = Real.sin (θ₀ - 2 * θ) := by
    rw [show 2 * θ + π - θ₀ = π - (θ₀ - 2 * θ) by ring, Real.sin_pi_sub]
  have hsin2 : Real.sin (2 * θ + π - θ₀ - θ) = Real.sin (θ₀ - θ) := by
    rw [show 2 * θ + π - θ₀ - θ = π - (θ₀ - θ) by ring, Real.sin_pi_sub]
  have hclause : a 1 * Real.sin (2 * θ + π - θ₀) = τ * Real.sin (2 * θ + π - θ₀ - θ) := by
    rw [hsin1, hsin2, hkey, hspec]
  have h2 := ftAngle_unique hτ hθπ hy hclause
  rw [ftAngleSum, Fin.sum_univ_two, ← hθ₀def, ← h2]
  push_cast
  ring

/-- **The branch radius of the quadratic pencil at `r = 2`.** -/
theorem ftTau_eq_quadRadiusTwo (ha : ∀ k, 0 < a k) {θ : ℝ} (hθ : θ ∈ Ioo 0 (π / 2)) :
    ftTau a 2 1 θ = quadRadiusTwo a θ := by
  have hσ : 0 < a 0 + a 1 := by linarith [ha 0, ha 1]
  have hcθ : 0 < Real.cos θ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
  refine (ftTau_eq_of (by norm_num) ha ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩ ?_
    (ftAngleSum_quadRadiusTwo ha hθ)).symm
  rw [quadRadiusTwo]
  have := ha 0; have := ha 1
  positivity

private theorem arc_eq_two : Ioo (0 : ℝ) (π / (2 : ℕ)) = Ioo 0 (π / 2) := by norm_num

/-- **`τ' = -2a₀a₁ sin θ/(a₀+a₁)`** at the `r = 2` quadratic pencil. -/
theorem ftTauDeriv_quadRadiusTwo (ha : ∀ k, 0 < a k) {θ : ℝ} (hθ : θ ∈ Ioo 0 (π / 2)) :
    ftTauDeriv a 2 1 θ = -(2 * (a 0 * a 1) / (a 0 + a 1) * Real.sin θ) := by
  have hb : ∀ s ∈ Ioo (0 : ℝ) (π / (2 : ℕ)), FTBranchAt a 2 1 s := by
    intro s hs
    exact ftBranchAt_of_arc_principal (by norm_num) ha (by norm_num)
      (Or.inl (by norm_num)) hs
  have hθ' : θ ∈ Ioo (0 : ℝ) (π / (2 : ℕ)) := by rw [arc_eq_two]; exact hθ
  have hd := hasDerivAt_ftTau (n := 2) (l := 1) (by norm_num) ha (by norm_num) hθ' hb
  have heq : ftTau a 2 1 =ᶠ[nhds θ] fun t => 2 * (a 0 * a 1) / (a 0 + a 1) * Real.cos t := by
    filter_upwards [isOpen_Ioo.mem_nhds hθ] with x hx
    rw [ftTau_eq_quadRadiusTwo ha hx, quadRadiusTwo]
  have h0 : HasDerivAt (ftTau a 2 1) (-(2 * (a 0 * a 1) / (a 0 + a 1) * Real.sin θ)) θ := by
    refine ((Real.hasDerivAt_cos θ).const_mul
      (2 * (a 0 * a 1) / (a 0 + a 1))).congr_of_eventuallyEq heq |>.congr_deriv ?_
    ring
  exact hd.unique h0

/-- **`τ'' = -τ`**: the `r = 2` branch is a circle through the origin. -/
theorem ftTauDeriv2_quadRadiusTwo (ha : ∀ k, 0 < a k) {θ : ℝ} (hθ : θ ∈ Ioo 0 (π / 2)) :
    ftTauDeriv2 a 2 1 θ = -(2 * (a 0 * a 1) / (a 0 + a 1) * Real.cos θ) := by
  have hb : ∀ s ∈ Ioo (0 : ℝ) (π / (2 : ℕ)), FTBranchAt a 2 1 s := by
    intro s hs
    exact ftBranchAt_of_arc_principal (by norm_num) ha (by norm_num)
      (Or.inl (by norm_num)) hs
  have hθ' : θ ∈ Ioo (0 : ℝ) (π / (2 : ℕ)) := by rw [arc_eq_two]; exact hθ
  have hd := hasDerivAt_ftTauDeriv (n := 2) (l := 1) (by norm_num) ha (by norm_num) hθ' hb
  have heq : ftTauDeriv a 2 1
      =ᶠ[nhds θ] fun t => -(2 * (a 0 * a 1) / (a 0 + a 1) * Real.sin t) := by
    filter_upwards [isOpen_Ioo.mem_nhds hθ] with x hx
    exact ftTauDeriv_quadRadiusTwo ha hx
  have h0 : HasDerivAt (ftTauDeriv a 2 1)
      (-(2 * (a 0 * a 1) / (a 0 + a 1) * Real.cos θ)) θ := by
    refine (((Real.hasDerivAt_sin θ).const_mul
      (2 * (a 0 * a 1) / (a 0 + a 1))).neg).congr_of_eventuallyEq heq |>.congr_deriv ?_
    ring
  exact hd.unique h0

/-- **The signed curvature of the `r = 2` quadratic branch is `8a₀²a₁²/(a₀+a₁)²`**, twice the
squared diameter of the circle it traces. -/
theorem wedge_ftGammaDeriv2_ftGammaDeriv_quadTwo (ha : ∀ k, 0 < a k) {θ : ℝ}
    (hθ : θ ∈ Ioo 0 (π / 2)) :
    wedge (ftGammaDeriv2 a 2 1 θ) (ftGammaDeriv a 2 1 θ)
      = 2 * (2 * (a 0 * a 1) / (a 0 + a 1)) ^ 2 := by
  have hσ : 0 < a 0 + a 1 := by linarith [ha 0, ha 1]
  rw [wedge_ftGammaDeriv2_ftGammaDeriv, ftTau_eq_quadRadiusTwo ha hθ, quadRadiusTwo,
    ftTauDeriv_quadRadiusTwo ha hθ, ftTauDeriv2_quadRadiusTwo ha hθ]
  have := Real.sin_sq_add_cos_sq θ
  nlinarith [this]

/-- **`sum_eVariationOn_of_curvature`'s hypothesis, discharged at `n = 2`, `r = 2`.** -/
theorem wedge_ne_zero_quadTwo (ha : ∀ k, 0 < a k) {θ : ℝ} (hθ : θ ∈ Ioo 0 (π / 2)) :
    wedge (ftGammaDeriv2 a 2 1 θ) (ftGammaDeriv a 2 1 θ) ≠ 0 := by
  have hσ : 0 < a 0 + a 1 := by linarith [ha 0, ha 1]
  have hp : 0 < a 0 * a 1 := mul_pos (ha 0) (ha 1)
  rw [wedge_ftGammaDeriv2_ftGammaDeriv_quadTwo ha hθ]
  positivity

end ForgacsTran
