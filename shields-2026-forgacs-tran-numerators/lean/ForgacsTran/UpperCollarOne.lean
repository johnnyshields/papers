/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import ForgacsTran.CollisionCollarLeft
import ForgacsTran.PhaseSupplyLowerCollar
import ForgacsTran.UpperEndpointSlope
import ForgacsTran.FTBranchEndpointUpper
import ForgacsTran.PhaseSupplyRegionBounds

/-!
# `κ₀`'s outer region at the `r = 1` upper endpoint

`PhaseSupplyUpperRegion` produces the bound at `π/r` for `2 ≤ r`, where the branch runs into
the **origin** and `E(0) = -rQ(0) ≠ 0`, so the ordinary estimate through `‖E'(γ)‖/‖E(γ)‖`
has a denominator.  At `r = 1` the arc ends at `π`, the branch runs into `-L` where `E`
vanishes, and that estimate has nothing to divide by.

What applies instead is the collision collar, anchored at the far end of the arc:
`CollisionCollarLeft.exists_bound_im_logDeriv_ftCofactorAlong_at_collision_left`.  Its
endpoint binders are exactly the two facts `UpperEndpointRadius` and `UpperEndpointSlope`
produce — the branch enters at `-iL`, and its derivative is Lipschitz there because the
radius reaches `L` quadratically and its slope vanishes linearly.

**The radius is carried at `ftTauArcAt … L`, not at `ftTauArc`.**  The two agree strictly
below `π` and differ **at** `π`, where `ftTauArc` returns `0` — the convention that is right
only when the branch runs into the origin.  Every hypothesis on the collar is transported
between them by that agreement, and the endpoint binders are stated at the radius that
carries the value the branch actually has.

Sorry-free.

## Main statements

* `ftGammaDerivPi` — `γ'` with the endpoint's value supplied, as `ftGammaDerivAt` does at the
  other end.
* `ft_upper_endpoint_branch_data_one` — the collar's endpoint binders at `r = 1`.
* `ft_upper_region_one` — the bound on `Ioo b₂ π`, with nothing assumed.

## References

Formalizes `../../shields-2026-forgacs-tran-numerators.tex`, `sec:geometry`,
`eq:Dprime-identity`, `cor:linear-phase-variation`.

## Tags

upper endpoint, collar, collision, bounded variation, Forgács–Tran
-/

namespace ForgacsTran

open Polynomial Set Real Filter Topology

variable {n : ℕ} {a : Fin n → ℝ} {c x₁ : ℝ}

/-- The two arc radii agree strictly below `π/r`; they differ only in the value they carry
past it, which is `0` for `ftTauArc` and the branch's own endpoint for `ftTauArcAt`. -/
theorem ftTauArcAt_eq_ftTauArc_of_lt (a : Fin n → ℝ) (r l : ℕ) (x₁ aEnd : ℝ) {θ : ℝ}
    (hθ : θ < π / r) : ftTauArcAt a r l x₁ aEnd θ = ftTauArc a r l x₁ θ := by
  rw [ftTauArcAt_eq_lower a r l x₁ aEnd hθ, ftTauArc_eq_lower a r l x₁ hθ]

open scoped Classical in
/-- **`γ'` with the `r = 1` upper endpoint's value supplied.**  `ftGammaDeriv` at `π` is the
branch equation's junk — `FTBranchAt` fails there — exactly as it is at the collision at the
other end, so the value comes in as a parameter and `BranchSupplyGeometry.ftGammaDerivAt` is
this at `0`. -/
noncomputable def ftGammaDerivPi (a : Fin n → ℝ) (l : ℕ) (v : ℂ) : ℝ → ℂ :=
  Function.update (ftGammaDeriv a 1 l) π v

open scoped Classical in
@[simp] theorem ftGammaDerivPi_pi (a : Fin n → ℝ) (l : ℕ) (v : ℂ) :
    ftGammaDerivPi a l v π = v := by simp [ftGammaDerivPi]

open scoped Classical in
theorem ftGammaDerivPi_of_ne (a : Fin n → ℝ) (l : ℕ) (v : ℂ) {θ : ℝ} (hθ : θ ≠ π) :
    ftGammaDerivPi a l v θ = ftGammaDeriv a 1 l θ := by simp [ftGammaDerivPi, hθ]

/-- **The collar's endpoint binders at the `r = 1` upper endpoint.**  The one-sided
derivative and its nonvanishing come from the quadratic rate, the derivative on the
punctured collar from the geometry group, and the Lipschitz bound from the slope bound: the
radius reaches `L` quadratically and its slope vanishes linearly, so the whole deviation of
`γ'` is linear in `π - θ`.

This is the mirror of `PhaseSupplyLowerCollar.ft_endpoint_branch_data`, and the two are not
the same argument — there the value is pinned by identifying a cluster expansion with a
limit of `γ'`, here by the reduced equation's evenness. -/
theorem ft_upper_endpoint_branch_data_one {L : ℝ}
    (hn2 : 2 ≤ n) (ha : ∀ k, 0 < a k) (hc : 0 < c) (hL : 0 < L)
    (hLe : (ftCriticalReal (ftRootPolyReal c a) 1).eval (-L) = 0)
    (hlim : Tendsto (ftTau a 1 (n - 1)) (𝓝[<] π) (𝓝 L)) :
    ∃ Lip b : ℝ, 0 < b ∧ b < π ∧ 0 ≤ Lip ∧
      HasDerivWithinAt (ftPrincipal (ftTauArcAt a 1 (n - 1) x₁ L))
        (ftGammaDerivPi a (n - 1) (-(((L : ℝ) : ℂ) * Complex.I)) π) (Iic π) π ∧
      (∀ θ ∈ Ico (π - b) π, HasDerivAt (ftPrincipal (ftTauArcAt a 1 (n - 1) x₁ L))
        (ftGammaDerivPi a (n - 1) (-(((L : ℝ) : ℂ) * Complex.I)) θ) θ) ∧
      (∀ θ ∈ Icc (π - b) π,
        ‖ftGammaDerivPi a (n - 1) (-(((L : ℝ) : ℂ) * Complex.I)) θ
          - ftGammaDerivPi a (n - 1) (-(((L : ℝ) : ℂ) * Complex.I)) π‖ ≤ Lip * (π - θ)) := by
  have hn : 0 < n := by omega
  have hπ := Real.pi_pos
  have hpi : π / ((1 : ℕ) : ℝ) = π := pi_div_natCast_one
  set v : ℂ := -(((L : ℝ) : ℂ) * Complex.I) with hv
  obtain ⟨K, δ₁, hδ₁, hquad⟩ :=
    exists_quadratic_bound_ftTau_upper (c := c) hn2 ha hc hL hLe hlim
  obtain ⟨M, δ₂, hδ₂, hslope⟩ := exists_linear_bound_ftTauDeriv_upper (c := c) hn2 ha hc hL hlim
  set b : ℝ := min (min δ₁ δ₂ / 2) (π / 2) with hb
  have hb0 : 0 < b := lt_min (by positivity) (by positivity)
  have hbπ : b < π := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hbδ₁ : b < δ₁ := lt_of_le_of_lt (min_le_left _ _) (by
    have := min_le_left δ₁ δ₂; linarith)
  have hbδ₂ : b < δ₂ := lt_of_le_of_lt (min_le_left _ _) (by
    have := min_le_right δ₁ δ₂; linarith)
  have hbhalf : b ≤ π / 2 := min_le_right _ _
  -- the one-sided derivative
  have hd0 : HasDerivWithinAt (ftPrincipal (ftTauArcAt a 1 (n - 1) x₁ L)) v (Iic π) π :=
    hasDerivWithinAt_ftPrincipal_ftTauArcAt_pi hn2 ha hc hL hLe hlim
  -- the derivative on the punctured collar
  have hd : ∀ θ ∈ Ico (π - b) π,
      HasDerivAt (ftPrincipal (ftTauArcAt a 1 (n - 1) x₁ L)) (ftGammaDerivPi a (n - 1) v θ) θ := by
    intro θ hθ
    have hθ0 : 0 < θ := by
      have h1 : (0 : ℝ) < π - b := by linarith
      linarith [hθ.1]
    rw [ftGammaDerivPi_of_ne a (n - 1) v (ne_of_lt hθ.2)]
    exact hasDerivAt_ftPrincipal_ftTauArcAt hn ha le_rfl (Or.inl hn2) x₁ L
      (by rw [hpi]; exact ⟨hθ0, hθ.2⟩)
  -- the Lipschitz bound
  refine ⟨|M| + |K| * π + 2 * L, b, hb0, hbπ, by positivity,
    (by rw [ftGammaDerivPi_pi]; exact hd0), hd, fun θ hθ => ?_⟩
  rcases eq_or_lt_of_le hθ.2 with rfl | hlt
  · simp
  have hθ0 : 0 < θ := by
    have h1 : (0:ℝ) < π - b := by linarith
    linarith [hθ.1]
  have hmem : θ ∈ Ioo (π - δ₁) π := ⟨by linarith [hθ.1], hlt⟩
  have hmem2 : θ ∈ Ioo (π - δ₂) π := ⟨by linarith [hθ.1], hlt⟩
  have hq := hquad θ hmem
  have hs := hslope θ hmem2
  have hexp : Complex.exp ((π : ℂ) * Complex.I) = -1 := Complex.exp_pi_mul_I
  have hdecomp : ftGammaDerivPi a (n - 1) v θ - ftGammaDerivPi a (n - 1) v π
      = Complex.exp ((θ : ℂ) * Complex.I) * ((ftTauDeriv a 1 (n - 1) θ : ℝ) : ℂ)
        + Complex.I * (Complex.exp ((θ : ℂ) * Complex.I)
            * ((ftTau a 1 (n - 1) θ - L : ℝ) : ℂ))
        + Complex.I * (((L : ℝ) : ℂ) * (Complex.exp ((θ : ℂ) * Complex.I)
            - Complex.exp ((π : ℂ) * Complex.I))) := by
    rw [ftGammaDerivPi_of_ne a (n - 1) v (ne_of_lt hlt), ftGammaDerivPi_pi, hv,
      ftGammaDeriv, hexp]
    push_cast
    ring
  rw [hdecomp]
  have he1 : ‖Complex.exp ((θ : ℂ) * Complex.I)‖ = 1 := Complex.norm_exp_ofReal_mul_I θ
  have hstep : ‖Complex.exp ((θ : ℂ) * Complex.I) * ((ftTauDeriv a 1 (n - 1) θ : ℝ) : ℂ)
        + Complex.I * (Complex.exp ((θ : ℂ) * Complex.I)
            * ((ftTau a 1 (n - 1) θ - L : ℝ) : ℂ))
        + Complex.I * (((L : ℝ) : ℂ) * (Complex.exp ((θ : ℂ) * Complex.I)
            - Complex.exp ((π : ℂ) * Complex.I)))‖
      ≤ |ftTauDeriv a 1 (n - 1) θ| + |ftTau a 1 (n - 1) θ - L| + L * (2 * (π - θ)) := by
    refine le_trans (norm_add₃_le) ?_
    have t1 : ‖Complex.exp ((θ : ℂ) * Complex.I) * ((ftTauDeriv a 1 (n - 1) θ : ℝ) : ℂ)‖
        = |ftTauDeriv a 1 (n - 1) θ| := by
      rw [norm_mul, he1, one_mul, Complex.norm_real, Real.norm_eq_abs]
    have t2 : ‖Complex.I * (Complex.exp ((θ : ℂ) * Complex.I)
          * ((ftTau a 1 (n - 1) θ - L : ℝ) : ℂ))‖ = |ftTau a 1 (n - 1) θ - L| := by
      rw [norm_mul, Complex.norm_I, one_mul, norm_mul, he1, one_mul, Complex.norm_real,
        Real.norm_eq_abs]
    have t3 : ‖Complex.I * (((L : ℝ) : ℂ) * (Complex.exp ((θ : ℂ) * Complex.I)
          - Complex.exp ((π : ℂ) * Complex.I)))‖ ≤ L * (2 * (π - θ)) := by
      rw [norm_mul, Complex.norm_I, one_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hL]
      refine mul_le_mul_of_nonneg_left ?_ hL.le
      have h := norm_exp_sub_exp_le θ π
      rwa [abs_of_nonpos (by linarith : θ - π ≤ 0), show -(θ - π) = π - θ from by ring] at h
    rw [t1, t2]
    linarith
  refine le_trans hstep ?_
  have hqa : |ftTau a 1 (n - 1) θ - L| ≤ |K| * π * (π - θ) := by
    refine le_trans hq ?_
    have h1 : K * (π - θ) ^ 2 ≤ |K| * (π - θ) ^ 2 := by
      nlinarith [le_abs_self K, sq_nonneg (π - θ)]
    have h2 : |K| * (π - θ) ^ 2 ≤ |K| * π * (π - θ) := by
      have hprod : 0 ≤ |K| * ((π - θ) * θ) := by
        have : (0 : ℝ) ≤ π - θ := by linarith
        positivity
      nlinarith [hprod]
    linarith
  have hsa : |ftTauDeriv a 1 (n - 1) θ| ≤ |M| * (π - θ) := by
    refine le_trans hs ?_
    nlinarith [le_abs_self M, sub_nonneg.2 hlt.le]
  linarith [hsa, hqa]

/-- The cofactor along the arc reads the radius pointwise, so two radii agreeing at a
parameter agree there. -/
theorem ftCofactorAlong_congr_radius {Q : Polynomial ℂ} {r : ℕ} {z τ τ' : ℝ → ℝ} {θ : ℝ}
    (h : τ θ = τ' θ) : ftCofactorAlong Q r z τ θ = ftCofactorAlong Q r z τ' θ := by
  simp only [ftCofactorAlong, ftPrincipal, h]

theorem ftCriticalAlong_congr_radius {Q : Polynomial ℂ} {r : ℕ} {τ τ' : ℝ → ℝ} {θ : ℝ}
    (h : τ θ = τ' θ) : ftCriticalAlong Q r τ θ = ftCriticalAlong Q r τ' θ := by
  simp only [ftCriticalAlong, ftPrincipal, h]

/-- **`κ₀`'s outer region at the `r = 1` upper endpoint, with nothing assumed.**  The
counterpart of `PhaseSupplyUpperRegion.ft_upper_region`, which covers `2 ≤ r` only because
the branch runs into the origin there and `E(0) ≠ 0`.

The cut point is returned rather than taken, as at the other end, so the region assembly
reuses it. -/
theorem ft_upper_region_one (hn2 : 2 ≤ n) (ha : ∀ k, 0 < a k) (hc : 0 < c) :
    ∃ b₂ C₃ : ℝ, 0 < b₂ ∧ b₂ < π / ((1 : ℕ) : ℝ) ∧
      ∀ θ ∈ Ioo b₂ (π / ((1 : ℕ) : ℝ)),
        |(ftArcCofactorDeriv a c 1 x₁ θ
          / ftCofactorAlong (ftRootPoly c a) 1 (ftBranchZLower a c 1 (n - 1))
              (ftTauArc a 1 (n - 1) x₁) θ).im| ≤ C₃ := by
  have hn : 0 < n := by omega
  have hπ := Real.pi_pos
  have hpi : π / ((1 : ℕ) : ℝ) = π := pi_div_natCast_one
  obtain ⟨L, hL, hlim, hLe⟩ := exists_tendsto_ftTau_nhdsLT_pi hn2 ha hc
  obtain ⟨Lip, b, hb0, hbπ, hLip0, hd0, hd, hlip⟩ :=
    ft_upper_endpoint_branch_data_one (x₁ := x₁) hn2 ha hc hL hLe hlim
  set v : ℂ := -(((L : ℝ) : ℂ) * Complex.I) with hv
  have hv0 : ftGammaDerivPi a (n - 1) v π ≠ 0 := by
    rw [ftGammaDerivPi_pi, hv]
    simp only [ne_eq, neg_eq_zero, mul_eq_zero, Complex.I_ne_zero, or_false,
      Complex.ofReal_eq_zero]
    exact hL.ne'
  -- the two radii agree strictly below `π`, which is where every collar hypothesis lives
  have hrad : ∀ θ < π, ftTauArcAt a 1 (n - 1) x₁ L θ = ftTauArc a 1 (n - 1) x₁ θ :=
    fun θ hθ => ftTauArcAt_eq_ftTauArc_of_lt a 1 (n - 1) x₁ L (by rw [hpi]; exact hθ)
  have hsubarc : ∀ θ ∈ Ioo (π - b) π, θ ∈ Ioo (0 : ℝ) (π / ((1 : ℕ) : ℝ)) := by
    intro θ hθ
    rw [hpi]
    exact ⟨by linarith [hθ.1], hθ.2⟩
  -- `τ` has a derivative on the collar
  have hbranchAll : ∀ t ∈ Ioo (0 : ℝ) (π / ((1 : ℕ) : ℝ)), FTBranchAt a 1 (n - 1) t :=
    fun t ht => ftBranchAt_of_arc_principal hn ha le_rfl (Or.inl hn2) ht
  have hτd : ∀ θ ∈ Ioo (π - b) π,
      HasDerivAt (ftTauArcAt a 1 (n - 1) x₁ L) (ftTauDeriv a 1 (n - 1) θ) θ := by
    intro θ hθ
    have harc := hsubarc θ hθ
    refine (hasDerivAt_ftTau hn ha le_rfl harc hbranchAll).congr_of_eventuallyEq ?_
    filter_upwards [isOpen_Ioo.mem_nhds harc] with s hs
    rw [hpi] at hs
    exact ftTauArcAt_agree a 1 (n - 1) x₁ L hs.1 (by rw [hpi]; exact hs.2)
  -- the cofactor's derivative and the branch state, transported off `ftTauArc`
  obtain ⟨hSd0, -, -⟩ := ft_cofactor_group (x₁ := x₁) hn ha hc.ne' le_rfl (Or.inl hn2)
  have hSd : ∀ θ ∈ Ioo (π - b) π,
      HasDerivAt (ftCofactorAlong (ftRootPoly c a) 1 (ftBranchZLower a c 1 (n - 1))
        (ftTauArcAt a 1 (n - 1) x₁ L)) (ftArcCofactorDeriv a c 1 x₁ θ) θ := by
    intro θ hθ
    have harc := hsubarc θ hθ
    refine (hSd0 θ harc).congr_of_eventuallyEq ?_
    filter_upwards [isOpen_Iio.mem_nhds (show θ ∈ Iio π from hθ.2)] with s hs
    exact ftCofactorAlong_congr_radius (hrad s hs)
  have hstate0 := ft_branch_state_arc (x₁ := x₁) hn ha hc.ne' le_rfl (Or.inl hn2)
  have hstate : ∀ θ ∈ Ioo (π - b) π,
      ftPrincipal (ftTauArcAt a 1 (n - 1) x₁ L) θ ≠ 0
      ∧ (ftDen (ftRootPoly c a) 1 ((ftBranchZLower a c 1 (n - 1) θ : ℝ) : ℂ)).eval
          (ftPrincipal (ftTauArcAt a 1 (n - 1) x₁ L) θ) = 0
      ∧ ftCriticalAlong (ftRootPoly c a) 1 (ftTauArcAt a 1 (n - 1) x₁ L) θ ≠ 0 := by
    intro θ hθ
    obtain ⟨h1, h2, h3⟩ := hstate0 θ (hsubarc θ hθ)
    have hγ : ftPrincipal (ftTauArcAt a 1 (n - 1) x₁ L) θ
        = ftPrincipal (ftTauArc a 1 (n - 1) x₁) θ := by
      simp only [ftPrincipal, hrad θ hθ.2]
    exact ⟨by rw [hγ]; exact h1, by rw [hγ]; exact h2,
      by rw [ftCriticalAlong_congr_radius (hrad θ hθ.2)]; exact h3⟩
  -- separation: on the open arc the branch point has positive imaginary part
  have hsep : ∀ θ ∈ Ioo (π - b) π,
      ftPrincipal (ftTauArcAt a 1 (n - 1) x₁ L) θ
        ≠ ftPrincipal (ftTauArcAt a 1 (n - 1) x₁ L) π := by
    intro θ hθ hEq
    have harc := hsubarc θ hθ
    have hτpos : 0 < ftTauArcAt a 1 (n - 1) x₁ L θ := by
      rw [ftTauArcAt_agree a 1 (n - 1) x₁ L harc.1 harc.2]
      exact ftTau_pos (hbranchAll θ harc)
    have him := congrArg Complex.im hEq
    rw [ftPrincipal_im, ftPrincipal_im] at him
    have hs0 : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi harc.1 hθ.2
    have hpos : (0 : ℝ) < ftTauArcAt a 1 (n - 1) x₁ L θ * Real.sin θ := by positivity
    rw [him, Real.sin_pi, mul_zero] at hpos
    exact lt_irrefl 0 hpos
  have hγc : ContinuousWithinAt (ftPrincipal (ftTauArcAt a 1 (n - 1) x₁ L)) (Iio π) π := by
    have h := (hd0.congr_deriv rfl).continuousWithinAt
    exact h.mono Iio_subset_Iic_self
  obtain ⟨b', κ, hb'0, hb'b, hκ0, hbd⟩ :=
    exists_bound_im_logDeriv_ftCofactorAlong_at_collision_left
      (Q := ftRootPoly c a) (r := 1) (z := ftBranchZLower a c 1 (n - 1))
      (τ := ftTauArcAt a 1 (n - 1) x₁ L) (dγ := ftGammaDerivPi a (n - 1) v)
      (dS := ftArcCofactorDeriv a c 1 x₁) (dτ := ftTauDeriv a 1 (n - 1))
      (c := π) le_rfl hb0 hLip0 hd0 hd hlip hv0 hτd hSd hstate hsep hγc
  refine ⟨π - b', κ, by linarith, by rw [hpi]; linarith, fun θ hθ => ?_⟩
  rw [hpi] at hθ
  have h := hbd θ ⟨by linarith [hθ.1], hθ.2⟩
  rwa [ftCofactorAlong_congr_radius (hrad θ hθ.2)] at h

/-- **`eq:phase-derivative-bound` on the region at the `r = 1` upper endpoint, with nothing
assumed.**  The counterpart of `PhaseSupplyRegionBounds.ft_region_upper`, whose route is
unavailable here: there the branch runs into `0`, neither `B` nor `E` vanishes, and the
bound is the numerator ratio against `‖γ'‖`.  At `r = 1` the branch runs into `-L`, where
`E` vanishes and `B` may, so the numerator's own multiplicity has to be divided out — which
is what `exists_bound_im_logDeriv_ftAmp_endpoint_left` does.

**No condition is placed on `B` at the collision.**  The estimate reads
`B.rootMultiplicity (-L)` off the polynomial and carries whatever it is, so a numerator
vanishing there is inside the scope rather than a case beyond it. -/
theorem ft_region_upper_one (B : Polynomial ℂ) (hB : B ≠ 0) (hn2 : 2 ≤ n)
    (ha : ∀ k, 0 < a k) (hc : 0 < c) :
    ∃ b₂ C₃ : ℝ, 0 < b₂ ∧ b₂ < π / ((1 : ℕ) : ℝ) ∧
      ∀ s ∈ Ico b₂ (π / ((1 : ℕ) : ℝ)),
        ftAmp (ftRootPoly c a) B 1 ((ftBranchZLower a c 1 (n - 1) s : ℝ) : ℂ)
            (ftPrincipal (ftTauArc a 1 (n - 1) x₁) s) ≠ 0 →
        |(ftArcAmpDeriv a B c 1 x₁ s / ftAmp (ftRootPoly c a) B 1
          ((ftBranchZLower a c 1 (n - 1) s : ℝ) : ℂ)
          (ftPrincipal (ftTauArc a 1 (n - 1) x₁) s)).im| ≤ C₃ := by
  classical
  have hn : 0 < n := by omega
  have hπ := Real.pi_pos
  have hpi : π / ((1 : ℕ) : ℝ) = π := pi_div_natCast_one
  obtain ⟨L, hL, hlim, hLe⟩ := exists_tendsto_ftTau_nhdsLT_pi hn2 ha hc
  obtain ⟨Lip, b, hb0, hbπ, hLip0, hd0, hd, hlip⟩ :=
    ft_upper_endpoint_branch_data_one (x₁ := x₁) hn2 ha hc hL hLe hlim
  set v : ℂ := -(((L : ℝ) : ℂ) * Complex.I) with hv
  set τ' : ℝ → ℝ := ftTauArcAt a 1 (n - 1) x₁ L with hτ'
  set γ : ℝ → ℂ := ftPrincipal τ' with hγ
  set zf : ℝ → ℂ := fun s : ℝ => ((ftBranchZLower a c 1 (n - 1) s : ℝ) : ℂ) with hzf
  have hv0 : ftGammaDerivPi a (n - 1) v π ≠ 0 := by
    rw [ftGammaDerivPi_pi, hv]
    simp only [ne_eq, neg_eq_zero, mul_eq_zero, Complex.I_ne_zero, or_false,
      Complex.ofReal_eq_zero]
    exact hL.ne'
  have hrad : ∀ θ < π, τ' θ = ftTauArc a 1 (n - 1) x₁ θ :=
    fun θ hθ => ftTauArcAt_eq_ftTauArc_of_lt a 1 (n - 1) x₁ L (by rw [hpi]; exact hθ)
  have hγeq : ∀ θ < π, γ θ = ftPrincipal (ftTauArc a 1 (n - 1) x₁) θ := by
    intro θ hθ
    simp only [hγ, ftPrincipal, hrad θ hθ]
  -- `E`'s factorization at the collision
  have hQ0 : (ftRootPoly c a).eval 0 ≠ 0 := eval_ftRootPoly_zero_ne_zero hc.ne' ha
  have hEne : ftCritical (ftRootPoly c a) 1 ≠ 0 := fun h0 =>
    eval_ftCritical_zero_ne_zero le_rfl hQ0 (by rw [h0]; simp)
  have hEfac := ftCritical_eq_pow_mul_ftCriticalReduced (ftRootPoly c a) 1 τ' π
  have hH0 := eval_ftCriticalReduced_ne_zero (Q := ftRootPoly c a) (r := 1) (τ := τ') hEne π
  have hteval : γ π = -((L : ℝ) : ℂ) := by
    have hτπ : τ' π = L := by
      rw [hτ', ftTauArcAt, if_neg (by rw [hpi]; exact lt_irrefl π)]
    rw [hγ, ftPrincipal, hτπ, show ((π : ℝ) : ℂ) = (π : ℂ) from rfl, Complex.exp_pi_mul_I]
    ring
  have hte : γ π ≠ 0 := by
    rw [hteval]
    simpa using hL.ne'
  -- the pencil vanishes at the branch point on the collar
  have hsubarc : ∀ θ ∈ Ico (π - b / 2) π, θ ∈ Ioo (0 : ℝ) (π / ((1 : ℕ) : ℝ)) := by
    intro θ hθ
    rw [hpi]
    exact ⟨by linarith [hθ.1], hθ.2⟩
  have hstate0 := ft_branch_state_arc (x₁ := x₁) hn ha hc.ne' le_rfl (Or.inl hn2)
  have hroot : ∀ θ ∈ Ico (π - b / 2) π,
      (ftDen (ftRootPoly c a) 1 (zf θ)).eval (γ θ) = 0 := by
    intro θ hθ
    rw [hγeq θ hθ.2]
    exact (hstate0 θ (hsubarc θ hθ)).2.1
  obtain ⟨b', C, hb'0, hb'b, hC0, hbd⟩ :=
    exists_bound_im_logDeriv_ftAmp_endpoint_left (Q := ftRootPoly c a) (B := B) (r := 1)
      (γ := γ) (dγ := ftGammaDerivPi a (n - 1) v) (zf := zf) (te := γ π)
      (H := ftCriticalReduced (ftRootPoly c a) 1 τ' π)
      (m := ftCollisionOrder (ftRootPoly c a) 1 τ' π) (c := π)
      hB le_rfl (by positivity) hLip0 hEfac hH0 hte rfl hd0
      (fun θ hθ => hd θ ⟨by linarith [hθ.1], hθ.2⟩)
      (fun θ hθ => hlip θ ⟨by linarith [hθ.1], hθ.2⟩) hv0 hroot
  refine ⟨π - b', C, by linarith, by rw [hpi]; linarith, fun s hs _ => ?_⟩
  rw [hpi] at hs
  have hsπ : s < π := hs.2
  have hsmem : s ∈ Ico (π - b') π := ⟨by linarith [hs.1], hsπ⟩
  have hs0 : s ∈ Ioo (0 : ℝ) (π / ((1 : ℕ) : ℝ)) := by
    rw [hpi]
    exact ⟨by linarith [hs.1, hb'b, hb0], hsπ⟩
  have h := hbd s hsmem
  -- the two radii agree below `π`, so both the amplitude and its derivative do
  have hfun : (fun t : ℝ => ftAmp (ftRootPoly c a) B 1 (zf t) (γ t))
      =ᶠ[nhds s] fun t : ℝ => ftAmp (ftRootPoly c a) B 1
        ((ftBranchZLower a c 1 (n - 1) t : ℝ) : ℂ)
        (ftPrincipal (ftTauArc a 1 (n - 1) x₁) t) := by
    filter_upwards [isOpen_Iio.mem_nhds (show s ∈ Iio π from hsπ)] with t ht
    rw [hγeq t ht]
  rw [hfun.deriv_eq, ft_deriv_ftAmp_eq (x₁ := x₁) B hn ha hc.ne' le_rfl (Or.inl hn2) hs0,
    hγeq s hsπ] at h
  exact h

end ForgacsTran
