/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import ForgacsTran.LowerEndpointRates
import ForgacsTran.PhaseSupplyLowerCollar
import ForgacsTran.PhaseSupplyRegionBounds

/-!
# The collar and the region bound at a SIMPLE lower endpoint

`PhaseSupplyLowerCollar.ft_endpoint_branch_data` packages the lower endpoint's binders at a
**repeated** smallest zero: the branch runs into `x₁` itself, the one-sided derivative is the
cluster expansion's `-x₁\cot(π/ρ) + ix₁`, and the Lipschitz bound comes from `τ''` at that
cluster.  Neither half survives at `ρ = 1`, and not because a proof is missing: the endpoint
is a **different point** — a critical point strictly inside the first gap — so the arc
extension carrying `x₁` is discontinuous there
(`LowerEndpointSimpleZero.not_continuousWithinAt_ftTauArcAt_min_of_simple`), and the binders
written against it are unsatisfiable rather than open.

This module packages the same binders at the endpoint the branch actually has, from
`LowerEndpointRates`' two rates.  The value is `iL` — perpendicular to the real axis, as the
`ρ ≥ 2` formula's junk return also is, which is why nothing about the value's shape can tell
the two apart and the rate is what has to be produced.

`ft_lower_collar` and `ft_region_lower` then follow by substitution: their only use of `ρ ≥ 2`
is through the package, and everything else in both is stated at `1 ≤ r`.

Sorry-free.

## Main statements

* `ft_endpoint_branch_data_simple` — the four endpoint binders at a simple endpoint.
* `ft_lower_collar_simple` — `κ₀`'s collar there.
* `ft_region_lower_simple` — `eq:phase-derivative-bound` on the same region.

## References

Formalizes `../../shields-2026-forgacs-tran-numerators.tex`,
`lem:principal-endpoint-regularity`, `cor:linear-phase-variation`.

## Tags

lower endpoint, simple zero, collar, bounded variation, Forgács–Tran
-/

namespace ForgacsTran

open Polynomial Set Real Filter Topology

variable {n r : ℕ} {a : Fin n → ℝ} {c L : ℝ}

/-- **The branch enters a simple lower endpoint with derivative `iL`.**  The radius reaches
`L` quadratically, so the whole derivative is the rotation's. -/
theorem hasDerivWithinAt_ftPrincipal_ftTauArc_simple (hn : 0 < n) (ha : ∀ k, 0 < a k)
    (hr : 1 ≤ r) (hnr : 2 ≤ n ∨ 2 ≤ r) (hL : 0 < L)
    (hLe : (ftCriticalReal (ftRootPolyReal c a) r).eval L = 0)
    (hLd : (derivative (ftCriticalReal (ftRootPolyReal c a) r)).eval L ≠ 0)
    (hlim : Tendsto (ftTau a r (n - 1)) (𝓝[>] (0 : ℝ)) (𝓝 L)) :
    HasDerivWithinAt (ftPrincipal (ftTauArc a r (n - 1) L))
      (((L : ℝ) : ℂ) * Complex.I) (Ici 0) 0 := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast Nat.lt_of_lt_of_le Nat.one_pos hr
  have harc : (0 : ℝ) < π / r := by positivity
  have hτ0 : ftTauArc a r (n - 1) L 0 = L := by
    rw [ftTauArc_eq_ftTauArcAt, ftTauArcAt_zero a r (n - 1) L 0 harc]
  have hrot : HasDerivAt (fun θ : ℝ => ((L : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))
      (((L : ℝ) : ℂ) * (Complex.exp (((0 : ℝ) : ℂ) * Complex.I) * (1 * Complex.I))) 0 :=
    ((((hasDerivAt_id (0 : ℝ)).ofReal_comp).mul_const Complex.I).cexp).const_mul _
  have hrotval : ((L : ℝ) : ℂ) * (Complex.exp (((0 : ℝ) : ℂ) * Complex.I) * (1 * Complex.I))
      = ((L : ℝ) : ℂ) * Complex.I := by
    simp
  rw [hrotval] at hrot
  obtain ⟨K, δ, hδ, hδarc, hquad⟩ :=
    exists_quadratic_bound_ftTau_lower (c := c) hn ha hr hnr hL hLe hLd hlim
  have hrem : HasDerivWithinAt
      (fun θ : ℝ => ((ftTauArc a r (n - 1) L θ - L : ℝ) : ℂ)
        * Complex.exp ((θ : ℂ) * Complex.I)) 0 (Ici 0) 0 := by
    rw [hasDerivWithinAt_iff_tendsto_slope]
    have hset : Ici (0 : ℝ) \ {0} = Ioi (0 : ℝ) := by
      ext y
      simp only [Set.mem_sdiff, mem_Ici, mem_singleton_iff, mem_Ioi]
      exact ⟨fun h => lt_of_le_of_ne h.1 (Ne.symm h.2), fun h => ⟨h.le, ne_of_gt h⟩⟩
    rw [hset]
    have hz : ∀ᶠ y in 𝓝[>] (0 : ℝ),
        ‖slope (fun θ : ℝ => ((ftTauArc a r (n - 1) L θ - L : ℝ) : ℂ)
          * Complex.exp ((θ : ℂ) * Complex.I)) 0 y‖ ≤ |K| * y := by
      filter_upwards [Ioo_mem_nhdsGT hδ] with y hy
      have hyarc : y < π / r := lt_of_lt_of_le hy.2 hδarc
      have hτy : ftTauArc a r (n - 1) L y = ftTau a r (n - 1) y :=
        ftTauArc_agree a r (n - 1) L hy.1 hyarc
      have hbd : |ftTauArc a r (n - 1) L y - L| ≤ K * y ^ 2 := by
        rw [hτy]; exact hquad y hy
      have hf0 : ((ftTauArc a r (n - 1) L 0 - L : ℝ) : ℂ)
          * Complex.exp (((0 : ℝ) : ℂ) * Complex.I) = 0 := by
        rw [hτ0]; simp
      have hslopeval : slope (fun θ : ℝ => ((ftTauArc a r (n - 1) L θ - L : ℝ) : ℂ)
            * Complex.exp ((θ : ℂ) * Complex.I)) 0 y
          = y⁻¹ • (((ftTauArc a r (n - 1) L y - L : ℝ) : ℂ)
            * Complex.exp ((y : ℂ) * Complex.I)) := by
        rw [slope, vsub_eq_sub, hf0, sub_zero, sub_zero]
      rw [hslopeval, norm_smul, norm_inv, Real.norm_eq_abs, norm_mul, Complex.norm_real,
        Complex.norm_exp_ofReal_mul_I, mul_one, Real.norm_eq_abs,
        inv_mul_le_iff₀ (abs_pos.2 (ne_of_gt hy.1)), abs_of_pos hy.1]
      calc |ftTauArc a r (n - 1) L y - L| ≤ K * y ^ 2 := hbd
        _ ≤ |K| * y ^ 2 := by nlinarith [le_abs_self K, sq_nonneg y]
        _ = y * (|K| * y) := by ring
    have hg : Tendsto (fun y : ℝ => |K| * y) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have h : Tendsto (fun y : ℝ => |K| * y) (𝓝[>] (0 : ℝ)) (𝓝 (|K| * 0)) :=
        ((continuous_const.mul continuous_id).tendsto 0).mono_left nhdsWithin_le_nhds
      simpa using h
    exact squeeze_zero_norm' hz hg
  have hsum := (hrot.hasDerivWithinAt (s := Ici (0 : ℝ))).add hrem
  rw [add_zero] at hsum
  refine hsum.congr (fun y _ => ?_) ?_
  · simp only [ftPrincipal, Pi.add_apply]; push_cast; ring
  · simp only [ftPrincipal, Pi.add_apply, hτ0]; push_cast; ring

/-- **The collar's endpoint binders at a simple lower endpoint.**  The same four
`ft_endpoint_branch_data` returns, at the endpoint the branch actually has. -/
theorem ft_endpoint_branch_data_simple (hn : 0 < n) (ha : ∀ k, 0 < a k)
    (hr : 1 ≤ r) (hnr : 2 ≤ n ∨ 2 ≤ r) (hL : 0 < L)
    (hLe : (ftCriticalReal (ftRootPolyReal c a) r).eval L = 0)
    (hLd : (derivative (ftCriticalReal (ftRootPolyReal c a) r)).eval L ≠ 0)
    (hlim : Tendsto (ftTau a r (n - 1)) (𝓝[>] (0 : ℝ)) (𝓝 L)) :
    ∃ (v : ℂ) (Lip b : ℝ), 0 < b ∧ b < π / r ∧ 0 ≤ Lip ∧
      ftGammaDerivAt a r (n - 1) v 0 ≠ 0 ∧
      HasDerivWithinAt (ftPrincipal (ftTauArc a r (n - 1) L))
        (ftGammaDerivAt a r (n - 1) v 0) (Ici 0) 0 ∧
      (∀ θ ∈ Ioc (0 : ℝ) b, HasDerivAt (ftPrincipal (ftTauArc a r (n - 1) L))
        (ftGammaDerivAt a r (n - 1) v θ) θ) ∧
      (∀ θ ∈ Icc (0 : ℝ) b,
        ‖ftGammaDerivAt a r (n - 1) v θ - ftGammaDerivAt a r (n - 1) v 0‖ ≤ Lip * θ) := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast Nat.lt_of_lt_of_le Nat.one_pos hr
  have harc : (0 : ℝ) < π / r := by positivity
  set v : ℂ := ((L : ℝ) : ℂ) * Complex.I with hv
  have hv0 : ftGammaDerivAt a r (n - 1) v 0 ≠ 0 := by
    rw [ftGammaDerivAt_zero, hv]
    simp only [ne_eq, mul_eq_zero, Complex.I_ne_zero, or_false, Complex.ofReal_eq_zero]
    exact hL.ne'
  obtain ⟨K, δ₁, hδ₁, hδ₁arc, hquad⟩ :=
    exists_quadratic_bound_ftTau_lower (c := c) hn ha hr hnr hL hLe hLd hlim
  obtain ⟨M, δ₂, hδ₂, hδ₂arc, hslope⟩ :=
    exists_linear_bound_ftTauDeriv_lower (c := c) hn ha hr hnr hL hLd hlim
  set b : ℝ := min (min δ₁ δ₂ / 2) (π / (2 * r)) with hb
  have hhalf : π / (2 * r) < π / r := div_lt_div_of_pos_left pi_pos hrR (by linarith)
  have hb0 : 0 < b := lt_min (by positivity) (by positivity)
  have hbarc : b < π / r := lt_of_le_of_lt (min_le_right _ _) hhalf
  have hbδ₁ : b < δ₁ := lt_of_le_of_lt (min_le_left _ _) (by
    have := min_le_left δ₁ δ₂; linarith)
  have hbδ₂ : b < δ₂ := lt_of_le_of_lt (min_le_left _ _) (by
    have := min_le_right δ₁ δ₂; linarith)
  have hd0 : HasDerivWithinAt (ftPrincipal (ftTauArc a r (n - 1) L))
      (ftGammaDerivAt a r (n - 1) v 0) (Ici 0) 0 := by
    rw [ftGammaDerivAt_zero, hv]
    exact hasDerivWithinAt_ftPrincipal_ftTauArc_simple hn ha hr hnr hL hLe hLd hlim
  have hd : ∀ θ ∈ Ioc (0 : ℝ) b, HasDerivAt (ftPrincipal (ftTauArc a r (n - 1) L))
      (ftGammaDerivAt a r (n - 1) v θ) θ := by
    intro θ hθ
    rw [ftGammaDerivAt_of_ne a r (n - 1) v (ne_of_gt hθ.1), ftTauArc_eq_ftTauArcAt]
    exact hasDerivAt_ftPrincipal_ftTauArcAt hn ha hr hnr L 0
      ⟨hθ.1, lt_of_le_of_lt hθ.2 hbarc⟩
  refine ⟨v, |M| + |K| * b + 2 * L, b, hb0, hbarc, by positivity, hv0, hd0, hd,
    fun θ hθ => ?_⟩
  rcases eq_or_lt_of_le hθ.1 with rfl | hpos
  · simp
  have hθarc : θ ∈ Ioo (0 : ℝ) (π / r) := ⟨hpos, lt_of_le_of_lt hθ.2 hbarc⟩
  have hq := hquad θ ⟨hpos, lt_of_le_of_lt hθ.2 hbδ₁⟩
  have hs := hslope θ ⟨hpos, lt_of_le_of_lt hθ.2 hbδ₂⟩
  rw [ftGammaDerivAt_of_ne a r (n - 1) v (ne_of_gt hpos), ftGammaDerivAt_zero]
  have hexp0 : Complex.exp (((0 : ℝ) : ℂ) * Complex.I) = 1 := by simp
  have hdecomp : ftGammaDeriv a r (n - 1) θ - v
      = Complex.exp ((θ : ℂ) * Complex.I) * ((ftTauDeriv a r (n - 1) θ : ℝ) : ℂ)
        + Complex.I * (Complex.exp ((θ : ℂ) * Complex.I)
            * ((ftTau a r (n - 1) θ - L : ℝ) : ℂ))
        + Complex.I * (((L : ℝ) : ℂ) * (Complex.exp ((θ : ℂ) * Complex.I)
            - Complex.exp (((0 : ℝ) : ℂ) * Complex.I))) := by
    rw [ftGammaDeriv, hv, hexp0]
    push_cast
    ring
  rw [hdecomp]
  have he1 : ‖Complex.exp ((θ : ℂ) * Complex.I)‖ = 1 := Complex.norm_exp_ofReal_mul_I θ
  have hstep : ‖Complex.exp ((θ : ℂ) * Complex.I) * ((ftTauDeriv a r (n - 1) θ : ℝ) : ℂ)
        + Complex.I * (Complex.exp ((θ : ℂ) * Complex.I)
            * ((ftTau a r (n - 1) θ - L : ℝ) : ℂ))
        + Complex.I * (((L : ℝ) : ℂ) * (Complex.exp ((θ : ℂ) * Complex.I)
            - Complex.exp (((0 : ℝ) : ℂ) * Complex.I)))‖
      ≤ |ftTauDeriv a r (n - 1) θ| + |ftTau a r (n - 1) θ - L| + L * (2 * θ) := by
    refine le_trans norm_add₃_le ?_
    have t1 : ‖Complex.exp ((θ : ℂ) * Complex.I) * ((ftTauDeriv a r (n - 1) θ : ℝ) : ℂ)‖
        = |ftTauDeriv a r (n - 1) θ| := by
      rw [norm_mul, he1, one_mul, Complex.norm_real, Real.norm_eq_abs]
    have t2 : ‖Complex.I * (Complex.exp ((θ : ℂ) * Complex.I)
          * ((ftTau a r (n - 1) θ - L : ℝ) : ℂ))‖ = |ftTau a r (n - 1) θ - L| := by
      rw [norm_mul, Complex.norm_I, one_mul, norm_mul, he1, one_mul, Complex.norm_real,
        Real.norm_eq_abs]
    have t3 : ‖Complex.I * (((L : ℝ) : ℂ) * (Complex.exp ((θ : ℂ) * Complex.I)
          - Complex.exp (((0 : ℝ) : ℂ) * Complex.I)))‖ ≤ L * (2 * θ) := by
      rw [norm_mul, Complex.norm_I, one_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hL]
      refine mul_le_mul_of_nonneg_left ?_ hL.le
      have h := norm_exp_sub_exp_le θ 0
      rwa [sub_zero, abs_of_pos hpos] at h
    rw [t1, t2]
    linarith
  refine le_trans hstep ?_
  have hqa : |ftTau a r (n - 1) θ - L| ≤ |K| * b * θ := by
    refine le_trans hq ?_
    have h1 : K * θ ^ 2 ≤ |K| * θ ^ 2 := by nlinarith [le_abs_self K, sq_nonneg θ]
    have h2 : |K| * θ ^ 2 ≤ |K| * b * θ := by
      have hprod : 0 ≤ |K| * ((b - θ) * θ) := by
        have : (0 : ℝ) ≤ b - θ := by linarith [hθ.2]
        positivity
      nlinarith [hprod]
    linarith
  have hsa : |ftTauDeriv a r (n - 1) θ| ≤ |M| * θ := by
    refine le_trans hs ?_
    nlinarith [le_abs_self M, hpos.le]
  linarith [hsa, hqa]

/-- **`κ₀`'s collar at a simple lower endpoint, with nothing assumed beyond the endpoint's
own data.**  `PhaseSupplyLowerCollar.ft_lower_collar` with the package substituted; its only
use of `ρ ≥ 2` is through the endpoint binders. -/
theorem ft_lower_collar_simple (hn : 0 < n) (ha : ∀ k, 0 < a k) (hr : 1 ≤ r)
    (hnr : 2 ≤ n ∨ 2 ≤ r) (hc : c ≠ 0) (hL : 0 < L)
    (hLe : (ftCriticalReal (ftRootPolyReal c a) r).eval L = 0)
    (hLd : (derivative (ftCriticalReal (ftRootPolyReal c a) r)).eval L ≠ 0)
    (hlim : Tendsto (ftTau a r (n - 1)) (𝓝[>] (0 : ℝ)) (𝓝 L)) :
    ∃ b₁ C₁ : ℝ, 0 < b₁ ∧ b₁ ≤ π / r ∧ 0 ≤ C₁ ∧ ∀ θ ∈ Ioo (0 : ℝ) b₁,
      |(ftArcCofactorDeriv a c r L θ
        / ftCofactorAlong (ftRootPoly c a) r (ftBranchZLower a c r (n - 1))
            (ftTauArc a r (n - 1) L) θ).im| ≤ C₁ := by
  classical
  have hrR : (0 : ℝ) < r := by exact_mod_cast Nat.lt_of_lt_of_le Nat.one_pos hr
  have harc : (0 : ℝ) < π / r := by positivity
  have hbranch : ∀ θ ∈ Ioo (0 : ℝ) (π / r), FTBranchAt a r (n - 1) θ :=
    fun θ hθ => ftBranchAt_of_arc_principal hn ha hr hnr hθ
  obtain ⟨hSd, hSc, hS0⟩ := ft_cofactor_group (x₁ := L) hn ha hc hr hnr
  have hstate := ft_branch_state_arc (x₁ := L) hn ha hc hr hnr
  obtain ⟨v, Lip, b, hb0, hblt, hLip0, hne0, hd0, hd, hlip⟩ :=
    ft_endpoint_branch_data_simple (c := c) hn ha hr hnr hL hLe hLd hlim
  have hsubarc : Ioo (0 : ℝ) b ⊆ Ioo (0 : ℝ) (π / r) :=
    fun θ hθ => ⟨hθ.1, lt_trans hθ.2 hblt⟩
  have hτd : ∀ θ ∈ Ioo (0 : ℝ) b,
      HasDerivAt (ftTauArc a r (n - 1) L) (ftTauDeriv a r (n - 1) θ) θ := by
    intro θ hθ
    refine (hasDerivAt_ftTau hn ha hr (hsubarc hθ) hbranch).congr_of_eventuallyEq ?_
    filter_upwards [isOpen_Ioo.mem_nhds (hsubarc hθ)] with s hs
    exact ftTauArc_agree a r (n - 1) L hs.1 hs.2
  have hsep : ∀ θ ∈ Ioo (0 : ℝ) b,
      ftPrincipal (ftTauArc a r (n - 1) L) θ ≠ ftPrincipal (ftTauArc a r (n - 1) L) 0 := by
    intro θ hθ hEq
    have hθπ : θ ∈ Ioo (0 : ℝ) π := ftArc_subset hr (hsubarc hθ)
    have hτpos : 0 < ftTauArc a r (n - 1) L θ := by
      rw [ftTauArc_agree a r (n - 1) L hθ.1 (hsubarc hθ).2]
      exact ftTau_pos (hbranch θ (hsubarc hθ))
    have him := congrArg Complex.im hEq
    rw [ftPrincipal_im, ftPrincipal_im] at him
    have hs0 : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθπ.1 hθπ.2
    have hpos : (0 : ℝ) < ftTauArc a r (n - 1) L θ * Real.sin θ := by positivity
    rw [him, Real.sin_zero, mul_zero] at hpos
    exact lt_irrefl 0 hpos
  obtain ⟨b', κ, hb'0, hb'b, hκ0, hbd⟩ :=
    exists_bound_im_logDeriv_ftCofactorAlong_at_collision
      (Q := ftRootPoly c a) (r := r) (z := ftBranchZLower a c r (n - 1))
      (τ := ftTauArc a r (n - 1) L) (dγ := ftGammaDerivAt a r (n - 1) v)
      (dS := ftArcCofactorDeriv a c r L) (dτ := ftTauDeriv a r (n - 1))
      hr hb0 hLip0 hd0 hd hlip hne0 hτd
      (fun θ hθ => hSd θ (hsubarc hθ)) (fun θ hθ => hstate θ (hsubarc hθ)) hsep
      (hd0.continuousWithinAt.mono Ioi_subset_Ici_self)
  exact ⟨b', κ, hb'0, le_trans (le_trans hb'b hblt.le) le_rfl, hκ0, hbd⟩

/-- **`eq:phase-derivative-bound` on the region at a simple lower endpoint.**
`PhaseSupplyRegionBounds.ft_region_lower` with the package substituted. -/
theorem ft_region_lower_simple (B : Polynomial ℂ) (hB : B ≠ 0) (hn : 0 < n)
    (ha : ∀ k, 0 < a k) (hr : 1 ≤ r) (hnr : 2 ≤ n ∨ 2 ≤ r) (hc : c ≠ 0) (hL : 0 < L)
    (hLe : (ftCriticalReal (ftRootPolyReal c a) r).eval L = 0)
    (hLd : (derivative (ftCriticalReal (ftRootPolyReal c a) r)).eval L ≠ 0)
    (hlim : Tendsto (ftTau a r (n - 1)) (𝓝[>] (0 : ℝ)) (𝓝 L)) :
    ∃ b₁ C₁ : ℝ, 0 < b₁ ∧ b₁ < π / r ∧ ∀ s ∈ Ioc (0 : ℝ) b₁,
      |(ftArcAmpDeriv a B c r L s / ftAmp (ftRootPoly c a) B r
        ((ftBranchZLower a c r (n - 1) s : ℝ) : ℂ)
        (ftPrincipal (ftTauArc a r (n - 1) L) s)).im| ≤ C₁ := by
  classical
  have hrR : (0 : ℝ) < r := by exact_mod_cast Nat.lt_of_lt_of_le Nat.one_pos hr
  have harc : (0 : ℝ) < π / r := by positivity
  have hstate := ft_branch_state_arc (x₁ := L) hn ha hc hr hnr
  obtain ⟨v, Lip, b, hb0, hblt, hLip0, hne0, hd0, hd, hlip⟩ :=
    ft_endpoint_branch_data_simple (c := c) hn ha hr hnr hL hLe hLd hlim
  have hE : ftCritical (ftRootPoly c a) r ≠ 0 := by
    intro h
    have hθ : (π / r) / 2 ∈ Ioo (0 : ℝ) (π / r) := ⟨by positivity, by linarith⟩
    exact (hstate _ hθ).2.2 (by rw [ftCriticalAlong, h]; simp)
  have hte : ftPrincipal (ftTauArc a r (n - 1) L) 0 ≠ 0 := by
    refine ftPrincipal_ne_zero ?_
    rw [ftTauArc_eq_ftTauArcAt, ftTauArcAt_zero a r (n - 1) L 0 harc]
    exact hL.ne'
  obtain ⟨b', C, hb'0, hb'b, hC0, hbd⟩ :=
    exists_bound_im_logDeriv_ftAmp_endpoint (Q := ftRootPoly c a) (B := B) (r := r)
      (γ := ftPrincipal (ftTauArc a r (n - 1) L)) (dγ := ftGammaDerivAt a r (n - 1) v)
      (zf := fun s : ℝ => ((ftBranchZLower a c r (n - 1) s : ℝ) : ℂ))
      (te := ftPrincipal (ftTauArc a r (n - 1) L) 0)
      (H := ftCriticalReduced (ftRootPoly c a) r (ftTauArc a r (n - 1) L) 0)
      (m := ftCollisionOrder (ftRootPoly c a) r (ftTauArc a r (n - 1) L) 0)
      hB hr hb0 hLip0
      (ftCritical_eq_pow_mul_ftCriticalReduced _ _ _ 0)
      (eval_ftCriticalReduced_ne_zero hE 0) hte rfl hd0 hd hlip hne0
      (fun δ hδ => (hstate δ ⟨hδ.1, lt_of_le_of_lt hδ.2 hblt⟩).2.1)
  refine ⟨b', C, hb'0, lt_of_le_of_lt hb'b hblt, fun s hs => ?_⟩
  have hsarc : s ∈ Ioo (0 : ℝ) (π / r) :=
    ⟨hs.1, lt_of_le_of_lt (le_trans hs.2 hb'b) hblt⟩
  rw [← ft_deriv_ftAmp_eq (x₁ := L) B hn ha hc hr hnr hsarc]
  exact hbd s hs

end ForgacsTran
