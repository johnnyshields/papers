/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import ForgacsTran.EndpointTauDeriv2
import ForgacsTran.PhaseSupplyKappaZero

/-!
# `κ₀`'s collar at the collision, at a general pencil

`PhaseSupplyKappaZero.ft_kappaZero_of_collars` leaves one bound per endpoint.  This module
produces the one at `θ = 0`, where the principal pair collides, in the `ρ ≥ 2` cell.

**Nothing is assumed.**  The collar in `BranchSupplyGeometry`,
`exists_bound_im_logDeriv_ftCofactorAlong_at_collision`, carries five endpoint binders — the
one-sided derivative of the branch, its nonvanishing, the Lipschitz bound on `γ'`,
separation from the endpoint value, and one-sided continuity —
and every one of them is now discharged: the derivative from the cluster expansion, the
Lipschitz bound from `EndpointTauDeriv2.exists_lipschitz_ftGammaDerivAt_of_repeated_min`,
which closes `τ''` at a repeated smallest zero, and separation from the imaginary part.

**The two endpoint values have to be identified, and that is the one real step.**  The
Lipschitz bound is stated at the value `v` its own construction produces — the limit of
`γ'` along the arc — while the derivative binder is stated at the value `u` the cluster
expansion computes.  Neither statement mentions the other, so the collar cannot be
assembled until they are proved equal.  They are: `γ'` converges to `v`, so
`hasDerivWithinAt_Ici_of_tendsto_deriv` makes `v` a one-sided derivative of the branch at
`0` as well, and a one-sided derivative on `Ici 0` is unique.

**Separation is about the imaginary part, not about injectivity.**  On the open arc the
branch point is `τ(θ)e^{iθ}` with `τ > 0` and `0 < θ < π`, so its imaginary part is
positive, while the endpoint value `τ(0) = x₁` is real.  No global injectivity of the
branch is needed, and none is available.

Sorry-free.

## Main statements

* `exists_ft_cluster_gap` — the cluster's index data and the gap constant, from `hcard`.
* `ft_hasDerivWithinAt_ftPrincipal_zero` — `hd0` at the arc's own radius.
* `ft_endpoint_branch_data` — the four endpoint binders every collar asks for, packaged.
* `ft_lower_collar` — the collar bound at the collision, with nothing assumed.

## References

Formalizes `../../shields-2026-forgacs-tran-numerators.tex`,
`lem:principal-endpoint-regularity`, `cor:linear-phase-variation`.

## Tags

collision, collar, cluster expansion, bounded variation, Forgács–Tran
-/

namespace ForgacsTran

open Polynomial Set Real Filter Topology

variable {n r ρ : ℕ} {a : Fin n → ℝ} {c x₁ : ℝ}

/-- **The cluster's index data and its gap, from the multiplicity alone.**
`BranchSupplyGeometry`'s endpoint statements take a cluster `S`, two of its members, and a
relative gap `c` to the zeros outside it; `ρ ≥ 2` supplies the members and finiteness
supplies the gap. -/
theorem exists_ft_cluster_gap (hx₁ : 0 < x₁) (hmin : ∀ k, x₁ ≤ a k)
    (hcard : (Finset.univ.filter fun k => a k = x₁).card = ρ) (hρ : 2 ≤ ρ) :
    ∃ (i j : Fin n) (g : ℝ), a i = x₁ ∧ a j = x₁ ∧ j ≠ i ∧ 0 < g ∧
      ∀ k ∉ (Finset.univ.filter fun k => a k = x₁), x₁ * (1 + g) < a k := by
  classical
  set S := (Finset.univ.filter fun k => a k = x₁) with hSdef
  have h1 : 1 < S.card := by omega
  obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.1 h1
  have hai : a i = x₁ := (Finset.mem_filter.1 hi).2
  have haj : a j = x₁ := (Finset.mem_filter.1 hj).2
  rcases (Finset.univ \ S).eq_empty_or_nonempty with hE | hE
  · refine ⟨i, j, 1, hai, haj, hij.symm, one_pos, fun k hk => ?_⟩
    have : k ∈ Finset.univ \ S := Finset.mem_sdiff.2 ⟨Finset.mem_univ k, hk⟩
    rw [hE] at this
    exact absurd this (Finset.notMem_empty k)
  obtain ⟨m, hm, hmle⟩ := Finset.exists_min_image (Finset.univ \ S) a hE
  have hmS : m ∉ S := (Finset.mem_sdiff.1 hm).2
  have hmne : a m ≠ x₁ := fun h => hmS (Finset.mem_filter.2 ⟨Finset.mem_univ m, h⟩)
  have hmgt : x₁ < a m := lt_of_le_of_ne (hmin m) (Ne.symm hmne)
  refine ⟨i, j, (a m - x₁) / (2 * x₁), hai, haj, hij.symm, by positivity, fun k hk => ?_⟩
  have hk' : k ∈ Finset.univ \ S := Finset.mem_sdiff.2 ⟨Finset.mem_univ k, hk⟩
  have hmk : a m ≤ a k := hmle k hk'
  have : x₁ * (1 + (a m - x₁) / (2 * x₁)) = x₁ + (a m - x₁) / 2 := by
    field_simp
  rw [this]
  linarith

/-- **`hd0` at the arc's own radius.**  `BranchSupplyGeometry`'s
`hasDerivWithinAt_ftPrincipal_ftTauArcAt_zero` at `aEnd = 0`, with the cluster data
supplied by `exists_ft_cluster_gap`.  The value is the cluster expansion's, `-x₁\cot(π/ρ) + ix₁`. -/
theorem ft_hasDerivWithinAt_ftPrincipal_zero (hn2 : 2 ≤ n) (ha : ∀ k, 0 < a k)
    (hr : 1 ≤ r) (hx₁ : 0 < x₁) (hmin : ∀ k, x₁ ≤ a k)
    (hcard : (Finset.univ.filter fun k => a k = x₁).card = ρ) (hρ : 2 ≤ ρ) :
    HasDerivWithinAt (ftPrincipal (ftTauArc a r (n - 1) x₁))
      (((-(x₁ * Real.cos (π / ρ) / Real.sin (π / ρ)) : ℝ) : ℂ) + ((x₁ : ℝ) : ℂ) * Complex.I)
      (Ici 0) 0 := by
  classical
  obtain ⟨i, j, g, hai, haj, hij, hg, hgap⟩ := exists_ft_cluster_gap hx₁ hmin hcard hρ
  have hS : ∀ k, k ∈ (Finset.univ.filter fun k => a k = x₁) ↔ a k = a i := by
    intro k
    rw [Finset.mem_filter, hai]
    exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ k, h⟩⟩
  have hj' : j ∈ (Finset.univ.filter fun k => a k = x₁) :=
    Finset.mem_filter.2 ⟨Finset.mem_univ j, haj⟩
  have hmin' : ∀ k, a i ≤ a k := by rw [hai]; exact hmin
  have hgap' : ∀ k ∉ (Finset.univ.filter fun k => a k = x₁), a i * (1 + g) < a k := by
    rw [hai]; exact hgap
  have h := hasDerivWithinAt_ftPrincipal_ftTauArcAt_zero (a := a) (r := r) (ρ := ρ)
    hn2 ha hr hS hcard hρ hmin' hj' hij hg hgap' 0
  rw [hai] at h
  rw [ftTauArc_eq_ftTauArcAt]
  exact h

/-- **The branch point's imaginary part along the arc.**  `γ = τe^{iθ}` with `τ` real, so
`Im γ = τ\sin θ` — positive on the open arc and zero at the collision, which is all the
collar's separation binder needs. -/
theorem ftPrincipal_im (τ : ℝ → ℝ) (θ : ℝ) :
    (ftPrincipal τ θ).im = τ θ * Real.sin θ := by
  rw [ftPrincipal, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  simp only [Complex.mul_im, Complex.add_re, Complex.add_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.mul_re, Complex.I_re, Complex.I_im]
  ring

/-- **The branch's endpoint data at the collision, packaged.**  The one-sided derivative,
its nonvanishing, the derivative on a punctured collar, and the Lipschitz bound on `γ'` —
what every endpoint estimate in `ArcPhaseBound` and `BranchSupplyGeometry` asks for, at
the corrected value `ftGammaDerivAt … v 0` rather than at `ftGammaDeriv … 0`, which the
division convention makes junk.

**The value is pinned here and nowhere else.**  The Lipschitz bound arrives at the limit
`v` of `γ'` along the arc and the derivative binder at the cluster expansion's `u`; they
agree because a converging `γ'` makes `v` a one-sided derivative too
(`hasDerivWithinAt_Ici_of_tendsto_deriv`) and a one-sided derivative on `Ici 0` is
unique.  Every consumer takes the package rather than re-deriving that. -/
theorem ft_endpoint_branch_data (hn2 : 2 ≤ n) (ha : ∀ k, 0 < a k) (hr : 1 ≤ r)
    (hx₁ : 0 < x₁) (hmin : ∀ k, x₁ ≤ a k)
    (hcard : (Finset.univ.filter fun k => a k = x₁).card = ρ) (hρ : 2 ≤ ρ) :
    ∃ (v : ℂ) (L b : ℝ), 0 < b ∧ b < π / r ∧ 0 ≤ L ∧
      ftGammaDerivAt a r (n - 1) v 0 ≠ 0 ∧
      HasDerivWithinAt (ftPrincipal (ftTauArc a r (n - 1) x₁))
        (ftGammaDerivAt a r (n - 1) v 0) (Ici 0) 0 ∧
      (∀ θ ∈ Ioc (0 : ℝ) b, HasDerivAt (ftPrincipal (ftTauArc a r (n - 1) x₁))
        (ftGammaDerivAt a r (n - 1) v θ) θ) ∧
      (∀ θ ∈ Icc (0 : ℝ) b,
        ‖ftGammaDerivAt a r (n - 1) v θ - ftGammaDerivAt a r (n - 1) v 0‖ ≤ L * θ) := by
  classical
  have hn : 0 < n := by omega
  have hnr : 2 ≤ n ∨ 2 ≤ r := Or.inl hn2
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have harc : (0 : ℝ) < π / r := by positivity
  have hbranch : ∀ θ ∈ Ioo (0 : ℝ) (π / r), FTBranchAt a r (n - 1) θ :=
    fun θ hθ => ftBranchAt_of_arc_principal hn ha hr hnr hθ
  obtain ⟨hγd, -, -, -⟩ := ft_geometry_group hn ha hr hnr hbranch x₁ 0
  rw [← ftTauArc_eq_ftTauArcAt] at hγd
  -- the endpoint derivative, from the cluster expansion
  set u : ℂ := ((-(x₁ * Real.cos (π / ρ) / Real.sin (π / ρ)) : ℝ) : ℂ)
    + ((x₁ : ℝ) : ℂ) * Complex.I with hu
  have hd0u : HasDerivWithinAt (ftPrincipal (ftTauArc a r (n - 1) x₁)) u (Ici 0) 0 :=
    ft_hasDerivWithinAt_ftPrincipal_zero hn2 ha hr hx₁ hmin hcard hρ
  -- the Lipschitz bound, at the value its own construction produces
  obtain ⟨v, L, bL, hbL, hL, hlipv⟩ :=
    exists_lipschitz_ftGammaDerivAt_of_repeated_min (a := a) (r := r) (ρ := ρ)
      hn ha hr hnr hx₁ hmin hcard hρ
  have hhalf : π / (2 * r) < π / r :=
    div_lt_div_of_pos_left Real.pi_pos hrR (by linarith)
  set b : ℝ := min bL (π / (2 * r)) with hbdef
  have hb0 : 0 < b := lt_min hbL (by positivity)
  have hblt : b < π / r := lt_of_le_of_lt (min_le_right _ _) hhalf
  have hsubarc : Ioo (0 : ℝ) b ⊆ Ioo (0 : ℝ) (π / r) :=
    fun θ hθ => ⟨hθ.1, lt_trans hθ.2 hblt⟩
  -- `γ'` converges to `v`, so `v` is a one-sided derivative too, hence `v = u`
  have hlim : Tendsto (fun x => deriv (ftPrincipal (ftTauArc a r (n - 1) x₁)) x)
      (𝓝[>] (0 : ℝ)) (𝓝 v) := by
    rw [← tendsto_sub_nhds_zero_iff]
    have hbd : ∀ᶠ x in 𝓝[>] (0 : ℝ),
        ‖deriv (ftPrincipal (ftTauArc a r (n - 1) x₁)) x - v‖ ≤ L * x := by
      filter_upwards [Ioo_mem_nhdsGT hb0] with x hx
      have hdx : deriv (ftPrincipal (ftTauArc a r (n - 1) x₁)) x
          = ftGammaDeriv a r (n - 1) x := (hγd x (hsubarc hx)).deriv
      have hle := hlipv x ⟨hx.1.le, le_trans hx.2.le (min_le_left _ _)⟩
      rw [ftGammaDerivAt_of_ne a r (n - 1) v (ne_of_gt hx.1), ftGammaDerivAt_zero] at hle
      rw [hdx]
      exact hle
    have hg : Tendsto (fun x : ℝ => L * x) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have h : Tendsto (fun x : ℝ => L * x) (𝓝[>] (0 : ℝ)) (𝓝 (L * 0)) :=
        ((continuous_const.mul continuous_id).tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
      simpa using h
    exact squeeze_zero_norm' hbd hg
  have hd0v : HasDerivWithinAt (ftPrincipal (ftTauArc a r (n - 1) x₁)) v (Ici 0) 0 :=
    hasDerivWithinAt_Ici_of_tendsto_deriv (s := Ioo (0 : ℝ) (π / r))
      (fun x hx => (hγd x hx).differentiableAt.differentiableWithinAt)
      (hd0u.continuousWithinAt.mono (fun x hx => le_of_lt hx.1)) (Ioo_mem_nhdsGT harc) hlim
  have hvu : v = u := by
    have huniq : UniqueDiffWithinAt ℝ (Ici (0 : ℝ)) 0 := uniqueDiffOn_Ici 0 0 (mem_Ici.2 le_rfl)
    rw [← hd0v.derivWithin huniq, ← hd0u.derivWithin huniq]
  -- the remaining endpoint binders
  have hd0 : HasDerivWithinAt (ftPrincipal (ftTauArc a r (n - 1) x₁))
      (ftGammaDerivAt a r (n - 1) v 0) (Ici 0) 0 := by
    rw [ftGammaDerivAt_zero]; exact hd0v
  have hne0 : ftGammaDerivAt a r (n - 1) v 0 ≠ 0 := by
    rw [ftGammaDerivAt_zero, hvu, hu]
    exact gammaDerivValue_ne_zero hx₁
  have hd : ∀ θ ∈ Ioc (0 : ℝ) b,
      HasDerivAt (ftPrincipal (ftTauArc a r (n - 1) x₁))
        (ftGammaDerivAt a r (n - 1) v θ) θ := by
    intro θ hθ
    rw [ftGammaDerivAt_of_ne a r (n - 1) v (ne_of_gt hθ.1)]
    exact hγd θ ⟨hθ.1, lt_of_le_of_lt hθ.2 hblt⟩
  have hlip : ∀ θ ∈ Icc (0 : ℝ) b,
      ‖ftGammaDerivAt a r (n - 1) v θ - ftGammaDerivAt a r (n - 1) v 0‖ ≤ L * θ :=
    fun θ hθ => hlipv θ ⟨hθ.1, le_trans hθ.2 (min_le_left _ _)⟩
  exact ⟨v, L, b, hb0, hblt, hL, hne0, hd0, hd, hlip⟩


/-- **The collar at the collision, with nothing assumed.**  Every endpoint binder of
`exists_bound_im_logDeriv_ftCofactorAlong_at_collision` discharged at the general pencil in
the `ρ ≥ 2` cell.

The width is returned rather than taken, so the caller assembles the three regions of
`ft_kappaZero_of_collars` at the cuts this hands it. -/
theorem ft_lower_collar (hn2 : 2 ≤ n) (ha : ∀ k, 0 < a k) (hc : c ≠ 0) (hr : 1 ≤ r)
    (hx₁ : 0 < x₁) (hmin : ∀ k, x₁ ≤ a k)
    (hcard : (Finset.univ.filter fun k => a k = x₁).card = ρ) (hρ : 2 ≤ ρ) :
    ∃ b₁ C₁ : ℝ, 0 < b₁ ∧ b₁ ≤ π / r ∧ 0 ≤ C₁ ∧ ∀ θ ∈ Ioo (0 : ℝ) b₁,
      |(ftArcCofactorDeriv a c r x₁ θ
        / ftCofactorAlong (ftRootPoly c a) r (ftBranchZLower a c r (n - 1))
            (ftTauArc a r (n - 1) x₁) θ).im| ≤ C₁ := by
  classical
  have hn : 0 < n := by omega
  have hnr : 2 ≤ n ∨ 2 ≤ r := Or.inl hn2
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have harc : (0 : ℝ) < π / r := by positivity
  have hbranch : ∀ θ ∈ Ioo (0 : ℝ) (π / r), FTBranchAt a r (n - 1) θ :=
    fun θ hθ => ftBranchAt_of_arc_principal hn ha hr hnr hθ
  obtain ⟨hSd, hSc, hS0⟩ := ft_cofactor_group (x₁ := x₁) hn ha hc hr hnr
  have hstate := ft_branch_state_arc (x₁ := x₁) hn ha hc hr hnr
  obtain ⟨v, L, b, hb0, hblt, hL, hne0, hd0, hd, hlip⟩ :=
    ft_endpoint_branch_data (n := n) (r := r) (ρ := ρ) (a := a) (x₁ := x₁)
      hn2 ha hr hx₁ hmin hcard hρ
  have hd0u : HasDerivWithinAt (ftPrincipal (ftTauArc a r (n - 1) x₁))
      (ftGammaDerivAt a r (n - 1) v 0) (Ici 0) 0 := hd0
  have hsubarc : Ioo (0 : ℝ) b ⊆ Ioo (0 : ℝ) (π / r) :=
    fun θ hθ => ⟨hθ.1, lt_trans hθ.2 hblt⟩
  have hτd : ∀ θ ∈ Ioo (0 : ℝ) b,
      HasDerivAt (ftTauArc a r (n - 1) x₁) (ftTauDeriv a r (n - 1) θ) θ := by
    intro θ hθ
    refine (hasDerivAt_ftTau hn ha hr (hsubarc hθ) hbranch).congr_of_eventuallyEq ?_
    filter_upwards [isOpen_Ioo.mem_nhds (hsubarc hθ)] with s hs
    exact ftTauArc_agree a r (n - 1) x₁ hs.1 hs.2
  have hsep : ∀ θ ∈ Ioo (0 : ℝ) b,
      ftPrincipal (ftTauArc a r (n - 1) x₁) θ ≠ ftPrincipal (ftTauArc a r (n - 1) x₁) 0 := by
    intro θ hθ hEq
    have hθπ : θ ∈ Ioo (0 : ℝ) π := ftArc_subset hr (hsubarc hθ)
    have hτpos : 0 < ftTauArc a r (n - 1) x₁ θ := by
      rw [ftTauArc_agree a r (n - 1) x₁ hθ.1 (hsubarc hθ).2]
      exact ftTau_pos (hbranch θ (hsubarc hθ))
    have him := congrArg Complex.im hEq
    rw [ftPrincipal_im, ftPrincipal_im] at him
    have hs0 : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθπ.1 hθπ.2
    have : (0 : ℝ) < ftTauArc a r (n - 1) x₁ θ * Real.sin θ := by positivity
    rw [him, Real.sin_zero, mul_zero] at this
    exact lt_irrefl 0 this
  obtain ⟨b', κ, hb'0, hb'b, hκ0, hbd⟩ :=
    exists_bound_im_logDeriv_ftCofactorAlong_at_collision
      (Q := ftRootPoly c a) (r := r) (z := ftBranchZLower a c r (n - 1))
      (τ := ftTauArc a r (n - 1) x₁) (dγ := ftGammaDerivAt a r (n - 1) v)
      (dS := ftArcCofactorDeriv a c r x₁) (dτ := ftTauDeriv a r (n - 1))
      hr hb0 hL hd0 hd hlip hne0 hτd
      (fun θ hθ => hSd θ (hsubarc hθ)) (fun θ hθ => hstate θ (hsubarc hθ)) hsep
      (hd0u.continuousWithinAt.mono Ioi_subset_Ici_self)
  exact ⟨b', κ, hb'0, le_trans (le_trans hb'b hblt.le) le_rfl, hκ0, hbd⟩

end ForgacsTran
