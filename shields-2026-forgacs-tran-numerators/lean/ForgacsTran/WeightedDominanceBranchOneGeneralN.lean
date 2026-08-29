/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import ForgacsTran.EndpointUpperGeneralN
import ForgacsTran.PencilIndex

/-!
# The `r = 1` upper retained set at every `n`

`EndpointUpperOne` establishes the upper endpoint's root count at `n = 3`, where
the pencil's remaining root can be located exactly: `∏ a_k / L^2`, cleared by
`∏ a_k ≥ 8L^3`.  That route reads the whole root product and does not survive a
fourth zero.

`EndpointUpperGeneralN.two_mul_lt_norm_of_root_endpoint_pi` replaces it at every
`n` with the weaker statement the count actually consumes — every root of the
limiting pencil other than the collision has modulus **strictly greater than**
`2L` — and this module carries that through the same three steps: the circle is
zero-free, the closed disk holds exactly two roots, and the count transports to
the branch pencil at every angle near `π`.

**What is inherited rather than reproved.**  The collision's multiplicity is
already general: `EndpointUpperOne.rootMultiplicity_ftDen_endpoint_pi_eq_two`
holds at `2 ≤ n`, because `Q'' > 0` on the negative axis has nothing to do with
the degree.  So the only thing `n = 3` was ever buying is the separation, and
that is what is swapped here.

The `n = 3` statements are not superseded by this and are not removed: they locate
the remaining root rather than bounding it, which is a sharper fact about that
pencil and the reason the measured clearance ratios sit just above eight.

It is named for `WeightedDominanceBranchOne`, the corner it exists to supply,
rather than for the `EndpointUpper*` family whose subject it shares.  That is
deliberate on both counts: the dependency direction is then readable from the
names, and a name one word from `EndpointUpperGeneralN` — the module it consumes —
is a mis-import that resolves silently to the wrong file.

## Main statements

* `eval_ne_zero_on_sphere_two_mul_endpoint_pi_of_two_le` — the circle `2L` carries
  no zero of the limiting pencil, at every `n ≥ 2`.
* `card_rootsIn_endpoint_pi_eq_two_of_two_le` — the closed disk of radius `2L`
  holds exactly two roots of the limiting pencil, the collision with its
  multiplicity and nothing else.
* `eventually_card_rootsIn_eq_two_near_pi_of_two_le` — the same count for the
  branch pencil at every angle near `π`.
* `eventually_upper_retained_one_of_two_le` — **the retained upper set at `r = 1`,
  every `n ≥ 2`**: the principal pair is exactly the pencil's zero set in the disk
  of radius `2L`, and both members are simple.  This is `n_1 = 0`.

## References

* `../../shields-2026-forgacs-tran-numerators.tex`, `thm:weighted-dominance`,
  `eq:principal-pair`, `eq:ab-def`, `subsec:proof`.

## Tags

upper endpoint, retained set, root count, double root, separating circle
-/

namespace ForgacsTran

open Real Set Filter Polynomial Complex
open scoped Topology

/-- **The circle of radius `2L` carries no zero of the endpoint pencil, at every
`n ≥ 2`.**  The collision sits at modulus `L` and every other root strictly beyond
`2L`, so nothing is left on the circle itself.  This is the side condition
`card_rootsIn_ftDen_eventuallyEq_of_tendsto` needs, at the same named radius the
count below uses. -/
theorem eval_ne_zero_on_sphere_two_mul_endpoint_pi_of_two_le {n : ℕ} {a : Fin n → ℝ}
    {c : ℝ} (hn2 : 2 ≤ n) (ha : ∀ k, 0 < a k) (hc : 0 < c) {L : ℝ} (hL : 0 < L)
    (hE : (ftCriticalReal (ftRootPolyReal c a) 1).eval (-L) = 0) :
    ∀ t ∈ Metric.sphere (0 : ℂ) (2 * L),
      (ftDen (ftRootPoly c a) 1
        ((-((ftRootPolyReal c a).eval (-L)) / (-L) : ℝ) : ℂ)).eval t ≠ 0 := by
  intro t ht hzero
  have hnt : ‖t‖ = 2 * L := by
    simpa [Complex.dist_eq, sub_zero] using Metric.mem_sphere.1 ht
  by_cases hne : t = ((-L : ℝ) : ℂ)
  · rw [hne, Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_of_pos hL] at hnt
    linarith
  · have hfar :=
      two_mul_lt_norm_of_root_endpoint_pi (by omega : 0 < n) ha hc hL hE hzero hne
    rw [hnt] at hfar
    linarith

/-- **The count inside the circle of radius `2L` is two, at every `n ≥ 2`**: the
collision, with its multiplicity, and nothing else.  That is `n_1 = r - 2 = 0`
made concrete — the retained upper cluster at `r = 1` is the principal pair alone.

The multiplicity is `rootMultiplicity_ftDen_endpoint_pi_eq_two`, which was already
general; what is new is that the filter of roots inside the disk collapses to the
collision at every `n` rather than only where the last root can be located. -/
theorem card_rootsIn_endpoint_pi_eq_two_of_two_le {n : ℕ} {a : Fin n → ℝ} {c : ℝ}
    (hn2 : 2 ≤ n) (ha : ∀ k, 0 < a k) (hc : 0 < c) {L : ℝ} (hL : 0 < L)
    (hE : (ftCriticalReal (ftRootPolyReal c a) 1).eval (-L) = 0) :
    (Shields.rootsIn (ftDen (ftRootPoly c a) 1
        ((-((ftRootPolyReal c a).eval (-L)) / (-L) : ℝ) : ℂ)) 0 (2 * L)).card = 2 := by
  classical
  set p : Polynomial ℂ := ftDen (ftRootPoly c a) 1
    ((-((ftRootPolyReal c a).eval (-L)) / (-L) : ℝ) : ℂ) with hpdef
  have hmult : p.roots.count ((-L : ℝ) : ℂ) = 2 := by
    rw [Polynomial.count_roots]
    exact rootMultiplicity_ftDen_endpoint_pi_eq_two hn2 ha hc hL hE
  have hfil : p.roots.filter (fun r => dist r 0 < 2 * L)
      = p.roots.filter (fun r => r = ((-L : ℝ) : ℂ)) := by
    refine Multiset.filter_congr fun r hr => ?_
    constructor
    · intro hlt
      by_contra hne
      have hroot : p.eval r = 0 := (Polynomial.mem_roots'.1 hr).2
      rw [hpdef] at hroot
      have hfar :=
        two_mul_lt_norm_of_root_endpoint_pi (by omega : 0 < n) ha hc hL hE hroot hne
      rw [dist_zero_right] at hlt
      linarith
    · intro heq
      rw [heq, dist_zero_right, Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_of_pos hL]
      linarith
  rw [Shields.rootsIn, hfil, Multiset.filter_eq', hmult, Multiset.card_replicate]

/-- **The separating radius near the upper endpoint at `r = 1`, every `n ≥ 2`.**  On
any filter along which the branch radius tends to `L`, the circle of radius `2L`
eventually contains exactly two zeros of the pencil.

The limit is taken at a named `L` rather than through an existential: every
statement here is about the pencil *at that value*, and a wrapper hiding the
constant is unusable exactly where the constant is what the rest of the argument
names. -/
theorem eventually_card_rootsIn_eq_two_near_pi_of_two_le {n : ℕ} {a : Fin n → ℝ}
    {c : ℝ} {l : ℕ} (hn2 : 2 ≤ n) (ha : ∀ k, 0 < a k) (hc : 0 < c) {L : ℝ} {S : Set ℝ}
    (hL : 0 < L)
    (hmem : ∀ᶠ θ in nhdsWithin Real.pi S, θ ∈ Set.Ioo 0 Real.pi ∧ FTBranchAt a 1 l θ)
    (hτ : Filter.Tendsto (ftTau a 1 l) (nhdsWithin Real.pi S) (nhds L))
    (hE : (ftCriticalReal (ftRootPolyReal c a) 1).eval (-L) = 0) :
    ∀ᶠ θ in nhdsWithin Real.pi S,
      (Shields.rootsIn (ftDen (ftRootPoly c a) 1 ((ftBranchZ a c 1 l θ : ℝ) : ℂ))
        0 (2 * L)).card = 2 := by
  have hz := tendsto_ftBranchZ_upper_pi (c := c) ha hL hmem hτ
  rw [pow_one] at hz
  have hzC : Filter.Tendsto (fun θ => ((ftBranchZ a c 1 l θ : ℝ) : ℂ))
      (nhdsWithin Real.pi S)
      (nhds ((-((ftRootPolyReal c a).eval (-L)) / (-L) : ℝ) : ℂ)) :=
    (Complex.continuous_ofReal.tendsto _).comp hz
  have hcount := card_rootsIn_ftDen_eventuallyEq_of_tendsto (Q := ftRootPoly c a) (r := 1)
    (by linarith : (0 : ℝ) < 2 * L) hzC
    (eval_ne_zero_on_sphere_two_mul_endpoint_pi_of_two_le hn2 ha hc hL hE)
  filter_upwards [hcount] with θ hθ
  rw [hθ]
  exact card_rootsIn_endpoint_pi_eq_two_of_two_le hn2 ha hc hL hE

/-- **The retained upper set at `r = 1`, every `n ≥ 2`.**  The pair `{t_+, t_-}` is
exactly the zero set of the pencil in the closed disk of radius `2L`, and both
members are simple.

`eventually_card_rootsIn_eq_two_near_pi_of_two_le` supplies the count with
multiplicity; `EndpointSeparation.simple_and_complete_of_count` turns it into
simplicity and completeness once the pair is exhibited inside and the circle is
zero-free.  The circle's zero-freeness is at the BRANCH pencil, which is
`eventually_eval_ftDen_ne_zero_on_sphere_of_tendsto` rather than the limiting
statement it is proved from.

**The window is punctured and must stay so.**  Simplicity holds at every `δ > 0`
and degenerates in the limit: `∂_tD(t_+)` vanishes **linearly** as `δ → 0`, because
the pair collides at `-L` where the limiting pencil has its double root.  The
closed-window form — at `δ = 0` — is FALSE.  It is the same collision that makes
the principal amplitude diverge, so the simplicity clause and the amplitude floor
cannot both be extended to the endpoint.

**The lower endpoint's statement is this one again** —
`RhoOneEndpointFactorization.eventually_lower_retained_rho_one`, at a free `r`, the
critical point `t_a` for `x₁`, the angle `δ` for `π - δ`, and its own separating
radius.  Neither names the shape, because the two modules are siblings with no shared
home below `EndpointSeparation` — whose `simple_and_complete_of_count` both of them
consume, and which is where a name for it would go. -/
theorem eventually_upper_retained_one_of_two_le {n : ℕ} {a : Fin n → ℝ} {c x₁ : ℝ}
    (hn2 : 2 ≤ n) (ha : ∀ k, 0 < a k) (hc : 0 < c) {L : ℝ} (hL : 0 < L)
    (hE : (ftCriticalReal (ftRootPolyReal c a) 1).eval (-L) = 0)
    (hτ : Tendsto (ftTau a 1 (n - 1)) (𝓝[<] π) (𝓝 L))
    (hz : Tendsto (ftBranchZ a c 1 (n - 1)) (𝓝[<] π)
      (𝓝 (-(ftRootPolyReal c a).eval (-L) / (-L)))) :
    ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      0 < ftTauArc a 1 (n - 1) x₁ (π - δ) ∧
      ftTauArc a 1 (n - 1) x₁ (π - δ) ≤ 3 * L / 2 ∧
      (ftDen (ftRootPoly c a) 1 ((ftBranchZ a c 1 (n - 1) (π - δ) : ℝ) : ℂ)).eval
        (ftPrincipal (ftTauArc a 1 (n - 1) x₁) (π - δ)) = 0 ∧
      ftPrincipal (ftTauArc a 1 (n - 1) x₁) (π - δ) ≠
        ((ftTauArc a 1 (n - 1) x₁ (π - δ) : ℝ) : ℂ) * Complex.exp (-((π - δ : ℝ) : ℂ) * I) ∧
      (∀ w ∈ ({ftPrincipal (ftTauArc a 1 (n - 1) x₁) (π - δ),
          ((ftTauArc a 1 (n - 1) x₁ (π - δ) : ℝ) : ℂ) *
            Complex.exp (-((π - δ : ℝ) : ℂ) * I)} : Finset ℂ),
        (ftDen (ftRootPoly c a) 1 ((ftBranchZ a c 1 (n - 1) (π - δ) : ℝ) : ℂ)).eval w = 0 ∧
          ‖w‖ < 2 * L ∧
          (derivative (ftDen (ftRootPoly c a) 1
            ((ftBranchZ a c 1 (n - 1) (π - δ) : ℝ) : ℂ))).eval w ≠ 0) ∧
      (∀ t : ℂ, ‖t‖ ≤ 2 * L →
        (ftDen (ftRootPoly c a) 1 ((ftBranchZ a c 1 (n - 1) (π - δ) : ℝ) : ℂ)).eval t = 0 →
        t ∈ ({ftPrincipal (ftTauArc a 1 (n - 1) x₁) (π - δ),
          ((ftTauArc a 1 (n - 1) x₁ (π - δ) : ℝ) : ℂ) *
            Complex.exp (-((π - δ : ℝ) : ℂ) * I)} : Finset ℂ)) := by
  classical
  have hcast : π / ((1 : ℕ) : ℝ) = π := pi_div_natCast_one
  have harc : ∀ᶠ δ in 𝓝[>] (0 : ℝ), π - δ ∈ Ioo 0 (π / ((1 : ℕ) : ℝ)) := by
    filter_upwards [Ioo_mem_nhdsGT pi_pos] with δ hδπ
    rw [hcast]
    exact ⟨by linarith [hδπ.2], by linarith [hδπ.1]⟩
  have hagree : ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      ftTauArc a 1 (n - 1) x₁ (π - δ) = ftTau a 1 (n - 1) (π - δ) := by
    filter_upwards [harc] with δ hδ
    exact ftTauArc_agree a 1 (n - 1) x₁ hδ.1 hδ.2
  obtain ⟨hrootA, hposA⟩ :=
    ft_branch_root_and_pos (a := a) (r := 1) c (by omega) ha le_rfl (Or.inl hn2)
  have hTsmall : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ftTau a 1 (n - 1) (π - δ) < 3 * L / 2 := by
    filter_upwards [Metric.tendsto_nhds.mp (hτ.comp tendsto_sub_nhdsGT_zero_nhdsLT)
      (L / 2) (by linarith)] with δ hδ
    simp only [Function.comp_apply, Real.dist_eq, abs_lt] at hδ
    linarith [hδ.2]
  have hsphere : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∀ t : ℂ, ‖t‖ = 2 * L →
      (ftDen (ftRootPoly c a) 1 ((ftBranchZ a c 1 (n - 1) (π - δ) : ℝ) : ℂ)).eval t ≠ 0 := by
    refine eventually_eval_ftDen_ne_zero_on_sphere_of_tendsto
      ((Complex.continuous_ofReal.tendsto _).comp (hz.comp tendsto_sub_nhdsGT_zero_nhdsLT))
      (by positivity) (fun t ht => ?_)
    exact eval_ne_zero_on_sphere_two_mul_endpoint_pi_of_two_le hn2 ha hc hL hE t
      (by simpa [Complex.dist_eq, sub_zero] using ht)
  have hcountθ : ∀ᶠ θ in 𝓝[<] π,
      (Shields.rootsIn (ftDen (ftRootPoly c a) 1
        ((ftBranchZ a c 1 (n - 1) θ : ℝ) : ℂ)) 0 (2 * L)).card = 2 := by
    refine eventually_card_rootsIn_eq_two_near_pi_of_two_le hn2 ha hc hL ?_ hτ hE
    filter_upwards [Ioo_mem_nhdsLT pi_pos] with θ hθ
    refine ⟨hθ, ftBranchAt_of_arc_principal (by omega) ha le_rfl (Or.inl hn2) ?_⟩
    rw [hcast]; exact hθ
  have hcount := (tendsto_sub_nhdsGT_zero_nhdsLT (b := π)).eventually hcountθ
  filter_upwards [harc, hagree, hTsmall, hsphere, hcount] with δ hδarc hδag hδsm hδsp hδct
  have hπarc : (π - δ) ∈ Ioo (0 : ℝ) π := by
    refine ⟨hδarc.1, ?_⟩
    have h := hδarc.2; rwa [hcast] at h
  have hTpos : 0 < ftTauArc a 1 (n - 1) x₁ (π - δ) := by rw [hδag]; exact hposA _ hδarc
  have hTle : ftTauArc a 1 (n - 1) x₁ (π - δ) ≤ 3 * L / 2 := by rw [hδag]; exact hδsm.le
  have hPeq : ftPrincipal (ftTauArc a 1 (n - 1) x₁) (π - δ)
      = ftPrincipal (ftTau a 1 (n - 1)) (π - δ) := by
    rw [ftPrincipal, ftPrincipal, hδag]
  have hProot : (ftDen (ftRootPoly c a) 1 ((ftBranchZ a c 1 (n - 1) (π - δ) : ℝ) : ℂ)).eval
      (ftPrincipal (ftTauArc a 1 (n - 1) x₁) (π - δ)) = 0 := by
    rw [hPeq]; exact hrootA _ hδarc
  have hCjeq : ((ftTauArc a 1 (n - 1) x₁ (π - δ) : ℝ) : ℂ) * Complex.exp (-((π - δ : ℝ) : ℂ) * I)
      = (starRingEnd ℂ) (ftPrincipal (ftTauArc a 1 (n - 1) x₁) (π - δ)) :=
    (conj_ftPrincipal' (ftTauArc a 1 (n - 1) x₁) (π - δ)).symm
  have hne : ftPrincipal (ftTauArc a 1 (n - 1) x₁) (π - δ) ≠
      ((ftTauArc a 1 (n - 1) x₁ (π - δ) : ℝ) : ℂ) * Complex.exp (-((π - δ : ℝ) : ℂ) * I) := by
    rw [hCjeq]
    exact ftPrincipal_ne_conj_of_pos hTpos hπarc
  have hCjroot : (ftDen (ftRootPoly c a) 1 ((ftBranchZ a c 1 (n - 1) (π - δ) : ℝ) : ℂ)).eval
      (((ftTauArc a 1 (n - 1) x₁ (π - δ) : ℝ) : ℂ) * Complex.exp (-((π - δ : ℝ) : ℂ) * I)) = 0 := by
    rw [hCjeq]
    exact ftDen_eval_conj_eq_zero (hasRealCoeffs_ftRootPoly c a) hProot
  have hPnorm : ‖ftPrincipal (ftTauArc a 1 (n - 1) x₁) (π - δ)‖ = ftTauArc a 1 (n - 1) x₁ (π - δ) :=
    norm_ftPrincipal_eq hTpos
  have hCjnorm : ‖((ftTauArc a 1 (n - 1) x₁ (π - δ) : ℝ) : ℂ) *
      Complex.exp (-((π - δ : ℝ) : ℂ) * I)‖ = ftTauArc a 1 (n - 1) x₁ (π - δ) := by
    rw [hCjeq]; simpa using hPnorm
  have hlt : ftTauArc a 1 (n - 1) x₁ (π - δ) < 2 * L := by linarith
  have hDne : ftDen (ftRootPoly c a) 1 ((ftBranchZ a c 1 (n - 1) (π - δ) : ℝ) : ℂ) ≠ 0 :=
    ftDen_one_ne_zero_of_real hc.ne' ha _
  have hTcard : (({ftPrincipal (ftTauArc a 1 (n - 1) x₁) (π - δ),
      ((ftTauArc a 1 (n - 1) x₁ (π - δ) : ℝ) : ℂ) *
        Complex.exp (-((π - δ : ℝ) : ℂ) * I)} : Finset ℂ)).card = 2 := by
    rw [Finset.card_insert_of_notMem (by simpa using hne), Finset.card_singleton]
  have hTmem : ∀ w ∈ ({ftPrincipal (ftTauArc a 1 (n - 1) x₁) (π - δ),
      ((ftTauArc a 1 (n - 1) x₁ (π - δ) : ℝ) : ℂ) *
        Complex.exp (-((π - δ : ℝ) : ℂ) * I)} : Finset ℂ),
      (ftDen (ftRootPoly c a) 1 ((ftBranchZ a c 1 (n - 1) (π - δ) : ℝ) : ℂ)).eval w = 0 ∧
        ‖w‖ < 2 * L := by
    intro w hw
    rcases Finset.mem_insert.1 hw with rfl | hw
    · exact ⟨hProot, by rw [hPnorm]; exact hlt⟩
    · rw [Finset.mem_singleton] at hw
      subst hw
      exact ⟨hCjroot, by rw [hCjnorm]; exact hlt⟩
  obtain ⟨hsimp, huniq⟩ :=
    simple_and_complete_of_count hDne hδct (fun t ht => hδsp t ht) hTcard hTmem
  exact ⟨hTpos, hTle, hProot, hne,
    fun w hw => ⟨(hTmem w hw).1, (hTmem w hw).2, hsimp w hw⟩, huniq⟩

end ForgacsTran
