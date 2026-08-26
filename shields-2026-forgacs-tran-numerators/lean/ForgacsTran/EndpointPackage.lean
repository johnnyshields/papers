/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib
import ForgacsTran.EndpointBranch
import ForgacsTran.EndpointSeparation
import ForgacsTran.DominanceFT
import ForgacsTran.FTGeometryAssembly
import ForgacsTran.FTMinModulus.RealCritical
import ForgacsTran.FTGeometryCone

/-!
# The lower-endpoint package

`EndpointBranch` supplies the analysis: the blow-up limit of the branch radius,
the chart `g - z_e = w^k` and its local inverse, and the cluster branches.  This
module states what `DominanceFT.weighted_dominance_of_branch_any_multiplicity_at`
asks for at the lower endpoint, at `2 ≤ ρ`, in that theorem's own binder shapes.

**The datum is one number reached three ways, and they agree.**  The squeeze gives
`τ'(0⁺) = -s₀` with `s₀ = x₁\cot(π/ρ)`; the arc contributes `i·x₁`; so
`γ_e = ftPrincipal'(0) = -s₀ + ix₁`.  That is `clusterAlpha x₁ ρ 0` on the nose —
`EndpointBranch.clusterAlpha_eq_blowup` — whose real part is the squeeze's limit
and whose imaginary part is `clusterAlpha_im`.  And `arg_blowup_root` is the same
constant a third way, as the root of the blown-up angle-sum equation.  Nothing is
matched by hand anywhere in the chain.

**Everything is handed back as a value, never an existential.**  `te₀ = ↑x₁` and
`γe₀ = clusterAlpha x₁ ρ 0` are literal terms, and `τ`, `z` are the total functions
`ftTauLower`, `ftBranchZLower`.  A constant that is existential in a producer and a
parameter in its consumer composes by being carried as an inert hypothesis, and
that type-checks.

**`ρ = 1` is not this module's case and must not be folded into it.**
`clusterAlpha` divides by `\sin(π/ρ)`, which is `0` at `ρ = 1`, so a supplier
written once for every `ρ` returns a wrong *finite* value there with nothing
failing — `EndpointBranch.clusterAlpha_one_eq_zero`.  The `ρ = 1` datum is
`i·t_a` at `t_e = t_a` strictly inside the first gap, and it belongs to a
physically separate producer.

## Main statements

* `ftTauLower`, `ftBranchZLower` — the branch data extended to the closed endpoint
  interval by their limits, which is what `hagree` and `hγ0₀` need.
* `hasDerivWithinAt_ftPrincipal_ftTauLower` — `hγd₀`.
* `endpoint_package_of_two_le_rho` — the six endpoint-factorization fields plus
  `hagree`.
* `endpoint_retained_partial_of_two_le_rho` — the four retained-cluster fields
  that are facts about the branch rather than about the cluster's enumeration.
* `rootMultiplicity_ftRootPoly`, `exists_z_endpoint_order_of_two_le_rho` —
  `eq:z-endpoint-order` with the exponent identified as `ρ`.
* `ftClusterParam`, `exists_tendsto_ftClusterParam_div` — the chart parameter
  along the branch, `v(δ)^ρ = z(δ)` and `v(δ)/δ → L > 0`.
* `tendsto_cluster_slope` — the cluster member's slope in the angular parameter.
* `ftClusterParam_pos`, `tendsto_ftClusterParam` — the chart parameter is positive
  on the arc and vanishes at the endpoint.
* `exists_cluster_family_of_two_le_rho` — **the lower cluster assembled**: the `ρ`
  members `ψ(ζ_j·v(δ))` are zeros of the pencil at the branch's own spectral
  parameter, are distinct, and enter `x_1` with slopes `γ_e·ζ_j·L`.
* `exists_z_window_of_two_le_rho` — the branch's spectral parameter stays inside
  the separating window, so `EndpointSeparation` applies along the branch.
* `exists_endpoint_contour_window_of_two_le_rho` — `hCbd₀`, and the zero-free
  circle `huniq₀` counts in.
* `ftClusterSet` — the `ρ` members at one angle, as a finite set.
* `exists_retained_set_of_two_le_rho` — **the lower retained set**, with `hroot₀`,
  `haR₀`, `huniq₀`, `hsimple₀` and its cardinality `ρ`, together with the chart and
  the slopes the index identification needs.
* `tendsto_ftPrincipal_slope_of_two_le_rho`,
  `exists_principal_pair_cluster_indices_of_two_le_rho` — **which members the
  principal pair is**: two distinct indices `j_p`, `j_c`, with the retained set's
  five fields on the same window.
* `exists_lower_cluster_enumeration_of_two_le_rho` — `hginj₀`, `hgmem₀`, `hgcard₀`,
  with the point's chart index and the manuscript's index returned separately.
* `tendsto_eval_div_pow_of_slope` — a polynomial's leading behavior along a point
  entering `t_e` linearly.
* `exists_residue_asymptotics_of_slopes` — `hBj₀`, `hBp₀`, `hEj₀`, `hEp₀`, with
  `c_B` and `c_Q` the nonvanishing cofactors at `x_1` rather than assumed constants.
* `tendsto_norm_sub_one_div_of_slope` — the modulus of a point entering `1`
  linearly enters at the real part of its slope.
* `exists_linear_gap_of_slopes` — `hgapin₀`, `eq:endpoint-linear-gap` from the
  slopes alone, with the rate positive exactly because `idx₀` avoids the principal
  pair's own labels `0` and `1`.
* `exists_upper_z_window` — the branch clears `ftUpperWindow` at the upper
  endpoint, which is what makes `EndpointSeparation`'s upper circle usable, and
  needs `2 ≤ r` because at `r = 1` the spectral parameter is bounded.

## Implementation notes

Sorry-free.

## References

* `../shields-2026-forgacs-tran-numerators.tex`, «Forgács--Tran geometry and
  endpoint separation» and «Weighted dominance» — `lem:principal-endpoint-regularity`,
  `eq:z-endpoint-order`, `eq:lower-cluster-expansion`, `thm:weighted-dominance`.
* `Forgacs2017RationalDenominator`, Proposition 3.

## Tags

lower endpoint, cluster, dominance, principal branch
-/

set_option linter.style.longFile 1700

namespace ForgacsTran

open Complex Filter Topology Polynomial
open scoped Topology

/-- The branch radius extended to the closed endpoint interval by its limit. -/
noncomputable def ftTauLower {n : ℕ} (a : Fin n → ℝ) (r l : ℕ) (x₁ : ℝ) : ℝ → ℝ :=
  fun θ => if 0 < θ then ftTau a r l θ else x₁

theorem ftTauLower_agree {n : ℕ} (a : Fin n → ℝ) (r l : ℕ) (x₁ : ℝ) {θ : ℝ} (hθ : 0 < θ) :
    ftTauLower a r l x₁ θ = ftTau a r l θ := by
  rw [ftTauLower, if_pos hθ]

@[simp] theorem ftTauLower_zero {n : ℕ} (a : Fin n → ℝ) (r l : ℕ) (x₁ : ℝ) :
    ftTauLower a r l x₁ 0 = x₁ := by
  rw [ftTauLower, if_neg (lt_irrefl 0)]

@[simp] theorem ftPrincipal_ftTauLower_zero {n : ℕ} (a : Fin n → ℝ) (r l : ℕ) (x₁ : ℝ) :
    ftPrincipal (ftTauLower a r l x₁) 0 = ((x₁ : ℝ) : ℂ) := by
  rw [ftPrincipal, ftTauLower_zero]
  simp

/-- **`hγd₀` at the lower endpoint, `2 ≤ ρ`.**  The principal branch enters the
repeated smallest zero with derivative `clusterAlpha x₁ ρ 0`.  The radius supplies
the real part through `tendsto_ftTau_blowup` and the arc supplies `ix₁` through
`tendsto_expI_slope`. -/
theorem hasDerivWithinAt_ftPrincipal_ftTauLower {n r ρ : ℕ} {a : Fin n → ℝ} {x₁ : ℝ}
    (hn : 0 < n) (ha : ∀ k, 0 < a k) (hr : 1 ≤ r) (hnr : 2 ≤ n ∨ 2 ≤ r)
    (hx₁ : 0 < x₁) (hmin : ∀ k, x₁ ≤ a k)
    (hcard : (Finset.univ.filter fun k => a k = x₁).card = ρ) (hρ : 2 ≤ ρ) :
    HasDerivWithinAt (fun δ : ℝ => ftPrincipal (ftTauLower a r (n - 1) x₁) δ)
      (clusterAlpha x₁ ρ 0) (Set.Ici 0) 0 := by
  have hπ := Real.pi_pos
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  set s₀ : ℝ := x₁ * (Real.cos (Real.pi / ρ) / Real.sin (Real.pi / ρ)) with hs₀
  -- the radius half
  have hreal : Tendsto (fun δ : ℝ => (ftTau a r (n - 1) δ - x₁) / δ) (𝓝[>] (0 : ℝ))
      (𝓝 (-s₀)) := by
    have h := (tendsto_ftTau_blowup hn ha hr hnr hx₁ hmin hcard hρ).neg
    refine h.congr fun δ => ?_
    rw [← neg_div, neg_sub]
  have hrealC : Tendsto (fun δ : ℝ => (((ftTau a r (n - 1) δ - x₁) / δ : ℝ) : ℂ))
      (𝓝[>] (0 : ℝ)) (𝓝 (((-s₀ : ℝ) : ℂ))) :=
    (Complex.continuous_ofReal.tendsto _).comp hreal
  -- the arc half
  have hexpc : Tendsto (fun δ : ℝ => Complex.exp (((δ : ℝ) : ℂ) * Complex.I))
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    have hc : Continuous fun δ : ℝ => Complex.exp (((δ : ℝ) : ℂ) * Complex.I) :=
      Complex.continuous_exp.comp (Complex.continuous_ofReal.mul continuous_const)
    have h : Tendsto (fun δ : ℝ => Complex.exp (((δ : ℝ) : ℂ) * Complex.I))
        (𝓝[>] (0 : ℝ)) (𝓝 (Complex.exp ((((0 : ℝ)) : ℂ) * Complex.I))) :=
      (hc.tendsto 0).mono_left nhdsWithin_le_nhds
    simpa using h
  have hsub : 𝓝[>] (0 : ℝ) ≤ 𝓝[≠] (0 : ℝ) := nhdsWithin_mono _ fun x hx => ne_of_gt hx
  have hcomb := (hrealC.mul hexpc).add
    ((tendsto_expI_slope.mono_left hsub).const_mul ((x₁ : ℝ) : ℂ))
  have hval : ((-s₀ : ℝ) : ℂ) * 1 + ((x₁ : ℝ) : ℂ) * Complex.I = clusterAlpha x₁ ρ 0 := by
    rw [clusterAlpha_eq_blowup hρ, hs₀, mul_one]
  rw [hval] at hcomb
  have hdiff : (Set.Ici (0 : ℝ)) \ {(0 : ℝ)} = Set.Ioi (0 : ℝ) := by
    ext x
    simp only [Set.mem_sdiff, Set.mem_Ici, Set.mem_singleton_iff, Set.mem_Ioi]
    constructor
    · rintro ⟨hx, hne⟩
      exact lt_of_le_of_ne hx (Ne.symm hne)
    · intro hx
      exact ⟨le_of_lt hx, ne_of_gt hx⟩
  rw [hasDerivWithinAt_iff_tendsto_slope, hdiff]
  refine hcomb.congr' ?_
  filter_upwards [self_mem_nhdsWithin,
    Ioo_mem_nhdsGT (show (0 : ℝ) < Real.pi / r by positivity)] with δ hδ hδarc
  have hδ0 : (0 : ℝ) < δ := hδ
  have hδC : ((δ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hδ0
  simp only [slope, vsub_eq_sub, sub_zero, Complex.real_smul, Complex.ofReal_inv]
  rw [ftPrincipal_ftTauLower_zero, ftPrincipal, ftTauLower_agree a r (n - 1) x₁ hδ0]
  push_cast
  field_simp
  ring


/-- The spectral parameter extended to the closed endpoint interval by its limit.
At `2 ≤ ρ` the endpoint value is `g(x_1) = -Q(x_1)/x_1^r = 0`, because `x_1` is a
zero of `Q`. -/
noncomputable def ftBranchZLower {n : ℕ} (a : Fin n → ℝ) (c : ℝ) (r l : ℕ) : ℝ → ℝ :=
  fun θ => if 0 < θ then ftBranchZ a c r l θ else 0

theorem ftBranchZLower_agree {n : ℕ} (a : Fin n → ℝ) (c : ℝ) (r l : ℕ) {θ : ℝ} (hθ : 0 < θ) :
    ftBranchZLower a c r l θ = ftBranchZ a c r l θ := by
  rw [ftBranchZLower, if_pos hθ]

@[simp] theorem ftBranchZLower_zero {n : ℕ} (a : Fin n → ℝ) (c : ℝ) (r l : ℕ) :
    ftBranchZLower a c r l 0 = 0 := by
  rw [ftBranchZLower, if_neg (lt_irrefl 0)]

/-- **The endpoint-factorization group of
`weighted_dominance_of_branch_any_multiplicity_at`, at `2 ≤ ρ`.**  All six fields,
at the explicit `te₀ = x_1` and `γe₀ = clusterAlpha x₁ ρ 0` — no existential, so
nothing here can compose by being carried as a hypothesis.  The seventh component
is `hagree`, which is what ties the abstract `τ` of the consumer to the branch. -/
theorem endpoint_package_of_two_le_rho {n r ρ : ℕ} {a : Fin n → ℝ} {c x₁ : ℝ}
    (hn : 0 < n) (ha : ∀ k, 0 < a k) (hc : 0 < c) (hr : 1 ≤ r) (hnr : 2 ≤ n ∨ 2 ≤ r)
    (hx₁ : 0 < x₁) (hmin : ∀ k, x₁ ≤ a k)
    (hcard : (Finset.univ.filter fun k => a k = x₁).card = ρ) (hρ : 2 ≤ ρ) :
    (∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / r),
        ftTauLower a r (n - 1) x₁ θ = ftTau a r (n - 1) θ)
      ∧ ((x₁ : ℝ) : ℂ) ≠ 0
      ∧ clusterAlpha x₁ ρ 0 ≠ 0
      ∧ ftPrincipal (ftTauLower a r (n - 1) x₁) 0 = ((x₁ : ℝ) : ℂ)
      ∧ HasDerivWithinAt (fun δ : ℝ => ftPrincipal (ftTauLower a r (n - 1) x₁) δ)
          (clusterAlpha x₁ ρ 0) (Set.Ici 0) 0
      ∧ 1 ≤ (ftDen (ftRootPoly c a) r
          ((ftBranchZLower a c r (n - 1) 0 : ℝ) : ℂ)).rootMultiplicity ((x₁ : ℝ) : ℂ)
      ∧ (∀ᶠ δ in 𝓝[>] (0 : ℝ),
          (ftDen (ftRootPoly c a) r ((ftBranchZLower a c r (n - 1) δ : ℝ) : ℂ)).eval
            (ftPrincipal (ftTauLower a r (n - 1) x₁) δ) = 0) := by
  classical
  have hπ := Real.pi_pos
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  -- a zero of `Q` sits at `x₁`
  have hne : (Finset.univ.filter fun k => a k = x₁).Nonempty := by
    rw [← Finset.card_pos, hcard]; omega
  obtain ⟨i, hi⟩ := hne
  have hix : a i = x₁ := (Finset.mem_filter.1 hi).2
  have hQ0 : (ftRootPoly c a).eval ((x₁ : ℝ) : ℂ) = 0 := by
    rw [eval_ftRootPoly]
    refine mul_eq_zero.2 (Or.inr (Finset.prod_eq_zero (Finset.mem_univ i) ?_))
    rw [hix]
    ring
  have hpne : ftRootPoly c a ≠ 0 := by
    intro h
    have h0 : (ftRootPoly c a).eval 0 = ((c * ∏ k, a k : ℝ) : ℂ) := by
      rw [eval_ftRootPoly]; push_cast; simp
    rw [h] at h0
    simp only [Polynomial.eval_zero] at h0
    have : (c * ∏ k, a k) ≠ 0 :=
      ne_of_gt (mul_pos hc (Finset.prod_pos fun k _ => ha k))
    exact this (by exact_mod_cast h0.symm)
  refine ⟨fun θ hθ => ftTauLower_agree a r (n - 1) x₁ hθ.1, ?_,
    clusterAlpha_ne_zero hx₁ hρ 0, ftPrincipal_ftTauLower_zero a r (n - 1) x₁,
    hasDerivWithinAt_ftPrincipal_ftTauLower hn ha hr hnr hx₁ hmin hcard hρ, ?_, ?_⟩
  · exact_mod_cast ne_of_gt hx₁
  · rw [ftBranchZLower_zero]
    have hden : ftDen (ftRootPoly c a) r (((0 : ℝ) : ℂ)) = ftRootPoly c a := by
      rw [ftDen]; simp
    rw [hden]
    exact (Polynomial.rootMultiplicity_pos hpne).2 hQ0
  · filter_upwards [self_mem_nhdsWithin,
      Ioo_mem_nhdsGT (show (0 : ℝ) < Real.pi / r by positivity)] with δ hδ hδarc
    have hδ0 : (0 : ℝ) < δ := hδ
    rw [ftBranchZLower_agree a c r (n - 1) hδ0]
    have hprin : ftPrincipal (ftTauLower a r (n - 1) x₁) δ
        = ftPrincipal (ftTau a r (n - 1)) δ := by
      rw [ftPrincipal, ftPrincipal, ftTauLower_agree a r (n - 1) x₁ hδ0]
    rw [hprin]
    exact ftDen_eval_ftPrincipal_ftBranchZ c ha (ftArc_subset hr hδarc)
      (ftBranchAt_of_arc_principal hn ha hr hnr hδarc)


/-- **Four fields of the lower retained-cluster group, at `2 ≤ ρ`.**  These are the
ones that are facts about the branch rather than about the enumeration of the
cluster: positivity and the endpoint bound on the radius, the principal point
being a zero, and the pair being genuine.  The remaining nine — `hroot₀`,
`hsimple₀`, `haR₀`, `huniq₀`, `hginj₀`, `hgmem₀`, `hgcard₀`, `hCbd₀` and the
choice of `sfun₀`, `g₀` — all depend on constructing and enumerating the cluster,
which is a separate object.

`τmax₀ = x_1` is the sharp bound: `ftTau` is strictly antitone on the arc with
limit `x_1`, so it never reaches it. -/
theorem endpoint_retained_partial_of_two_le_rho {n r ρ : ℕ} {a : Fin n → ℝ} {c x₁ : ℝ}
    (hn2 : 2 ≤ n) (ha : ∀ k, 0 < a k) (hr : 1 ≤ r) (hne1 : ¬(r = 1 ∧ n = 2))
    (hmin : ∀ k, x₁ ≤ a k)
    (hcard : (Finset.univ.filter fun k => a k = x₁).card = ρ) (hρ : 2 ≤ ρ)
    {e₀ : ℝ} (he₀lt : e₀ < Real.pi / r) :
    (∀ δ : ℝ, 0 < δ → δ ≤ e₀ → 0 < ftTauLower a r (n - 1) x₁ δ)
      ∧ (∀ δ : ℝ, 0 < δ → δ ≤ e₀ → ftTauLower a r (n - 1) x₁ δ ≤ x₁)
      ∧ (∀ δ : ℝ, 0 < δ → δ ≤ e₀ →
          (ftDen (ftRootPoly c a) r ((ftBranchZLower a c r (n - 1) δ : ℝ) : ℂ)).eval
            (ftPrincipal (ftTauLower a r (n - 1) x₁) δ) = 0)
      ∧ (∀ δ : ℝ, 0 < δ → δ ≤ e₀ →
          ftPrincipal (ftTauLower a r (n - 1) x₁) δ
            ≠ ((ftTauLower a r (n - 1) x₁ δ : ℝ) : ℂ)
              * Complex.exp (-((δ : ℝ) : ℂ) * Complex.I)) := by
  classical
  have hn : 0 < n := by omega
  have hnr : 2 ≤ n ∨ 2 ≤ r := Or.inl hn2
  -- two distinct indices carry the repeated smallest zero
  have hcardρ : 2 ≤ (Finset.univ.filter fun k => a k = x₁).card := by rw [hcard]; exact hρ
  have h1lt : 1 < (Finset.univ.filter fun k => a k = x₁).card := by omega
  obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.1 h1lt
  have hix : a i = x₁ := (Finset.mem_filter.1 hi).2
  have hjx : a j = x₁ := (Finset.mem_filter.1 hj).2
  have hmini : ∀ k, a i ≤ a k := fun k => by rw [hix]; exact hmin k
  have harc : ∀ δ : ℝ, 0 < δ → δ ≤ e₀ → δ ∈ Set.Ioo (0 : ℝ) (Real.pi / r) :=
    fun δ h1 h2 => ⟨h1, lt_of_le_of_lt h2 he₀lt⟩
  refine ⟨fun δ h1 h2 => ?_, fun δ h1 h2 => ?_, fun δ h1 h2 => ?_, fun δ h1 h2 => ?_⟩
  · rw [ftTauLower_agree a r (n - 1) x₁ h1]
    exact ftTau_pos (ftBranchAt_of_arc_principal hn ha hr hnr (harc δ h1 h2))
  · rw [ftTauLower_agree a r (n - 1) x₁ h1, ← hix]
    exact ftTau_le_of_repeated_min hn2 ha hr hne1 hij (hix.trans hjx.symm) hmini (harc δ h1 h2)
  · rw [ftBranchZLower_agree a c r (n - 1) h1]
    have hprin : ftPrincipal (ftTauLower a r (n - 1) x₁) δ
        = ftPrincipal (ftTau a r (n - 1)) δ := by
      rw [ftPrincipal, ftPrincipal, ftTauLower_agree a r (n - 1) x₁ h1]
    rw [hprin]
    exact ftDen_eval_ftPrincipal_ftBranchZ c ha (ftArc_subset hr (harc δ h1 h2))
      (ftBranchAt_of_arc_principal hn ha hr hnr (harc δ h1 h2))
  · have hτ : 0 < ftTauLower a r (n - 1) x₁ δ := by
      rw [ftTauLower_agree a r (n - 1) x₁ h1]
      exact ftTau_pos (ftBranchAt_of_arc_principal hn ha hr hnr (harc δ h1 h2))
    have hδπ : δ ∈ Set.Ioo (0 : ℝ) Real.pi := ftArc_subset hr (harc δ h1 h2)
    have h := ftPrincipal_ne_conj_of_pos hτ hδπ
    rwa [conj_ftPrincipal] at h


/-! ### The multiplicity of a zero of `Q` in the pencil at `z = 0` -/

/-- **`ρ` read off the pencil.**  The multiplicity of `x` as a zero of
`Q = c∏(a_k - X)` is the number of indices carrying it.  At the lower endpoint of a
repeated smallest zero this is what `EndpointRegularity.z_endpoint_order` consumes
as its exponent, so it is what makes that exponent `ρ` rather than an opaque
`rootMultiplicity`. -/
theorem rootMultiplicity_ftRootPoly {n : ℕ} {c : ℝ} (hc : c ≠ 0) (a : Fin n → ℝ) (x : ℝ) :
    (ftRootPoly c a).rootMultiplicity ((x : ℝ) : ℂ)
      = (Finset.univ.filter fun k => a k = x).card := by
  classical
  have hC : ((-1 : ℂ) ^ n * (c : ℂ)) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (by norm_num)) (by exact_mod_cast hc)
  rw [← Polynomial.count_roots, ftRootPoly_eq_posRootPoly, posRootPoly,
    Polynomial.roots_C_mul _ hC]
  have hmap : (Multiset.map a Finset.univ.val).map
      (fun x : ℝ => (X - C ((x : ℝ) : ℂ) : Polynomial ℂ))
      = ((Multiset.map a Finset.univ.val).map (fun x : ℝ => ((x : ℝ) : ℂ))).map
        (fun z : ℂ => X - C z) := by
    simp [Function.comp_def]
  rw [hmap, Polynomial.roots_multiset_prod_X_sub_C,
    Multiset.count_map_eq_count' _ _ Complex.ofReal_injective,
    Multiset.count_map]
  have hfil : (Multiset.filter (fun k => x = a k) Finset.univ.val)
      = (Multiset.filter (fun k => a k = x) Finset.univ.val) :=
    Multiset.filter_congr fun k _ => ⟨Eq.symm, Eq.symm⟩
  rw [hfil, Finset.card, Finset.filter_val]


/-- **`eq:z-endpoint-order` at the lower endpoint, `2 ≤ ρ`, with the exponent
identified.**  `z(δ) = δ^ρ·c(δ)` with `c` continuous at `0` and `c(0) ≠ 0`.  The
exponent is `ρ` rather than an opaque `rootMultiplicity` because
`rootMultiplicity_ftRootPoly` reads it off the pencil, and the branch derivative
`EndpointRegularity.z_endpoint_order` needs is `hγd₀`, already proved — so this is
a consequence of the endpoint package rather than an independent input. -/
theorem exists_z_endpoint_order_of_two_le_rho {n r ρ : ℕ} {a : Fin n → ℝ} {c x₁ : ℝ}
    (hn : 0 < n) (ha : ∀ k, 0 < a k) (hc : 0 < c) (hr : 1 ≤ r) (hnr : 2 ≤ n ∨ 2 ≤ r)
    (hx₁ : 0 < x₁) (hmin : ∀ k, x₁ ≤ a k)
    (hcard : (Finset.univ.filter fun k => a k = x₁).card = ρ) (hρ : 2 ≤ ρ) :
    ∃ cf : ℝ → ℂ, ContinuousWithinAt cf (Set.Ici (0 : ℝ)) 0 ∧ cf 0 ≠ 0 ∧
      ∀ᶠ δ in 𝓝[>] (0 : ℝ),
        ((ftBranchZLower a c r (n - 1) δ : ℝ) : ℂ) = (δ : ℂ) ^ ρ * cf δ := by
  classical
  obtain ⟨-, hte, hγe, hγ0, hγd, hk, hrootev⟩ :=
    endpoint_package_of_two_le_rho hn ha hc hr hnr hx₁ hmin hcard hρ
  have hpne : ftRootPoly c a ≠ 0 := by
    intro h
    have h0 : (ftRootPoly c a).eval 0 = ((c * ∏ k, a k : ℝ) : ℂ) := by
      rw [eval_ftRootPoly]; push_cast; simp
    rw [h] at h0
    simp only [Polynomial.eval_zero] at h0
    exact (ne_of_gt (mul_pos hc (Finset.prod_pos fun k _ => ha k))) (by exact_mod_cast h0.symm)
  have hden : ftDen (ftRootPoly c a) r ((0 : ℂ)) = ftRootPoly c a := by rw [ftDen]; simp
  have hP : ftDen (ftRootPoly c a) r ((0 : ℂ)) ≠ 0 := by rw [hden]; exact hpne
  have hmult : (ftDen (ftRootPoly c a) r ((0 : ℂ))).rootMultiplicity ((x₁ : ℝ) : ℂ) = ρ := by
    rw [hden, rootMultiplicity_ftRootPoly hc.ne' a x₁, hcard]
  have hz0 : ((ftBranchZLower a c r (n - 1) 0 : ℝ) : ℂ) = (0 : ℂ) := by
    rw [ftBranchZLower_zero]; norm_num
  obtain ⟨cf, hcfc, hcf0, hcfev⟩ :=
    z_endpoint_order (Q := ftRootPoly c a) (r := r) (ze := (0 : ℂ)) (te := ((x₁ : ℝ) : ℂ))
      hte hP (γ := fun δ => ftPrincipal (ftTauLower a r (n - 1) x₁) δ)
      (zf := fun δ => ((ftBranchZLower a c r (n - 1) δ : ℝ) : ℂ))
      (γe := clusterAlpha x₁ ρ 0) hγe hγ0 hγd (by simpa using hrootev)
  refine ⟨cf, hcfc, hcf0, ?_⟩
  filter_upwards [hcfev] with δ hδ
  rw [hmult, sub_zero] at hδ
  exact hδ


/-! ### The chart parameter along the branch

Two families of roots of unity appear here and they are **not** the same one.  The
*chart* variable rotates by `ζ` with `ζ^ρ = 1` — that is what puts the rotates on
one fibre, and it is what `EndpointBranch.cluster_member_root` consumes.  The
resulting *slopes* carry `clusterOmega ρ j`, which satisfies
`clusterOmega ρ j ^ ρ = -1`, not `1`.  The two are related by
`clusterAlpha x₁ ρ 0 * ζ_k = clusterAlpha x₁ ρ k`, an identity rather than a
matching. -/

/-- `z(δ)/δ^ρ` converges to a positive real.  This is `eq:z-endpoint-order` with
the complex cofactor resolved: `z` and `δ` are real, so the cofactor is, and it is
positive because the branch value is. -/
theorem exists_tendsto_z_div_pow_of_two_le_rho {n r ρ : ℕ} {a : Fin n → ℝ} {c x₁ : ℝ}
    (hn : 0 < n) (ha : ∀ k, 0 < a k) (hc : 0 < c) (hr : 1 ≤ r) (hnr : 2 ≤ n ∨ 2 ≤ r)
    (hx₁ : 0 < x₁) (hmin : ∀ k, x₁ ≤ a k)
    (hcard : (Finset.univ.filter fun k => a k = x₁).card = ρ) (hρ : 2 ≤ ρ) :
    ∃ A : ℝ, 0 < A ∧ Filter.Tendsto
      (fun δ : ℝ => ftBranchZLower a c r (n - 1) δ / δ ^ ρ) (𝓝[>] (0 : ℝ)) (𝓝 A) := by
  classical
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  obtain ⟨cf, hcfc, hcf0, hcfev⟩ :=
    exists_z_endpoint_order_of_two_le_rho hn ha hc hr hnr hx₁ hmin hcard hρ
  have hsub : 𝓝[>] (0 : ℝ) ≤ 𝓝[Set.Ici (0 : ℝ)] (0 : ℝ) :=
    nhdsWithin_mono _ fun x hx => Set.mem_Ici.2 (le_of_lt (Set.mem_Ioi.1 hx))
  have hcflim : Filter.Tendsto cf (𝓝[>] (0 : ℝ)) (𝓝 (cf 0)) := hcfc.tendsto.mono_left hsub
  -- the cofactor is the real quotient
  have hreal : ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      ((ftBranchZLower a c r (n - 1) δ / δ ^ ρ : ℝ) : ℂ) = cf δ := by
    filter_upwards [hcfev, self_mem_nhdsWithin] with δ hδ hδ0
    have hδC : ((δ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hδ0
    have hpow : ((δ : ℝ) : ℂ) ^ ρ ≠ 0 := pow_ne_zero _ hδC
    push_cast
    rw [hδ]
    field_simp
  have hQlim : Filter.Tendsto
      (fun δ : ℝ => ((ftBranchZLower a c r (n - 1) δ / δ ^ ρ : ℝ) : ℂ))
      (𝓝[>] (0 : ℝ)) (𝓝 (cf 0)) := hcflim.congr' (hreal.mono fun δ h => h.symm)
  have hre : Filter.Tendsto (fun δ : ℝ => ftBranchZLower a c r (n - 1) δ / δ ^ ρ)
      (𝓝[>] (0 : ℝ)) (𝓝 (cf 0).re) := by
    have h := (Complex.continuous_re.tendsto (cf 0)).comp hQlim
    simp only [Function.comp_def, Complex.ofReal_re] at h
    exact h
  have him : (cf 0).im = 0 := by
    have h := (Complex.continuous_im.tendsto (cf 0)).comp hQlim
    simp only [Function.comp_def, Complex.ofReal_im] at h
    exact tendsto_nhds_unique h tendsto_const_nhds
  -- positivity of the branch value gives positivity of the limit
  have hparp : Even (n + (n - 1) + 1) := by
    have hEq : n + (n - 1) + 1 = 2 * n := by omega
    rw [hEq]; exact even_two_mul n
  have hpos : ∀ᶠ δ in 𝓝[>] (0 : ℝ), 0 < ftBranchZLower a c r (n - 1) δ / δ ^ ρ := by
    filter_upwards [self_mem_nhdsWithin,
      Ioo_mem_nhdsGT (show (0 : ℝ) < Real.pi / r by positivity)] with δ hδ0 hδarc
    have hδ : (0 : ℝ) < δ := hδ0
    rw [ftBranchZLower_agree a c r (n - 1) hδ]
    refine div_pos ?_ (by positivity)
    exact ftBranchZ_pos ha hc hparp (ftArc_subset hr hδarc)
      (ftBranchAt_of_arc_principal hn ha hr hnr hδarc)
  have hnn : 0 ≤ (cf 0).re := ge_of_tendsto hre (hpos.mono fun δ h => le_of_lt h)
  refine ⟨(cf 0).re, lt_of_le_of_ne hnn ?_, hre⟩
  intro h
  exact hcf0 (Complex.ext h.symm him)


/-- The chart parameter along the branch: the positive real `ρ`-th root of the
spectral parameter, so `v(δ)^ρ = z(δ)` and the cluster members at angle `δ` are
`ψ(ζ·v(δ))` over the `ρ`-th roots of unity `ζ`. -/
noncomputable def ftClusterParam {n : ℕ} (a : Fin n → ℝ) (c : ℝ) (r l ρ : ℕ) : ℝ → ℝ :=
  fun δ => (ftBranchZLower a c r l δ) ^ ((ρ : ℝ)⁻¹)

theorem ftClusterParam_pow {n : ℕ} {a : Fin n → ℝ} {c : ℝ} {r l ρ : ℕ} (hρ : ρ ≠ 0)
    {δ : ℝ} (hz : 0 ≤ ftBranchZLower a c r l δ) :
    (ftClusterParam a c r l ρ δ) ^ ρ = ftBranchZLower a c r l δ :=
  Real.rpow_inv_natCast_pow hz hρ

/-- **`v(δ)/δ` converges to a positive limit.**  `(v(δ)/δ)^ρ = z(δ)/δ^ρ`, which
`exists_tendsto_z_div_pow_of_two_le_rho` sends to `A > 0`, and the `ρ`-th root is
continuous there.  This is what turns the chart's `ψ'(0) ≠ 0` into a statement
about the *angular* parameter the paper uses. -/
theorem exists_tendsto_ftClusterParam_div {n r ρ : ℕ} {a : Fin n → ℝ} {c x₁ : ℝ}
    (hn : 0 < n) (ha : ∀ k, 0 < a k) (hc : 0 < c) (hr : 1 ≤ r) (hnr : 2 ≤ n ∨ 2 ≤ r)
    (hx₁ : 0 < x₁) (hmin : ∀ k, x₁ ≤ a k)
    (hcard : (Finset.univ.filter fun k => a k = x₁).card = ρ) (hρ : 2 ≤ ρ) :
    ∃ L : ℝ, 0 < L ∧ Filter.Tendsto
      (fun δ : ℝ => ftClusterParam a c r (n - 1) ρ δ / δ) (𝓝[>] (0 : ℝ)) (𝓝 L) := by
  classical
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hρ0 : (ρ : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  obtain ⟨A, hA, hAlim⟩ :=
    exists_tendsto_z_div_pow_of_two_le_rho hn ha hc hr hnr hx₁ hmin hcard hρ
  have hcont : ContinuousAt (fun x : ℝ => x ^ ((ρ : ℝ)⁻¹)) A :=
    Real.continuousAt_rpow_const A _ (Or.inl (ne_of_gt hA))
  refine ⟨A ^ ((ρ : ℝ)⁻¹), Real.rpow_pos_of_pos hA _, ?_⟩
  have hcomp := hcont.tendsto.comp hAlim
  refine hcomp.congr' ?_
  filter_upwards [self_mem_nhdsWithin,
    Ioo_mem_nhdsGT (show (0 : ℝ) < Real.pi / r by positivity)] with δ hδ0 hδarc
  have hδ : (0 : ℝ) < δ := hδ0
  have hparp : Even (n + (n - 1) + 1) := by
    have hEq : n + (n - 1) + 1 = 2 * n := by omega
    rw [hEq]; exact even_two_mul n
  have hzpos : 0 < ftBranchZLower a c r (n - 1) δ := by
    rw [ftBranchZLower_agree a c r (n - 1) hδ]
    exact ftBranchZ_pos ha hc hparp (ftArc_subset hr hδarc)
      (ftBranchAt_of_arc_principal hn ha hr hnr hδarc)
  rw [Function.comp_apply, ftClusterParam,
    Real.div_rpow (le_of_lt hzpos) (by positivity),
    ← Real.rpow_natCast δ ρ, ← Real.rpow_mul (le_of_lt hδ)]
  rw [mul_inv_cancel₀ hρ0, Real.rpow_one]


/-- **The cluster member's slope in the angular parameter.**  If the chart has
`ψ(0) = t_e` and `ψ'(0) = γ_e`, and the chart parameter satisfies `v(δ)/δ → L`,
then the member at chart direction `ζ` enters `t_e` with slope `γ_e·ζ·L` in `δ`.

`ζ` here ranges over the `ρ`-th roots of **unity** — the chart directions — not
over `clusterOmega`, whose `ρ`-th power is `-1`.  The two families are related by
`clusterAlpha x₁ ρ 0 * ζ_k = clusterAlpha x₁ ρ k`. -/
theorem tendsto_cluster_slope {ψ : ℂ → ℂ} {te γe : ℂ} (hψ0 : ψ 0 = te)
    (hψd : HasDerivAt ψ γe 0) {v : ℝ → ℝ} {L : ℝ}
    (hvpos : ∀ᶠ δ in 𝓝[>] (0 : ℝ), 0 < v δ)
    (hv : Filter.Tendsto (fun δ : ℝ => v δ / δ) (𝓝[>] (0 : ℝ)) (𝓝 L))
    {ζ : ℂ} (hζ : ζ ≠ 0) :
    Filter.Tendsto (fun δ : ℝ => (ψ (ζ * ((v δ : ℝ) : ℂ)) - te) / ((δ : ℝ) : ℂ))
      (𝓝[>] (0 : ℝ)) (𝓝 (γe * (ζ * (L : ℂ)))) := by
  classical
  -- `v δ → 0`
  have hδ0 : Filter.Tendsto (fun δ : ℝ => (δ : ℝ)) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hv0 : Filter.Tendsto v (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h := hv.mul hδ0
    rw [mul_zero] at h
    refine h.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    have hδne : (δ : ℝ) ≠ 0 := ne_of_gt (Set.mem_Ioi.1 hδ)
    field_simp
  -- the chart argument tends to `0` and stays off it
  have hargne : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ζ * ((v δ : ℝ) : ℂ) ≠ 0 := by
    filter_upwards [hvpos] with δ h
    exact mul_ne_zero hζ (by exact_mod_cast ne_of_gt h)
  have hargC : Filter.Tendsto (fun δ : ℝ => ζ * ((v δ : ℝ) : ℂ)) (𝓝[>] (0 : ℝ))
      (𝓝[≠] (0 : ℂ)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ hargne
    have h := ((Complex.continuous_ofReal.tendsto (0 : ℝ)).comp hv0).const_mul ζ
    simpa [Function.comp_def] using h
  -- the difference quotient of the chart
  have hslope : Filter.Tendsto (fun u : ℂ => (ψ u - te) / u) (𝓝[≠] (0 : ℂ)) (𝓝 γe) := by
    have h := hasDerivAt_iff_tendsto_slope.1 hψd
    refine h.congr fun u => ?_
    rw [slope_def_field, hψ0]
    ring_nf
  have hfirst := hslope.comp hargC
  -- the chart parameter against the angle
  have hsecond : Filter.Tendsto (fun δ : ℝ => ζ * ((v δ : ℝ) : ℂ) / ((δ : ℝ) : ℂ))
      (𝓝[>] (0 : ℝ)) (𝓝 (ζ * (L : ℂ))) := by
    have h := ((Complex.continuous_ofReal.tendsto L).comp hv).const_mul ζ
    simp only [Function.comp_def] at h
    refine h.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    have hδ0' : ((δ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt (Set.mem_Ioi.1 hδ)
    push_cast
    field_simp
  refine (hfirst.mul hsecond).congr' ?_
  filter_upwards [self_mem_nhdsWithin, hargne] with δ hδ hne
  have hδ0' : ((δ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt (Set.mem_Ioi.1 hδ)
  have hvne : ((v δ : ℝ) : ℂ) ≠ 0 := fun h => hne (by rw [h, mul_zero])
  rw [Function.comp_apply]
  field_simp


/-! ### The cluster family -/

theorem ftClusterParam_pos {n r ρ : ℕ} {a : Fin n → ℝ} {c : ℝ} (hn : 0 < n)
    (ha : ∀ k, 0 < a k) (hc : 0 < c) (hr : 1 ≤ r) (hnr : 2 ≤ n ∨ 2 ≤ r) :
    ∀ᶠ δ in 𝓝[>] (0 : ℝ), 0 < ftClusterParam a c r (n - 1) ρ δ := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hparp : Even (n + (n - 1) + 1) := by
    have hEq : n + (n - 1) + 1 = 2 * n := by omega
    rw [hEq]; exact even_two_mul n
  filter_upwards [self_mem_nhdsWithin,
    Ioo_mem_nhdsGT (show (0 : ℝ) < Real.pi / r by positivity)] with δ hδ0 hδarc
  have hδ : (0 : ℝ) < δ := hδ0
  have hzpos : 0 < ftBranchZLower a c r (n - 1) δ := by
    rw [ftBranchZLower_agree a c r (n - 1) hδ]
    exact ftBranchZ_pos ha hc hparp (ftArc_subset hr hδarc)
      (ftBranchAt_of_arc_principal hn ha hr hnr hδarc)
  exact Real.rpow_pos_of_pos hzpos _

theorem tendsto_ftClusterParam {n r ρ : ℕ} {a : Fin n → ℝ} {c x₁ : ℝ}
    (hn : 0 < n) (ha : ∀ k, 0 < a k) (hc : 0 < c) (hr : 1 ≤ r) (hnr : 2 ≤ n ∨ 2 ≤ r)
    (hx₁ : 0 < x₁) (hmin : ∀ k, x₁ ≤ a k)
    (hcard : (Finset.univ.filter fun k => a k = x₁).card = ρ) (hρ : 2 ≤ ρ) :
    Filter.Tendsto (ftClusterParam a c r (n - 1) ρ) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  obtain ⟨L, hL, hLlim⟩ :=
    exists_tendsto_ftClusterParam_div hn ha hc hr hnr hx₁ hmin hcard hρ
  have hδ0 : Filter.Tendsto (fun δ : ℝ => (δ : ℝ)) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have h := hLlim.mul hδ0
  rw [mul_zero] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  have hδne : (δ : ℝ) ≠ 0 := ne_of_gt (Set.mem_Ioi.1 hδ)
  field_simp


/-- **The lower cluster, assembled.**  The `ρ` members at angle `δ` are
`ψ(ζ_j·v(δ))` over the chart directions; they are zeros of the pencil at the
branch's own spectral parameter, distinct, and each enters `x_1` with slope
`γ_e·ζ_j·L`.

Everything here is a product of pieces proved in `EndpointBranch` — the chart and
its inverse, `cluster_member_root`, `cluster_member_ne`, and `tendsto_cluster_slope`
— against the chart parameter `ftClusterParam`.  Nothing is assumed. -/
theorem exists_cluster_family_of_two_le_rho {n r ρ : ℕ} {a : Fin n → ℝ} {c x₁ : ℝ}
    (hn : 0 < n) (ha : ∀ k, 0 < a k) (hc : 0 < c) (hr : 1 ≤ r) (hnr : 2 ≤ n ∨ 2 ≤ r)
    (hx₁ : 0 < x₁) (hmin : ∀ k, x₁ ≤ a k)
    (hcard : (Finset.univ.filter fun k => a k = x₁).card = ρ) (hρ : 2 ≤ ρ) :
    ∃ (ψ : ℂ → ℂ) (γe : ℂ) (L : ℝ), γe ≠ 0 ∧ 0 < L
      ∧ (∀ᶠ δ in 𝓝[>] (0 : ℝ), ∀ j ∈ Finset.range ρ,
          (ftDen (ftRootPoly c a) r ((ftBranchZLower a c r (n - 1) δ : ℝ) : ℂ)).eval
            (ψ (clusterDir ρ j * ((ftClusterParam a c r (n - 1) ρ δ : ℝ) : ℂ))) = 0)
      ∧ (∀ᶠ δ in 𝓝[>] (0 : ℝ), ∀ i ∈ Finset.range ρ, ∀ j ∈ Finset.range ρ, i ≠ j →
          ψ (clusterDir ρ i * ((ftClusterParam a c r (n - 1) ρ δ : ℝ) : ℂ))
            ≠ ψ (clusterDir ρ j * ((ftClusterParam a c r (n - 1) ρ δ : ℝ) : ℂ)))
      ∧ (∀ j : ℕ, Filter.Tendsto
          (fun δ : ℝ => (ψ (clusterDir ρ j * ((ftClusterParam a c r (n - 1) ρ δ : ℝ) : ℂ))
              - ((x₁ : ℝ) : ℂ)) / ((δ : ℝ) : ℂ))
          (𝓝[>] (0 : ℝ)) (𝓝 (γe * (clusterDir ρ j * (L : ℂ))))) := by
  classical
  have hρ0 : ρ ≠ 0 := by omega
  have hte : ((x₁ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hx₁
  -- the endpoint factorization, with the exponent identified as `ρ`
  have hpne : ftRootPoly c a ≠ 0 := by
    intro h
    have h0 : (ftRootPoly c a).eval 0 = ((c * ∏ k, a k : ℝ) : ℂ) := by
      rw [eval_ftRootPoly]; push_cast; simp
    rw [h] at h0
    simp only [Polynomial.eval_zero] at h0
    exact (ne_of_gt (mul_pos hc (Finset.prod_pos fun k _ => ha k))) (by exact_mod_cast h0.symm)
  have hden : ftDen (ftRootPoly c a) r ((0 : ℂ)) = ftRootPoly c a := by rw [ftDen]; simp
  have hP : ftDen (ftRootPoly c a) r ((0 : ℂ)) ≠ 0 := by rw [hden]; exact hpne
  have hmult : (ftDen (ftRootPoly c a) r ((0 : ℂ))).rootMultiplicity ((x₁ : ℝ) : ℂ) = ρ := by
    rw [hden, rootMultiplicity_ftRootPoly hc.ne' a x₁, hcard]
  obtain ⟨G, hfac, hG⟩ :=
    exists_endpointFactor (Q := ftRootPoly c a) (r := r) (ze := (0 : ℂ))
      (te := ((x₁ : ℝ) : ℂ)) hP
  rw [hmult] at hfac
  obtain ⟨ψ, γe, hψa, hψ0, hγe, hψd, ⟨U, hU, hinj⟩, hchart⟩ :=
    exists_cluster_branch (by omega) hte hG hfac
  obtain ⟨L, hL, hvL⟩ := exists_tendsto_ftClusterParam_div hn ha hc hr hnr hx₁ hmin hcard hρ
  have hvpos := ftClusterParam_pos (a := a) (c := c) (ρ := ρ) hn ha hc hr hnr
  have hv0 := tendsto_ftClusterParam hn ha hc hr hnr hx₁ hmin hcard hρ
  have hv0C : Filter.Tendsto
      (fun δ : ℝ => ((ftClusterParam a c r (n - 1) ρ δ : ℝ) : ℂ)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h := (Complex.continuous_ofReal.tendsto (0 : ℝ)).comp hv0
    simpa [Function.comp_def] using h
  -- the chart parameter's `ρ`-th power is the branch's spectral parameter
  have hpow : ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      ((ftClusterParam a c r (n - 1) ρ δ : ℝ) : ℂ) ^ ρ
        = ((ftBranchZLower a c r (n - 1) δ : ℝ) : ℂ) := by
    have hrR : (0 : ℝ) < r := by exact_mod_cast hr
    have hparp : Even (n + (n - 1) + 1) := by
      have hEq : n + (n - 1) + 1 = 2 * n := by omega
      rw [hEq]; exact even_two_mul n
    filter_upwards [self_mem_nhdsWithin,
      Ioo_mem_nhdsGT (show (0 : ℝ) < Real.pi / r by positivity)] with δ hδ0 hδarc
    have hδ : (0 : ℝ) < δ := hδ0
    have hz : 0 ≤ ftBranchZLower a c r (n - 1) δ := by
      rw [ftBranchZLower_agree a c r (n - 1) hδ]
      exact le_of_lt (ftBranchZ_pos ha hc hparp (ftArc_subset hr hδarc)
        (ftBranchAt_of_arc_principal hn ha hr hnr hδarc))
    rw [← Complex.ofReal_pow, ftClusterParam_pow hρ0 hz]
  refine ⟨ψ, γe, L, hγe, hL, ?_, ?_, ?_⟩
  · rw [Filter.eventually_all_finset]
    intro j _
    have hcm := cluster_member_root hchart (clusterDir_pow hρ0 j)
    filter_upwards [hv0C.eventually hcm, hpow] with δ hδ hpδ
    rwa [hpδ] at hδ
  · have hmem : ∀ j ∈ Finset.range ρ, ∀ᶠ δ in 𝓝[>] (0 : ℝ),
        clusterDir ρ j * ((ftClusterParam a c r (n - 1) ρ δ : ℝ) : ℂ) ∈ U := by
      intro j _
      have hmul : Filter.Tendsto
          (fun δ : ℝ => clusterDir ρ j * ((ftClusterParam a c r (n - 1) ρ δ : ℝ) : ℂ))
          (𝓝[>] (0 : ℝ)) (𝓝 0) := by
        have h := hv0C.const_mul (clusterDir ρ j)
        simpa using h
      exact hmul hU
    have hall : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∀ j ∈ Finset.range ρ,
        clusterDir ρ j * ((ftClusterParam a c r (n - 1) ρ δ : ℝ) : ℂ) ∈ U :=
      Filter.eventually_all_finset _ |>.2 hmem
    filter_upwards [hall, hvpos] with δ hδU hvδ
    intro i hi j hj hij
    refine cluster_member_ne hinj (hδU i hi) (hδU j hj)
      (by exact_mod_cast ne_of_gt hvδ) ?_
    intro h
    exact hij (clusterDir_inj hρ0 (Finset.mem_range.1 hi) (Finset.mem_range.1 hj) h)
  · intro j
    exact tendsto_cluster_slope hψ0 hψd hvpos hvL (clusterDir_ne_zero ρ j)

/-! ### The separating circle at the branch -/

/-- **The branch's spectral parameter stays inside the separating window.**
`z(δ) → 0` at the rate `eq:z-endpoint-order` gives, so every statement
`EndpointSeparation` proves for `‖z‖ ≤ ftSepWindow` holds along the branch on a
window of angles. -/
theorem exists_z_window_of_two_le_rho {n r ρ : ℕ} {a : Fin n → ℝ} {c x₁ : ℝ}
    (hn : 0 < n) (ha : ∀ k, 0 < a k) (hc : 0 < c) (hr : 1 ≤ r) (hnr : 2 ≤ n ∨ 2 ≤ r)
    (hx₁ : 0 < x₁) (hmin : ∀ k, x₁ ≤ a k)
    (hcard : (Finset.univ.filter fun k => a k = x₁).card = ρ) (hρ : 2 ≤ ρ) :
    ∃ e > (0 : ℝ), ∀ δ : ℝ, 0 < δ → δ ≤ e →
      ‖((ftBranchZLower a c r (n - 1) δ : ℝ) : ℂ)‖ ≤ ftSepWindow c a x₁ r := by
  obtain ⟨A, hA, hzr⟩ := exists_tendsto_z_div_pow_of_two_le_rho hn ha hc hr hnr hx₁ hmin hcard hρ
  have hρ0 : ρ ≠ 0 := by omega
  have hpow : Filter.Tendsto (fun δ : ℝ => δ ^ ρ) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h := (continuous_pow ρ).tendsto (0 : ℝ)
    rw [zero_pow hρ0] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hz0 : Filter.Tendsto (fun δ : ℝ => ftBranchZLower a c r (n - 1) δ)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hmul := hzr.mul hpow
    rw [mul_zero] at hmul
    refine hmul.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    have hne : (δ : ℝ) ^ ρ ≠ 0 := ne_of_gt (pow_pos hδ ρ)
    field_simp
  have hw : 0 < ftSepWindow c a x₁ r := ftSepWindow_pos hc.ne' hx₁ hmin
  have hev : ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      |ftBranchZLower a c r (n - 1) δ| ≤ ftSepWindow c a x₁ r := by
    filter_upwards [Metric.tendsto_nhds.1 hz0 _ hw] with δ hδ
    rw [Real.dist_eq, sub_zero] at hδ
    exact hδ.le
  rw [eventually_nhdsWithin_iff] at hev
  obtain ⟨ε₀, hε₀, hball⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨ε₀ / 2, by linarith, fun δ hδ hδe => ?_⟩
  have hd : dist δ (0 : ℝ) < ε₀ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hδ]; linarith
  rw [Complex.norm_real, Real.norm_eq_abs]
  exact hball hd hδ

/-- **`hCbd₀`, and the zero-free circle it needs, at the lower endpoint.**  The
radius is `ftSepRadius`, fixed by the spectrum of `Q` alone; the window is where
the branch's spectral parameter stays inside `ftSepWindow`, which it does because
`z(δ) → 0` at the rate `eq:z-endpoint-order` gives.

Two of the three circle binders of
`DominanceFT.weighted_dominance_of_branch_any_multiplicity_at` come out of this:
`hCbd₀` directly, and the zero-freeness `huniq₀` needs before it can count.  The
third, `haR₀`, is about the cluster's position and waits on the enumeration.

`C₀` depends on `B`; the radius and the window do not, so the same circle serves
every numerator over one denominator. -/
theorem exists_endpoint_contour_window_of_two_le_rho {n r ρ : ℕ} {a : Fin n → ℝ} {c x₁ : ℝ}
    (hn : 0 < n) (ha : ∀ k, 0 < a k) (hc : 0 < c) (hr : 1 ≤ r) (hnr : 2 ≤ n ∨ 2 ≤ r)
    (hx₁ : 0 < x₁) (hmin : ∀ k, x₁ ≤ a k)
    (hcard : (Finset.univ.filter fun k => a k = x₁).card = ρ) (hρ : 2 ≤ ρ)
    (B : Polynomial ℂ) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∃ e₀ > (0 : ℝ), ∀ δ : ℝ, 0 < δ → δ ≤ e₀ →
      (∀ t ∈ Metric.sphere (0 : ℂ) (ftSepRadius a x₁),
          ‖B.eval t / (ftDen (ftRootPoly c a) r
            ((ftBranchZLower a c r (n - 1) δ : ℝ) : ℂ)).eval t‖ ≤ C₀)
        ∧ ∀ t : ℂ, ‖t‖ = ftSepRadius a x₁ →
            (ftDen (ftRootPoly c a) r
              ((ftBranchZLower a c r (n - 1) δ : ℝ) : ℂ)).eval t ≠ 0 := by
  obtain ⟨C₀, hC₀, hbd⟩ := exists_endpoint_contour_bound (c := c) (r := r) hc.ne' ha hx₁ hmin B
  obtain ⟨e₀, he₀, hzw⟩ :=
    exists_z_window_of_two_le_rho hn ha hc hr hnr hx₁ hmin hcard hρ
  refine ⟨C₀, hC₀, e₀, he₀, fun δ hδ hδe => ?_⟩
  exact ⟨fun t ht => hbd _ (hzw δ hδ hδe) t ht,
    fun t ht => eval_ftDen_ne_zero_on_sphere hc.ne' ha hx₁ hmin (hzw δ hδ hδe) ht⟩

open scoped Classical in
/-- The `ρ` cluster members at angle `δ`, as a finite set.  Naming it keeps the
retained set's *identity* — it is the cluster, indexed by chart direction — rather
than hiding it behind an existential, which is what the residue asymptotics need
in order to know which member they are looking at. -/
noncomputable def ftClusterSet {n : ℕ} (a : Fin n → ℝ) (c : ℝ) (r l ρ : ℕ) (ψ : ℂ → ℂ)
    (δ : ℝ) : Finset ℂ :=
  (Finset.range ρ).image fun j =>
    ψ (clusterDir ρ j * ((ftClusterParam a c r l ρ δ : ℝ) : ℂ))

theorem mem_ftClusterSet {n : ℕ} {a : Fin n → ℝ} {c : ℝ} {r l ρ : ℕ} {ψ : ℂ → ℂ} {δ : ℝ}
    {w : ℂ} : w ∈ ftClusterSet a c r l ρ ψ δ ↔ ∃ j ∈ Finset.range ρ,
      ψ (clusterDir ρ j * ((ftClusterParam a c r l ρ δ : ℝ) : ℂ)) = w := by
  classical
  simp [ftClusterSet, Finset.mem_image]

/-- **The lower retained set, and five of its binders.**  The `ρ` cluster members
of `exists_cluster_family_of_two_le_rho` are collected into a finite set; the
count of `EndpointSeparation.simple_and_complete_of_card` then says they are
simple and that nothing else in the separating disk is a zero.

That gives `hroot₀`, `haR₀`, `huniq₀`, `hsimple₀` and the cardinality `hgcard₀`
rests on, all at once — they are one fact about the count, not five facts about
the cluster.  The chart and the slopes are handed back with them, because the
completeness field is what identifies the principal pair's index and the residue
asymptotics are stated per index.  What is still owed is that identification,
which is what turns `ρ` into `n_0 = ρ - 2`. -/
theorem exists_retained_set_of_two_le_rho {n r ρ : ℕ} {a : Fin n → ℝ} {c x₁ : ℝ}
    (hn : 0 < n) (ha : ∀ k, 0 < a k) (hc : 0 < c) (hr : 1 ≤ r) (hnr : 2 ≤ n ∨ 2 ≤ r)
    (hx₁ : 0 < x₁) (hmin : ∀ k, x₁ ≤ a k)
    (hcard : (Finset.univ.filter fun k => a k = x₁).card = ρ) (hρ : 2 ≤ ρ) :
    ∃ (ψ : ℂ → ℂ) (γe : ℂ) (L : ℝ), γe ≠ 0 ∧ 0 < L
      ∧ (∀ j : ℕ, Filter.Tendsto
          (fun δ : ℝ => (ψ (clusterDir ρ j
              * ((ftClusterParam a c r (n - 1) ρ δ : ℝ) : ℂ)) - ((x₁ : ℝ) : ℂ))
            / ((δ : ℝ) : ℂ))
          (𝓝[>] (0 : ℝ)) (𝓝 (γe * (clusterDir ρ j * ((L : ℝ) : ℂ)))))
      ∧ ∃ e₀ > (0 : ℝ), ∀ δ : ℝ, 0 < δ → δ ≤ e₀ →
        (ftClusterSet a c r (n - 1) ρ ψ δ).card = ρ
          ∧ (∀ w ∈ ftClusterSet a c r (n - 1) ρ ψ δ, (ftDen (ftRootPoly c a) r
              ((ftBranchZLower a c r (n - 1) δ : ℝ) : ℂ)).eval w = 0)
          ∧ (∀ w ∈ ftClusterSet a c r (n - 1) ρ ψ δ, ‖w‖ < ftSepRadius a x₁)
          ∧ (∀ w ∈ ftClusterSet a c r (n - 1) ρ ψ δ,
              (Polynomial.derivative (ftDen (ftRootPoly c a) r
                ((ftBranchZLower a c r (n - 1) δ : ℝ) : ℂ))).eval w ≠ 0)
          ∧ (∀ w : ℂ, ‖w‖ ≤ ftSepRadius a x₁ →
              (ftDen (ftRootPoly c a) r
                ((ftBranchZLower a c r (n - 1) δ : ℝ) : ℂ)).eval w = 0 →
              w ∈ ftClusterSet a c r (n - 1) ρ ψ δ) := by
  classical
  obtain ⟨ψ, γe, L, hγe, hL, hroots, hdistinct, hslope⟩ :=
    exists_cluster_family_of_two_le_rho hn ha hc hr hnr hx₁ hmin hcard hρ
  obtain ⟨ez, hez, hzw⟩ := exists_z_window_of_two_le_rho hn ha hc hr hnr hx₁ hmin hcard hρ
  set v : ℝ → ℝ := ftClusterParam a c r (n - 1) ρ with hv
  have hmult : (ftRootPoly c a).rootMultiplicity ((x₁ : ℝ) : ℂ) = ρ := by
    rw [rootMultiplicity_ftRootPoly hc.ne' a x₁, hcard]
  -- each member tends to `x₁`, so eventually every one is strictly inside the circle
  have hin : ∀ j : ℕ, ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      ‖ψ (clusterDir ρ j * ((v δ : ℝ) : ℂ))‖ < ftSepRadius a x₁ := by
    intro j
    have hid : Filter.Tendsto (fun δ : ℝ => ((δ : ℝ) : ℂ)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have hcont : Continuous fun δ : ℝ => ((δ : ℝ) : ℂ) := Complex.continuous_ofReal
      simpa using (hcont.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
    have hmul := (hslope j).mul hid
    rw [mul_zero] at hmul
    have hsub : Filter.Tendsto
        (fun δ : ℝ => ψ (clusterDir ρ j * ((v δ : ℝ) : ℂ)) - ((x₁ : ℝ) : ℂ))
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      refine hmul.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with δ hδ
      have hne : ((δ : ℝ) : ℂ) ≠ 0 := by
        exact_mod_cast ne_of_gt hδ
      field_simp
    have htend : Filter.Tendsto (fun δ : ℝ => ψ (clusterDir ρ j * ((v δ : ℝ) : ℂ)))
        (𝓝[>] (0 : ℝ)) (𝓝 ((x₁ : ℝ) : ℂ)) := by
      have := hsub.add_const ((x₁ : ℝ) : ℂ)
      simpa using this
    have hnorm := htend.norm
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx₁] at hnorm
    exact hnorm.eventually_lt_const (lt_ftSepRadius hmin)
  have hinall : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∀ j ∈ Finset.range ρ,
      ‖ψ (clusterDir ρ j * ((v δ : ℝ) : ℂ))‖ < ftSepRadius a x₁ :=
    (Filter.eventually_all_finset _).2 fun j _ => hin j
  have hev : ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      (∀ j ∈ Finset.range ρ, (ftDen (ftRootPoly c a) r
          ((ftBranchZLower a c r (n - 1) δ : ℝ) : ℂ)).eval
            (ψ (clusterDir ρ j * ((v δ : ℝ) : ℂ))) = 0)
        ∧ (∀ i ∈ Finset.range ρ, ∀ j ∈ Finset.range ρ, i ≠ j →
            ψ (clusterDir ρ i * ((v δ : ℝ) : ℂ)) ≠ ψ (clusterDir ρ j * ((v δ : ℝ) : ℂ)))
        ∧ ∀ j ∈ Finset.range ρ,
            ‖ψ (clusterDir ρ j * ((v δ : ℝ) : ℂ))‖ < ftSepRadius a x₁ := by
    filter_upwards [hroots, hdistinct, hinall] with δ h1 h2 h3 using ⟨h1, h2, h3⟩
  rw [eventually_nhdsWithin_iff] at hev
  obtain ⟨ε₀, hε₀, hball⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨ψ, γe, L, hγe, hL, hslope, min (ε₀ / 2) ez, lt_min (by linarith) hez,
    fun δ hδ hδe => ?_⟩
  have hd : dist δ (0 : ℝ) < ε₀ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hδ]
    linarith [le_trans hδe (min_le_left (ε₀ / 2) ez)]
  obtain ⟨hr0, hdd, hlt⟩ := hball hd hδ
  have hzδ := hzw δ hδ (le_trans hδe (min_le_right (ε₀ / 2) ez))
  have hcardS : (ftClusterSet a c r (n - 1) ρ ψ δ).card = ρ := by
    rw [ftClusterSet, Finset.card_image_of_injOn, Finset.card_range]
    intro i hi j hj hij
    by_contra hne
    exact hdd i hi j hj hne hij
  have hmemS : ∀ w ∈ ftClusterSet a c r (n - 1) ρ ψ δ, (ftDen (ftRootPoly c a) r
      ((ftBranchZLower a c r (n - 1) δ : ℝ) : ℂ)).eval w = 0
        ∧ ‖w‖ < ftSepRadius a x₁ := by
    intro w hw
    obtain ⟨j, hj, rfl⟩ := mem_ftClusterSet.1 hw
    exact ⟨hr0 j hj, hlt j hj⟩
  obtain ⟨hsimple, hcomplete⟩ :=
    simple_and_complete_of_card (r := r) hc.ne' ha hx₁ hmin hmult hzδ hcardS hmemS
  exact ⟨hcardS, fun w hw => (hmemS w hw).1, fun w hw => (hmemS w hw).2, hsimple, hcomplete⟩

/-- **The principal branch's slope, as a limit along the arc.**  The endpoint
derivative of `hγd₀`, read as the quotient `exists_cluster_index_of_cover`
consumes. -/
theorem tendsto_ftPrincipal_slope_of_two_le_rho {n r ρ : ℕ} {a : Fin n → ℝ} {x₁ : ℝ}
    (hn : 0 < n) (ha : ∀ k, 0 < a k) (hr : 1 ≤ r) (hnr : 2 ≤ n ∨ 2 ≤ r)
    (hx₁ : 0 < x₁) (hmin : ∀ k, x₁ ≤ a k)
    (hcard : (Finset.univ.filter fun k => a k = x₁).card = ρ) (hρ : 2 ≤ ρ) :
    Filter.Tendsto
      (fun δ : ℝ => (ftPrincipal (ftTauLower a r (n - 1) x₁) δ - ((x₁ : ℝ) : ℂ))
        / ((δ : ℝ) : ℂ))
      (𝓝[>] (0 : ℝ)) (𝓝 (clusterAlpha x₁ ρ 0)) := by
  have hdiff : Set.Ici (0 : ℝ) \ {0} = Set.Ioi 0 := by
    ext u
    simp only [Set.mem_sdiff, Set.mem_Ici, Set.mem_singleton_iff, Set.mem_Ioi]
    exact ⟨fun h => lt_of_le_of_ne h.1 (Ne.symm h.2), fun h => ⟨h.le, ne_of_gt h⟩⟩
  have hd := hasDerivWithinAt_ftPrincipal_ftTauLower hn ha hr hnr hx₁ hmin hcard hρ
  rw [hasDerivWithinAt_iff_tendsto_slope, hdiff] at hd
  refine hd.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  have hδ0 : ((δ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt (Set.mem_Ioi.1 hδ)
  rw [slope, ftPrincipal_ftTauLower_zero, vsub_eq_sub, sub_zero, Complex.real_smul,
    Complex.ofReal_inv]
  field_simp

/-- **The principal pair's cluster indices.**  The completeness field of
`exists_retained_set_of_two_le_rho` puts both members of the principal pair in the
cluster, each carries its own endpoint slope, and `exists_cluster_index_of_cover`
reads off the one member whose slope matches.  From then on each *is* that member,
which is what lets the residue asymptotics be stated per index and what turns the
retained cardinality `ρ` into `n_0 = ρ - 2`.

The two indices are distinct because the two slopes are: they are conjugate and
`clusterAlpha_im` says the imaginary part is `x_1 ≠ 0`.  That is the whole content
of "the pair is genuine" at the level of the enumeration, and it is why `ρ - 2` is
the right count rather than `ρ - 1`. -/
theorem exists_principal_pair_cluster_indices_of_two_le_rho {n r ρ : ℕ} {a : Fin n → ℝ}
    {c x₁ : ℝ}
    (hn2 : 2 ≤ n) (ha : ∀ k, 0 < a k) (hc : 0 < c) (hr : 1 ≤ r) (hne1 : ¬(r = 1 ∧ n = 2))
    (hx₁ : 0 < x₁) (hmin : ∀ k, x₁ ≤ a k)
    (hcard : (Finset.univ.filter fun k => a k = x₁).card = ρ) (hρ : 2 ≤ ρ) :
    ∃ (ψ : ℂ → ℂ) (jp jc : ℕ), jp < ρ ∧ jc < ρ ∧ jc = (1 + jp) % ρ
      ∧ (∀ j : ℕ, Filter.Tendsto
          (fun δ : ℝ => (ψ (clusterDir ρ j
              * ((ftClusterParam a c r (n - 1) ρ δ : ℝ) : ℂ)) - ((x₁ : ℝ) : ℂ))
            / ((δ : ℝ) : ℂ))
          (𝓝[>] (0 : ℝ)) (𝓝 (clusterAlpha x₁ ρ ((j + ρ - jp) % ρ))))
      ∧ ∃ e > (0 : ℝ), ∀ δ : ℝ, 0 < δ → δ ≤ e →
        ftPrincipal (ftTauLower a r (n - 1) x₁) δ
            = ψ (clusterDir ρ jp * ((ftClusterParam a c r (n - 1) ρ δ : ℝ) : ℂ))
          ∧ (starRingEnd ℂ) (ftPrincipal (ftTauLower a r (n - 1) x₁) δ)
            = ψ (clusterDir ρ jc * ((ftClusterParam a c r (n - 1) ρ δ : ℝ) : ℂ))
          ∧ (ftClusterSet a c r (n - 1) ρ ψ δ).card = ρ
          ∧ (∀ w ∈ ftClusterSet a c r (n - 1) ρ ψ δ, (ftDen (ftRootPoly c a) r
              ((ftBranchZLower a c r (n - 1) δ : ℝ) : ℂ)).eval w = 0)
          ∧ (∀ w ∈ ftClusterSet a c r (n - 1) ρ ψ δ, ‖w‖ < ftSepRadius a x₁)
          ∧ (∀ w ∈ ftClusterSet a c r (n - 1) ρ ψ δ,
              (Polynomial.derivative (ftDen (ftRootPoly c a) r
                ((ftBranchZLower a c r (n - 1) δ : ℝ) : ℂ))).eval w ≠ 0)
          ∧ (∀ w : ℂ, ‖w‖ ≤ ftSepRadius a x₁ →
              (ftDen (ftRootPoly c a) r
                ((ftBranchZLower a c r (n - 1) δ : ℝ) : ℂ)).eval w = 0 →
              w ∈ ftClusterSet a c r (n - 1) ρ ψ δ) := by
  classical
  have hn : 0 < n := by omega
  have hnr : 2 ≤ n ∨ 2 ≤ r := Or.inl hn2
  obtain ⟨ψ, γe, L, hγe, hL, hslope, e₀, he₀, hfields⟩ :=
    exists_retained_set_of_two_le_rho hn ha hc hr hnr hx₁ hmin hcard hρ
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hhalf : 0 < Real.pi / r / 2 := div_pos (div_pos Real.pi_pos hrR) two_pos
  obtain ⟨hτpos, hτle, hrootplus, _⟩ :=
    endpoint_retained_partial_of_two_le_rho (c := c) hn2 ha hr hne1 hmin hcard hρ
      (e₀ := min e₀ (Real.pi / r / 2))
      (lt_of_le_of_lt (min_le_right _ _) (by linarith))
  -- the window, and on it the two facts every covering needs
  have hwin : ∀ᶠ δ in 𝓝[>] (0 : ℝ), δ ≤ min e₀ (Real.pi / r / 2) := by
    refine eventually_nhdsWithin_of_eventually_nhds ?_
    exact (continuousAt_id (x := (0 : ℝ))).eventually_le_const (lt_min he₀ hhalf)
  have hcover : ∀ (P : ℝ → ℂ),
      (∀ δ : ℝ, 0 < δ → δ ≤ min e₀ (Real.pi / r / 2) →
        (ftDen (ftRootPoly c a) r ((ftBranchZLower a c r (n - 1) δ : ℝ) : ℂ)).eval (P δ) = 0
          ∧ ‖P δ‖ ≤ ftSepRadius a x₁) →
      ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∃ j ∈ Finset.range ρ,
        P δ = ψ (clusterDir ρ j * ((ftClusterParam a c r (n - 1) ρ δ : ℝ) : ℂ)) := by
    intro P hP
    filter_upwards [hwin, self_mem_nhdsWithin] with δ hδe hδ
    obtain ⟨_, _, _, _, hcomplete⟩ := hfields δ hδ (le_trans hδe (min_le_left _ _))
    obtain ⟨h0, hn0⟩ := hP δ hδ hδe
    obtain ⟨j, hj, hje⟩ := mem_ftClusterSet.1 (hcomplete _ hn0 h0)
    exact ⟨j, hj, hje.symm⟩
  have hbase : ∀ δ : ℝ, 0 < δ → δ ≤ min e₀ (Real.pi / r / 2) →
      (ftDen (ftRootPoly c a) r ((ftBranchZLower a c r (n - 1) δ : ℝ) : ℂ)).eval
          (ftPrincipal (ftTauLower a r (n - 1) x₁) δ) = 0
        ∧ ‖ftPrincipal (ftTauLower a r (n - 1) x₁) δ‖ ≤ ftSepRadius a x₁ := by
    intro δ hδ hδe
    refine ⟨hrootplus δ hδ hδe, ?_⟩
    rw [norm_ftPrincipal_eq (hτpos δ hδ hδe)]
    exact le_trans (hτle δ hδ hδe) (lt_ftSepRadius hmin).le
  have hLne : ((L : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hL
  have hρ0 : ρ ≠ 0 := by omega
  -- the principal branch
  obtain ⟨jp, hjp, hAp, heqp⟩ :=
    exists_cluster_index_of_cover (ρ := ρ) (ψ := ψ) (γe := γe) (L := L)
      (te := ((x₁ : ℝ) : ℂ)) (A := clusterAlpha x₁ ρ 0)
      (V := fun δ => ((ftClusterParam a c r (n - 1) ρ δ : ℝ) : ℂ))
      hρ0 hγe hLne hslope
      (tendsto_ftPrincipal_slope_of_two_le_rho hn ha hr hnr hx₁ hmin hcard hρ)
      (hcover _ hbase)
  -- its conjugate
  have hslopec : Filter.Tendsto
      (fun δ : ℝ => ((starRingEnd ℂ) (ftPrincipal (ftTauLower a r (n - 1) x₁) δ)
          - ((x₁ : ℝ) : ℂ)) / ((δ : ℝ) : ℂ))
      (𝓝[>] (0 : ℝ)) (𝓝 ((starRingEnd ℂ) (clusterAlpha x₁ ρ 0))) := by
    have hst := (tendsto_ftPrincipal_slope_of_two_le_rho hn ha hr hnr hx₁ hmin hcard hρ).star
    refine hst.congr fun δ => ?_
    simp only [RCLike.star_def, map_div₀, map_sub, Complex.conj_ofReal]
  obtain ⟨jc, hjc, hAc, heqc⟩ :=
    exists_cluster_index_of_cover (ρ := ρ) (ψ := ψ) (γe := γe) (L := L)
      (te := ((x₁ : ℝ) : ℂ)) (A := (starRingEnd ℂ) (clusterAlpha x₁ ρ 0))
      (V := fun δ => ((ftClusterParam a c r (n - 1) ρ δ : ℝ) : ℂ))
      hρ0 hγe hLne hslope hslopec
      (hcover _ (fun δ hδ hδe => by
        refine ⟨ftDen_eval_conj_eq_zero (hasRealCoeffs_ftRootPoly c a)
          (hbase δ hδ hδe).1, ?_⟩
        rw [RCLike.norm_conj]
        exact (hbase δ hδ hδe).2))
  -- the arc point is the chart's `j_p + 1`, because `α_1 = conj α_0`
  have hρ0 : ρ ≠ 0 := by omega
  have hjcshift : jc = (1 + jp) % ρ := by
    have hmod : ((1 + jp) % ρ + ρ - jp) % ρ = 1 := by
      rcases lt_or_ge (1 + jp) ρ with h | h
      · rw [Nat.mod_eq_of_lt h, show 1 + jp + ρ - jp = 1 + ρ by omega,
          Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : 1 < ρ)]
      · rw [show 1 + jp = ρ by omega, Nat.mod_self,
          show 0 + ρ - jp = 1 by omega, Nat.mod_eq_of_lt (by omega : 1 < ρ)]
    have h1 : γe * (clusterDir ρ ((1 + jp) % ρ) * ((L : ℝ) : ℂ))
        = clusterAlpha x₁ ρ 1 := by
      rw [clusterSlope_shift hρ0 hjp.le hAp, hmod]
    have h2 : γe * (clusterDir ρ jc * ((L : ℝ) : ℂ))
        = γe * (clusterDir ρ ((1 + jp) % ρ) * ((L : ℝ) : ℂ)) := by
      rw [h1, hAc, conj_clusterAlpha_zero]
    by_contra hne
    exact clusterSlope_inj hρ0 hγe hLne hjc (Nat.mod_lt _ (by omega)) hne h2
  -- the slopes, relabelled from the chart's indexing to the manuscript's
  have hshift : ∀ j : ℕ, Filter.Tendsto
      (fun δ : ℝ => (ψ (clusterDir ρ j
          * ((ftClusterParam a c r (n - 1) ρ δ : ℝ) : ℂ)) - ((x₁ : ℝ) : ℂ))
        / ((δ : ℝ) : ℂ))
      (𝓝[>] (0 : ℝ)) (𝓝 (clusterAlpha x₁ ρ ((j + ρ - jp) % ρ))) := by
    intro j
    have h := hslope j
    rwa [clusterSlope_shift (by omega : ρ ≠ 0) hjp.le hAp j] at h
  -- one window carrying the two identities and the five fields
  refine ⟨ψ, jp, jc, hjp, hjc, hjcshift, hshift, ?_⟩
  have hboth : ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      ftPrincipal (ftTauLower a r (n - 1) x₁) δ
          = ψ (clusterDir ρ jp * ((ftClusterParam a c r (n - 1) ρ δ : ℝ) : ℂ))
        ∧ (starRingEnd ℂ) (ftPrincipal (ftTauLower a r (n - 1) x₁) δ)
          = ψ (clusterDir ρ jc * ((ftClusterParam a c r (n - 1) ρ δ : ℝ) : ℂ)) := by
    filter_upwards [heqp, heqc] with δ h1 h2 using ⟨h1, h2⟩
  rw [eventually_nhdsWithin_iff] at hboth
  obtain ⟨ε₁, hε₁, hball⟩ := Metric.eventually_nhds_iff.mp hboth
  refine ⟨min (ε₁ / 2) e₀, lt_min (by linarith) he₀, fun δ hδ hδe => ?_⟩
  have hd : dist δ (0 : ℝ) < ε₁ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hδ]
    linarith [le_trans hδe (min_le_left (ε₁ / 2) e₀)]
  obtain ⟨hp, hq⟩ := hball hd hδ
  obtain ⟨f1, f2, f3, f4, f5⟩ := hfields δ hδ (le_trans hδe (min_le_right (ε₁ / 2) e₀))
  exact ⟨hp, hq, f1, f2, f3, f4, f5⟩

/-- The index shift, computed.  Both branches are ordinary subtraction, which is
what lets the rest of the bookkeeping be `omega`'s. -/
private theorem shift_mod {ρ j jp : ℕ} (hj : j < ρ) (hjp : jp < ρ) :
    (j + ρ - jp) % ρ = if jp ≤ j then j - jp else j + ρ - jp := by
  by_cases h : jp ≤ j
  · rw [if_pos h, show j + ρ - jp = (j - jp) + ρ by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega)]
  · rw [if_neg h, Nat.mod_eq_of_lt (by omega)]

/-- **`hginj₀`, `hgmem₀` and `hgcard₀`: the nonprincipal cluster, enumerated.**
The two principal indices are erased from `range ρ` and what is left enumerates
the retained cluster.  Two indices come back, and they are **not** the same
function.  `chart` names the point — member `i` is `ψ(ζ_{chart i}·v(δ))` — and
`idx₀` is the manuscript's label for it, `(chart i + ρ - j_p) \bmod ρ`, which is
the index whose `α` is that member's actual slope.  They agree only when the
principal branch is the chart's direction `0`, and nothing makes that so.

Both are fixed once, before `δ`.  An enumeration chosen per angle would satisfy
all three binders below, build green, and leave the residue asymptotics — stated
at `clusterAlpha x_1 ρ (idx₀ i)` — with nothing to be stated against.

`idx₀` never takes the values `0` or `1`: those are the manuscript's labels for
the principal pair, since `α_1 = \overline{α_0}`.  So the retained labels are
`2, …, ρ-1`, which is `eq:lower-cluster-expansion`'s own convention, and
`n_0 = ρ - 2` throughout — at `ρ = 2` the whole group is empty, the manuscript's
"the cluster is the principal pair alone". -/
theorem exists_lower_cluster_enumeration_of_two_le_rho {n r ρ : ℕ} {a : Fin n → ℝ}
    {c x₁ : ℝ}
    (hn2 : 2 ≤ n) (ha : ∀ k, 0 < a k) (hc : 0 < c) (hr : 1 ≤ r) (hne1 : ¬(r = 1 ∧ n = 2))
    (hx₁ : 0 < x₁) (hmin : ∀ k, x₁ ≤ a k)
    (hcard : (Finset.univ.filter fun k => a k = x₁).card = ρ) (hρ : 2 ≤ ρ) :
    ∃ (ψ : ℂ → ℂ) (chart idx₀ : Fin (ρ - 2) → ℕ),
      (∀ i, chart i < ρ) ∧ Function.Injective chart
      ∧ (∀ i, idx₀ i ≠ 0 ∧ idx₀ i ≠ 1)
      ∧ (∀ i : Fin (ρ - 2), Filter.Tendsto
          (fun δ : ℝ => (ψ (clusterDir ρ (chart i)
              * ((ftClusterParam a c r (n - 1) ρ δ : ℝ) : ℂ)) - ((x₁ : ℝ) : ℂ))
            / ((δ : ℝ) : ℂ))
          (𝓝[>] (0 : ℝ)) (𝓝 (clusterAlpha x₁ ρ (idx₀ i))))
      ∧ ∃ e > (0 : ℝ), ∀ δ : ℝ, 0 < δ → δ ≤ e →
        Function.Injective (fun i : Fin (ρ - 2) =>
            ψ (clusterDir ρ (chart i) * ((ftClusterParam a c r (n - 1) ρ δ : ℝ) : ℂ)))
          ∧ (∀ i : Fin (ρ - 2),
              ψ (clusterDir ρ (chart i) * ((ftClusterParam a c r (n - 1) ρ δ : ℝ) : ℂ))
                ∈ ((ftClusterSet a c r (n - 1) ρ ψ δ).erase
                    (ftPrincipal (ftTauLower a r (n - 1) x₁) δ)).erase
                  (((ftTauLower a r (n - 1) x₁ δ : ℝ) : ℂ)
                    * Complex.exp (-((δ : ℝ) : ℂ) * Complex.I)))
          ∧ (((ftClusterSet a c r (n - 1) ρ ψ δ).erase
                (ftPrincipal (ftTauLower a r (n - 1) x₁) δ)).erase
              (((ftTauLower a r (n - 1) x₁ δ : ℝ) : ℂ)
                * Complex.exp (-((δ : ℝ) : ℂ) * Complex.I))).card = ρ - 2 := by
  classical
  obtain ⟨ψ, jp, jc, hjp, hjc, hjcshift, hshift, e, he, hall⟩ :=
    exists_principal_pair_cluster_indices_of_two_le_rho hn2 ha hc hr hne1 hx₁ hmin hcard hρ
  have hjpc : jp ≠ jc := by
    rw [hjcshift]
    rcases lt_or_ge (1 + jp) ρ with h | h
    · rw [Nat.mod_eq_of_lt h]; omega
    · rw [show 1 + jp = ρ by omega, Nat.mod_self]; omega
  set J : Finset ℕ := ((Finset.range ρ).erase jp).erase jc with hJdef
  have hjpm : jp ∈ Finset.range ρ := Finset.mem_range.2 hjp
  have hjcm : jc ∈ (Finset.range ρ).erase jp :=
    Finset.mem_erase.2 ⟨Ne.symm hjpc, Finset.mem_range.2 hjc⟩
  have hJ : J.card = ρ - 2 := by
    rw [hJdef, Finset.card_erase_of_mem hjcm, Finset.card_erase_of_mem hjpm,
      Finset.card_range]
    omega
  set chart : Fin (ρ - 2) → ℕ := fun i => ((J.orderIsoOfFin hJ i : J) : ℕ) with hidx
  have hmemJ : ∀ i, chart i ∈ J := fun i => (J.orderIsoOfFin hJ i).2
  have hlt : ∀ i, chart i < ρ := fun i =>
    Finset.mem_range.1 (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase (hmemJ i)))
  have hnejp : ∀ i, chart i ≠ jp := fun i =>
    Finset.ne_of_mem_erase (Finset.mem_of_mem_erase (hmemJ i))
  have hnejc : ∀ i, chart i ≠ jc := fun i => Finset.ne_of_mem_erase (hmemJ i)
  have hinj : Function.Injective chart := fun i j hij =>
    (J.orderIsoOfFin hJ).injective (Subtype.ext hij)
  have hjcval : (jp + 1 < ρ ∧ jc = jp + 1) ∨ (jp + 1 = ρ ∧ jc = 0) := by
    rcases lt_or_ge (1 + jp) ρ with h | h
    · exact Or.inl ⟨by omega, by rw [hjcshift, Nat.mod_eq_of_lt h]; omega⟩
    · exact Or.inr ⟨by omega, by rw [hjcshift, show 1 + jp = ρ by omega, Nat.mod_self]⟩
  have hnot01 : ∀ i, (chart i + ρ - jp) % ρ ≠ 0 ∧ (chart i + ρ - jp) % ρ ≠ 1 := by
    intro i
    have hci := hlt i
    have hp := hnejp i
    have hq := hnejc i
    rw [shift_mod hci hjp]
    rcases hjcval with ⟨hltρ, hv⟩ | ⟨heρ, hv⟩ <;> split_ifs with h <;>
      exact ⟨by omega, by omega⟩
  refine ⟨ψ, chart, fun i => (chart i + ρ - jp) % ρ, hlt, hinj, hnot01,
    fun i => hshift (chart i), e, he, fun δ hδ hδe => ?_⟩
  obtain ⟨hp, hq, hcardS, _, _, _, _⟩ := hall δ hδ hδe
  -- the chart map is injective on `range ρ`, because the image has `ρ` elements
  have hInjOn : Set.InjOn
      (fun j => ψ (clusterDir ρ j * ((ftClusterParam a c r (n - 1) ρ δ : ℝ) : ℂ)))
      (Finset.range ρ) := by
    refine Finset.injOn_of_card_image_eq ?_
    change (ftClusterSet a c r (n - 1) ρ ψ δ).card = (Finset.range ρ).card
    rw [hcardS, Finset.card_range]
  have harc : (((ftTauLower a r (n - 1) x₁ δ : ℝ) : ℂ)
      * Complex.exp (-((δ : ℝ) : ℂ) * Complex.I))
      = ψ (clusterDir ρ jc * ((ftClusterParam a c r (n - 1) ρ δ : ℝ) : ℂ)) := by
    rw [← conj_ftPrincipal (τ := ftTauLower a r (n - 1) x₁) δ]
    exact hq
  have hmemS : ∀ j : ℕ, j < ρ →
      ψ (clusterDir ρ j * ((ftClusterParam a c r (n - 1) ρ δ : ℝ) : ℂ))
        ∈ ftClusterSet a c r (n - 1) ρ ψ δ :=
    fun j hj => mem_ftClusterSet.2 ⟨j, Finset.mem_range.2 hj, rfl⟩
  have hchartne : ∀ i j : ℕ, i < ρ → j < ρ → i ≠ j →
      ψ (clusterDir ρ i * ((ftClusterParam a c r (n - 1) ρ δ : ℝ) : ℂ))
        ≠ ψ (clusterDir ρ j * ((ftClusterParam a c r (n - 1) ρ δ : ℝ) : ℂ)) := by
    intro i j hi hj hij hEq
    exact hij (hInjOn (Finset.mem_coe.2 (Finset.mem_range.2 hi))
      (Finset.mem_coe.2 (Finset.mem_range.2 hj)) hEq)
  refine ⟨fun i j hij => hinj (hInjOn (Finset.mem_coe.2 (Finset.mem_range.2 (hlt i)))
    (Finset.mem_coe.2 (Finset.mem_range.2 (hlt j))) hij), fun i => ?_, ?_⟩
  · refine Finset.mem_erase.2 ⟨?_, Finset.mem_erase.2 ⟨?_, hmemS _ (hlt i)⟩⟩
    · rw [harc]; exact hchartne _ _ (hlt i) hjc (hnejc i)
    · rw [hp]; exact hchartne _ _ (hlt i) hjp (hnejp i)
  · have hpS : ftPrincipal (ftTauLower a r (n - 1) x₁) δ
        ∈ ftClusterSet a c r (n - 1) ρ ψ δ := by rw [hp]; exact hmemS _ hjp
    have hqS : (((ftTauLower a r (n - 1) x₁ δ : ℝ) : ℂ)
        * Complex.exp (-((δ : ℝ) : ℂ) * Complex.I))
        ∈ (ftClusterSet a c r (n - 1) ρ ψ δ).erase
          (ftPrincipal (ftTauLower a r (n - 1) x₁) δ) := by
      refine Finset.mem_erase.2 ⟨?_, by rw [harc]; exact hmemS _ hjc⟩
      rw [harc, hp]
      exact hchartne _ _ hjc hjp (Ne.symm hjpc)
    rw [Finset.card_erase_of_mem hqS, Finset.card_erase_of_mem hpS, hcardS]
    omega

/-! ### The residue asymptotics: leading behavior along a member -/

/-- **A polynomial's leading behavior along a point entering `t_e` linearly.**  If
`t(δ) - t_e = Aδ + o(δ)` and `P` vanishes to order `ν` at `t_e`, then
`P(t(δ))/δ^ν → A^ν·H(t_e)` with `H = P /ₘ (X - t_e)^ν` the nonvanishing cofactor.

This is `hBj₀` and `hBp₀` in one lemma and half of `hEj₀`, and it is where the
manuscript's "the leading behavior of `B` and of `∂_tD` along each branch" is
actually produced.  Nothing about the cluster enters: only the slope. -/
theorem tendsto_eval_div_pow_of_slope (P : Polynomial ℂ) {te A : ℂ}
    {t : ℝ → ℂ}
    (hslope : Filter.Tendsto (fun δ : ℝ => (t δ - te) / ((δ : ℝ) : ℂ))
      (𝓝[>] (0 : ℝ)) (𝓝 A)) :
    Filter.Tendsto
      (fun δ : ℝ => P.eval (t δ) / ((δ : ℝ) : ℂ) ^ (P.rootMultiplicity te))
      (𝓝[>] (0 : ℝ))
      (𝓝 (A ^ (P.rootMultiplicity te)
        * (P /ₘ (Polynomial.X - Polynomial.C te) ^ (P.rootMultiplicity te)).eval te)) := by
  classical
  set ν := P.rootMultiplicity te with hν
  set H := P /ₘ (Polynomial.X - Polynomial.C te) ^ ν with hH
  have hfac : ∀ w : ℂ, P.eval w = (w - te) ^ ν * H.eval w := by
    intro w
    conv_lhs => rw [← Polynomial.pow_mul_divByMonic_rootMultiplicity_eq P te]
    simp [hH, hν]
  -- the point itself converges, so the cofactor's value does
  have hid : Filter.Tendsto (fun δ : ℝ => ((δ : ℝ) : ℂ)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hcont : Continuous fun δ : ℝ => ((δ : ℝ) : ℂ) := Complex.continuous_ofReal
    simpa using (hcont.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
  have hsub : Filter.Tendsto (fun δ : ℝ => t δ - te) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hmul := hslope.mul hid
    rw [mul_zero] at hmul
    refine hmul.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    have hne : ((δ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hδ
    field_simp
  have hpt : Filter.Tendsto t (𝓝[>] (0 : ℝ)) (𝓝 te) := by
    have := hsub.add_const te
    simpa using this
  have hcof : Filter.Tendsto (fun δ : ℝ => H.eval (t δ)) (𝓝[>] (0 : ℝ)) (𝓝 (H.eval te)) :=
    (H.continuous_aeval.tendsto te).comp hpt
  have hlim := (hslope.pow ν).mul hcof
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  have hne : ((δ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hδ
  rw [hfac (t δ), div_pow]
  field_simp

/-- **`hBj₀`, `hBp₀`, `hEj₀` and `hEp₀`: the residue asymptotics.**  Along any
family of points entering `x_1` with slope `α_{idx i}` — the cluster members and
the principal branch alike — the numerator and `∂_tD` have the leading behavior
`eq:lower-residue-ratio` is derived from.

The two constants are the nonvanishing cofactors at `x_1`: `c_B` of `B` at its own
multiplicity `ν_B`, and `c_Q` of `Q'` at `ρ-1`.  Neither is assumed; both are what
`Polynomial.eval_divByMonic_pow_rootMultiplicity_ne_zero` returns.

The spectral parameter contributes nothing to `∂_tD`: it enters as
`z(δ)·r·t^{r-1}` and `z(δ)/δ^ρ` converges, so that term is `O(δ)` after the
division by `δ^{ρ-1}` and drops.  That is why `∂_tD`'s order is the denominator's
`ρ-1` rather than something the pencil could change. -/
theorem exists_residue_asymptotics_of_slopes {n r ρ : ℕ} {a : Fin n → ℝ} {c x₁ : ℝ}
    {B : Polynomial ℂ}
    (hn2 : 2 ≤ n) (ha : ∀ k, 0 < a k) (hc : 0 < c) (hr : 1 ≤ r)
    (hx₁ : 0 < x₁) (hmin : ∀ k, x₁ ≤ a k)
    (hcard : (Finset.univ.filter fun k => a k = x₁).card = ρ) (hρ : 2 ≤ ρ) (hB0 : B ≠ 0)
    {m : ℕ} {t : Fin m → ℝ → ℂ} {idx : Fin m → ℕ}
    (hslopes : ∀ i : Fin m, Filter.Tendsto
      (fun δ : ℝ => (t i δ - ((x₁ : ℝ) : ℂ)) / ((δ : ℝ) : ℂ))
      (𝓝[>] (0 : ℝ)) (𝓝 (clusterAlpha x₁ ρ (idx i)))) :
    ∃ cB cQ : ℂ, cB ≠ 0 ∧ cQ ≠ 0
      ∧ (∀ i : Fin m, Filter.Tendsto
          (fun δ : ℝ => B.eval (t i δ)
            / ((δ : ℝ) : ℂ) ^ (B.rootMultiplicity ((x₁ : ℝ) : ℂ)))
          (𝓝[>] (0 : ℝ))
          (𝓝 (cB * clusterAlpha x₁ ρ (idx i) ^ (B.rootMultiplicity ((x₁ : ℝ) : ℂ)))))
      ∧ (∀ i : Fin m, Filter.Tendsto
          (fun δ : ℝ => (Polynomial.derivative (ftDen (ftRootPoly c a) r
              ((ftBranchZLower a c r (n - 1) δ : ℝ) : ℂ))).eval (t i δ)
            / ((δ : ℝ) : ℂ) ^ (ρ - 1))
          (𝓝[>] (0 : ℝ)) (𝓝 (cQ * clusterAlpha x₁ ρ (idx i) ^ (ρ - 1)))) := by
  classical
  have hn : 0 < n := by omega
  have hnr : 2 ≤ n ∨ 2 ≤ r := Or.inl hn2
  have hQ0 : ftRootPoly c a ≠ 0 := ftRootPoly_ne_zero' hc.ne' ha
  -- the multiplicity of `x₁` in `Q`, and hence in `Q'`
  have hmult : (ftRootPoly c a).rootMultiplicity ((x₁ : ℝ) : ℂ) = ρ := by
    rw [rootMultiplicity_ftRootPoly hc.ne' a x₁, hcard]
  have hroot : (ftRootPoly c a).IsRoot ((x₁ : ℝ) : ℂ) := by
    rw [← Polynomial.rootMultiplicity_pos hQ0, hmult]; omega
  have hdmult : (Polynomial.derivative (ftRootPoly c a)).rootMultiplicity ((x₁ : ℝ) : ℂ)
      = ρ - 1 := by
    rw [Polynomial.derivative_rootMultiplicity_of_root hroot, hmult]
  have hdQ0 : Polynomial.derivative (ftRootPoly c a) ≠ 0 := by
    intro h0
    have := Polynomial.eval_divByMonic_pow_rootMultiplicity_ne_zero
      (p := ftRootPoly c a) ((x₁ : ℝ) : ℂ) hQ0
    have hzero : (ftRootPoly c a).rootMultiplicity ((x₁ : ℝ) : ℂ) = 0 := by
      by_contra hne
      have hpos : 0 < (ftRootPoly c a).rootMultiplicity ((x₁ : ℝ) : ℂ) := Nat.pos_of_ne_zero hne
      have hd := Polynomial.derivative_rootMultiplicity_of_root hroot
      rw [h0, Polynomial.rootMultiplicity_zero] at hd
      omega
    omega
  refine ⟨(B /ₘ (Polynomial.X - Polynomial.C ((x₁ : ℝ) : ℂ))
      ^ (B.rootMultiplicity ((x₁ : ℝ) : ℂ))).eval ((x₁ : ℝ) : ℂ),
    (Polynomial.derivative (ftRootPoly c a)
      /ₘ (Polynomial.X - Polynomial.C ((x₁ : ℝ) : ℂ)) ^ (ρ - 1)).eval ((x₁ : ℝ) : ℂ),
    Polynomial.eval_divByMonic_pow_rootMultiplicity_ne_zero _ hB0, ?_, ?_, ?_⟩
  · have h := Polynomial.eval_divByMonic_pow_rootMultiplicity_ne_zero
      (p := Polynomial.derivative (ftRootPoly c a)) ((x₁ : ℝ) : ℂ) hdQ0
    rwa [hdmult] at h
  · intro i
    have h := tendsto_eval_div_pow_of_slope B (hslopes i)
    rwa [mul_comm (clusterAlpha x₁ ρ (idx i) ^ B.rootMultiplicity ((x₁ : ℝ) : ℂ))] at h
  · intro i
    -- the `∂_tQ` half, at multiplicity `ρ - 1`
    have hd := tendsto_eval_div_pow_of_slope (Polynomial.derivative (ftRootPoly c a))
      (hslopes i)
    rw [hdmult] at hd
    -- the pencil's own term vanishes after dividing by `δ^{ρ-1}`
    obtain ⟨Az, _, hz⟩ :=
      exists_tendsto_z_div_pow_of_two_le_rho hn ha hc hr hnr hx₁ hmin hcard hρ
    have hid : Filter.Tendsto (fun δ : ℝ => ((δ : ℝ) : ℂ)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have hcont : Continuous fun δ : ℝ => ((δ : ℝ) : ℂ) := Complex.continuous_ofReal
      simpa using (hcont.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
    have hsub : Filter.Tendsto (fun δ : ℝ => t i δ - ((x₁ : ℝ) : ℂ))
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have hmul := (hslopes i).mul hid
      rw [mul_zero] at hmul
      refine hmul.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with δ hδ
      have hne : ((δ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hδ
      field_simp
    have hpt : Filter.Tendsto (t i) (𝓝[>] (0 : ℝ)) (𝓝 ((x₁ : ℝ) : ℂ)) := by
      have := hsub.add_const ((x₁ : ℝ) : ℂ)
      simpa using this
    have hzC : Filter.Tendsto
        (fun δ : ℝ => ((ftBranchZLower a c r (n - 1) δ / δ ^ ρ : ℝ) : ℂ))
        (𝓝[>] (0 : ℝ)) (𝓝 ((Az : ℝ) : ℂ)) :=
      (Complex.continuous_ofReal.tendsto (Az : ℝ)).comp hz
    have htail : Filter.Tendsto
        (fun δ : ℝ => ((ftBranchZLower a c r (n - 1) δ / δ ^ ρ : ℝ) : ℂ) * ((δ : ℝ) : ℂ)
          * ((r : ℂ) * t i δ ^ (r - 1)))
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have hcont : Continuous fun w : ℂ => (r : ℂ) * w ^ (r - 1) := by fun_prop
      have hlim := (hzC.mul hid).mul ((hcont.tendsto ((x₁ : ℝ) : ℂ)).comp hpt)
      simpa using hlim
    have hsum := hd.add htail
    rw [add_zero] at hsum
    have hfinal : Filter.Tendsto
        (fun δ : ℝ => (Polynomial.derivative (ftDen (ftRootPoly c a) r
            ((ftBranchZLower a c r (n - 1) δ : ℝ) : ℂ))).eval (t i δ)
          / ((δ : ℝ) : ℂ) ^ (ρ - 1))
        (𝓝[>] (0 : ℝ))
        (𝓝 (clusterAlpha x₁ ρ (idx i) ^ (ρ - 1)
          * (Polynomial.derivative (ftRootPoly c a)
              /ₘ (Polynomial.X - Polynomial.C ((x₁ : ℝ) : ℂ)) ^ (ρ - 1)).eval
            ((x₁ : ℝ) : ℂ))) := by
      refine hsum.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with δ hδ
      have hne : ((δ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hδ
      have hρ1 : ρ - 1 + 1 = ρ := by omega
      have heval : (Polynomial.derivative (ftDen (ftRootPoly c a) r
            ((ftBranchZLower a c r (n - 1) δ : ℝ) : ℂ))).eval (t i δ)
          = (Polynomial.derivative (ftRootPoly c a)).eval (t i δ)
            + ((ftBranchZLower a c r (n - 1) δ : ℝ) : ℂ)
              * ((r : ℂ) * t i δ ^ (r - 1)) := by
        rw [ftDen, Polynomial.derivative_add, Polynomial.derivative_C_mul,
          Polynomial.derivative_X_pow]
        simp
      have hpow : ((δ : ℝ) : ℂ) ^ ρ = ((δ : ℝ) : ℂ) ^ (ρ - 1) * ((δ : ℝ) : ℂ) := by
        rw [← pow_succ, hρ1]
      have hd1 : ((δ : ℝ) : ℂ) ^ (ρ - 1) ≠ 0 := pow_ne_zero _ hne
      rw [heval]
      push_cast
      rw [hpow]
      field_simp
    rwa [mul_comm (clusterAlpha x₁ ρ (idx i) ^ (ρ - 1))] at hfinal

/-! ### `eq:endpoint-linear-gap`: the modulus gap along the cluster -/

/-- **The modulus's slope is the real part of the point's.**  If `z(δ) = 1 + wδ +
o(δ)` then `‖z(δ)‖ = 1 + (\Re w)δ + o(δ)`.

Proved through `‖z‖² - 1 = (\Re z - 1)(\Re z + 1) + (\Im z)²` rather than through
any differentiability of the norm, which is not differentiable at points the
argument would have to pass through in a more general statement. -/
theorem tendsto_norm_sub_one_div_of_slope {z : ℝ → ℂ} {w : ℂ}
    (hz : Filter.Tendsto (fun δ : ℝ => (z δ - 1) / ((δ : ℝ) : ℂ))
      (𝓝[>] (0 : ℝ)) (𝓝 w)) :
    Filter.Tendsto (fun δ : ℝ => (‖z δ‖ - 1) / δ) (𝓝[>] (0 : ℝ)) (𝓝 w.re) := by
  have hid : Filter.Tendsto (fun δ : ℝ => ((δ : ℝ) : ℂ)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hcont : Continuous fun δ : ℝ => ((δ : ℝ) : ℂ) := Complex.continuous_ofReal
    simpa using (hcont.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
  have hz1 : Filter.Tendsto z (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    have hmul := hz.mul hid
    rw [mul_zero] at hmul
    have hsub : Filter.Tendsto (fun δ : ℝ => z δ - 1) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      refine hmul.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with δ hδ
      have hne : ((δ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hδ
      field_simp
    have := hsub.add_const (1 : ℂ)
    simpa using this
  have hre : Filter.Tendsto (fun δ : ℝ => ((z δ).re - 1) / δ) (𝓝[>] (0 : ℝ)) (𝓝 w.re) := by
    refine ((Complex.continuous_re.tendsto w).comp hz).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    have hδ0 : δ ≠ 0 := ne_of_gt hδ
    simp only [Function.comp_apply, Complex.div_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im, Complex.normSq_apply]
    field_simp
    ring
  have him : Filter.Tendsto (fun δ : ℝ => (z δ).im / δ) (𝓝[>] (0 : ℝ)) (𝓝 w.im) := by
    refine ((Complex.continuous_im.tendsto w).comp hz).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    have hδ0 : δ ≠ 0 := ne_of_gt hδ
    simp only [Function.comp_apply, Complex.div_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im, Complex.normSq_apply]
    field_simp
    ring
  have hzre : Filter.Tendsto (fun δ : ℝ => (z δ).re + 1) (𝓝[>] (0 : ℝ)) (𝓝 2) := by
    have h := ((Complex.continuous_re.tendsto (1 : ℂ)).comp hz1).add_const (1 : ℝ)
    simpa [Function.comp, show (1 : ℝ) + 1 = 2 by norm_num] using h
  have hzim : Filter.Tendsto (fun δ : ℝ => (z δ).im) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    exact (Complex.continuous_im.tendsto (1 : ℂ)).comp hz1
  have hnsq : Filter.Tendsto (fun δ : ℝ => (‖z δ‖ ^ 2 - 1) / δ)
      (𝓝[>] (0 : ℝ)) (𝓝 (w.re * 2)) := by
    have hlim := (hre.mul hzre).add (him.mul hzim)
    rw [mul_zero, add_zero] at hlim
    refine hlim.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    have hδ0 : δ ≠ 0 := ne_of_gt hδ
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    field_simp
    ring
  have hden : Filter.Tendsto (fun δ : ℝ => ‖z δ‖ + 1) (𝓝[>] (0 : ℝ)) (𝓝 2) := by
    have h := (hz1.norm).add_const (1 : ℝ)
    simpa [show (1 : ℝ) + 1 = 2 by norm_num] using h
  have hdiv : Filter.Tendsto (fun δ : ℝ => ((‖z δ‖ ^ 2 - 1) / δ) / (‖z δ‖ + 1))
      (𝓝[>] (0 : ℝ)) (𝓝 (w.re * 2 / 2)) := hnsq.div hden (by norm_num)
  have hval : w.re * 2 / 2 = w.re := by ring
  rw [hval] at hdiv
  refine hdiv.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  have hδ0 : δ ≠ 0 := ne_of_gt hδ
  have hpos : (0 : ℝ) < ‖z δ‖ + 1 := by positivity
  field_simp
  ring

/-- **`hgapin₀`: `eq:endpoint-linear-gap` from the slopes alone.**  Every member
enters `x_1` with slope `α_{idx i}` and the principal branch with `α_0`, so the
normalized member `g_i(δ)/γ(δ)` enters `1` with slope `(α_{idx i} - α_0)/x_1`,
whose real part is the manuscript's `(\cos(π/ρ) - \Re ω_{idx i})/\sin(π/ρ)`.
That is positive exactly when `idx i` is neither `0` nor `1` — the principal
pair's own labels — which is what `exists_lower_cluster_enumeration_of_two_le_rho`
returns.

**Differs from the paper's route.**  `[Prop.~3]` states the expansion with an
`O(δ^2)` remainder and the gap is read off it.  Here only the first-order limit is
used: a limit above `c_0` is eventually above `c_0`, and no second-order control
is needed.  The manuscript has the stronger statement anyway, so nothing is lost;
what is gained is that the endpoint's second-order behavior never enters, and the
`\sin θ` degeneracy of `ftAngleSumDerivTau` at `θ = 0` is never approached.

`τ` is not differentiated either: `‖γ(δ)‖ = τ(δ)`, so the ratio is a modulus of a
quotient and the branch radius enters only through the principal point's own
slope. -/
theorem exists_linear_gap_of_slopes {ρ : ℕ} {x₁ : ℝ} (hx₁ : 0 < x₁) (hρ : 2 ≤ ρ)
    {m : ℕ} {g : Fin m → ℝ → ℂ} {P : ℝ → ℂ} {τ : ℝ → ℝ} {idx : Fin m → ℕ}
    (hidx : ∀ i, idx i < ρ) (hidx01 : ∀ i, idx i ≠ 0 ∧ idx i ≠ 1)
    (hτ : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ‖P δ‖ = τ δ ∧ P δ ≠ 0)
    (hgs : ∀ i, Filter.Tendsto (fun δ : ℝ => (g i δ - ((x₁ : ℝ) : ℂ)) / ((δ : ℝ) : ℂ))
      (𝓝[>] (0 : ℝ)) (𝓝 (clusterAlpha x₁ ρ (idx i))))
    (hPs : Filter.Tendsto (fun δ : ℝ => (P δ - ((x₁ : ℝ) : ℂ)) / ((δ : ℝ) : ℂ))
      (𝓝[>] (0 : ℝ)) (𝓝 (clusterAlpha x₁ ρ 0))) :
    ∃ c₀ > (0 : ℝ), ∃ e > (0 : ℝ), ∀ δ : ℝ, 0 < δ → δ ≤ e → ∀ i,
      1 + c₀ * δ ≤ ‖g i δ‖ / τ δ := by
  classical
  rcases isEmpty_or_nonempty (Fin m) with hem | hnem
  · exact ⟨1, one_pos, 1, one_pos, fun δ _ _ i => (hem.false i).elim⟩
  have hπ := Real.pi_pos
  have hρR : (0 : ℝ) < ρ := by
    have : (2 : ℝ) ≤ (ρ : ℝ) := by exact_mod_cast hρ
    linarith
  have hsin : 0 < Real.sin (Real.pi / ρ) := by
    refine Real.sin_pos_of_pos_of_lt_pi (by positivity) ?_
    rw [div_lt_iff₀ hρR]
    have : (2 : ℝ) ≤ (ρ : ℝ) := by exact_mod_cast hρ
    nlinarith
  have hxC : ((x₁ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hx₁
  -- the point converges, so the quotient by the principal point does
  have hP1 : Filter.Tendsto P (𝓝[>] (0 : ℝ)) (𝓝 ((x₁ : ℝ) : ℂ)) := by
    have hid : Filter.Tendsto (fun δ : ℝ => ((δ : ℝ) : ℂ)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have hcont : Continuous fun δ : ℝ => ((δ : ℝ) : ℂ) := Complex.continuous_ofReal
      simpa using (hcont.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
    have hmul := hPs.mul hid
    rw [mul_zero] at hmul
    have hsub : Filter.Tendsto (fun δ : ℝ => P δ - ((x₁ : ℝ) : ℂ))
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      refine hmul.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with δ hδ
      have hne : ((δ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hδ
      field_simp
    have := hsub.add_const ((x₁ : ℝ) : ℂ)
    simpa using this
  -- the manuscript's coefficient, as the real part of the normalized slope
  set R : Fin m → ℝ := fun i =>
    (Real.cos (Real.pi / ρ) - (clusterOmega ρ (idx i)).re) / Real.sin (Real.pi / ρ) with hR
  have hRpos : ∀ i, 0 < R i := by
    intro i
    refine endpoint_linear_coeff_pos hρ (clusterOmega_pow (by omega : 1 ≤ ρ) _) ?_ ?_
    · rw [← clusterOmega_one_eq]
      intro hEq
      exact (hidx01 i).2 (clusterOmega_inj (by omega) (hidx i) (by omega) hEq)
    · rw [← clusterOmega_zero_eq]
      intro hEq
      exact (hidx01 i).1 (clusterOmega_inj (by omega) (hidx i) (by omega) hEq)
  have hslopeRe : ∀ i,
      ((clusterAlpha x₁ ρ (idx i) - clusterAlpha x₁ ρ 0) / ((x₁ : ℝ) : ℂ)).re = R i := by
    intro i
    have hsC : ((Real.sin (Real.pi / ρ) : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast ne_of_gt hsin
    have hid : (clusterAlpha x₁ ρ (idx i) - clusterAlpha x₁ ρ 0) / ((x₁ : ℝ) : ℂ)
        = -(clusterOmega ρ (idx i) - clusterOmega ρ 0)
          / ((Real.sin (Real.pi / ρ) : ℝ) : ℂ) := by
      rw [clusterAlpha, clusterAlpha]
      field_simp
      ring
    have hω0 : (clusterOmega ρ 0).re = Real.cos (Real.pi / ρ) := by
      rw [clusterOmega_zero_eq, Complex.exp_ofReal_mul_I_re, Real.cos_neg]
    rw [hid, hR]
    simp only [Complex.div_re, Complex.ofReal_re, Complex.ofReal_im, Complex.neg_re,
      Complex.neg_im, Complex.sub_re, Complex.sub_im, Complex.normSq_apply, hω0]
    field_simp
    ring
  -- each normalized member's modulus rises at rate `R i`
  have hgap : ∀ i, Filter.Tendsto (fun δ : ℝ => (‖g i δ‖ / τ δ - 1) / δ)
      (𝓝[>] (0 : ℝ)) (𝓝 (R i)) := by
    intro i
    have hquot : Filter.Tendsto (fun δ : ℝ => (g i δ / P δ - 1) / ((δ : ℝ) : ℂ))
        (𝓝[>] (0 : ℝ))
        (𝓝 ((clusterAlpha x₁ ρ (idx i) - clusterAlpha x₁ ρ 0) / ((x₁ : ℝ) : ℂ))) := by
      have hnum := (hgs i).sub hPs
      have hdiv : Filter.Tendsto
          (fun δ : ℝ => ((g i δ - ((x₁ : ℝ) : ℂ)) / ((δ : ℝ) : ℂ)
            - (P δ - ((x₁ : ℝ) : ℂ)) / ((δ : ℝ) : ℂ)) / P δ)
          (𝓝[>] (0 : ℝ))
          (𝓝 ((clusterAlpha x₁ ρ (idx i) - clusterAlpha x₁ ρ 0) / ((x₁ : ℝ) : ℂ))) :=
        hnum.div hP1 hxC
      refine hdiv.congr' ?_
      filter_upwards [self_mem_nhdsWithin, hτ] with δ hδ hpd
      have hne : ((δ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hδ
      have hPne : P δ ≠ 0 := hpd.2
      field_simp
      ring
    have hnorm := tendsto_norm_sub_one_div_of_slope hquot
    rw [hslopeRe i] at hnorm
    refine hnorm.congr' ?_
    filter_upwards [hτ] with δ hpd
    rw [norm_div, hpd.1]
  -- one rate for the whole family
  set c₀ : ℝ := (Finset.univ.inf' Finset.univ_nonempty R) / 2 with hc₀
  have hc₀pos : 0 < c₀ := by
    rw [hc₀]
    have : 0 < Finset.univ.inf' Finset.univ_nonempty R :=
      (Finset.lt_inf'_iff Finset.univ_nonempty).2 fun i _ => hRpos i
    linarith
  have hc₀lt : ∀ i, c₀ < R i := by
    intro i
    have hle : Finset.univ.inf' Finset.univ_nonempty R ≤ R i :=
      Finset.inf'_le _ (Finset.mem_univ i)
    have := hRpos i
    rw [hc₀]; linarith
  have hev : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∀ i ∈ (Finset.univ : Finset (Fin m)),
      c₀ < (‖g i δ‖ / τ δ - 1) / δ :=
    (Filter.eventually_all_finset _).2 fun i _ => (hgap i).eventually_const_lt (hc₀lt i)
  rw [eventually_nhdsWithin_iff] at hev
  obtain ⟨ε₀, hε₀, hball⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨c₀, hc₀pos, ε₀ / 2, by linarith, fun δ hδ hδe i => ?_⟩
  have hd : dist δ (0 : ℝ) < ε₀ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hδ]; linarith
  have h := hball hd hδ i (Finset.mem_univ i)
  rw [lt_div_iff₀ hδ] at h
  linarith

/-! ### The upper endpoint's window on the spectral parameter -/

/-- **The branch's spectral parameter clears the upper circle's threshold.**  At
`r ≥ 2` the upper endpoint sends `z → +∞`, so `ftUpperWindow ≤ ‖z‖` — which
`EndpointSeparation`'s whole upper section is conditioned on — holds on a window of
angles.  At `r = 1` it does not, and cannot: `z` is bounded there.  That is why
`2 ≤ r` is a hypothesis here rather than `1 ≤ r`. -/
theorem exists_upper_z_window {n r : ℕ} {a : Fin n → ℝ} {c x₁ : ℝ}
    (hn : 0 < n) (ha : ∀ k, 0 < a k) (hc : 0 < c) (hr : 2 ≤ r) :
    ∃ e > (0 : ℝ), ∀ δ : ℝ, 0 < δ → δ ≤ e →
      ftUpperWindow c a x₁ r
        ≤ ‖((ftBranchZ a c r (n - 1) (Real.pi / r - δ) : ℝ) : ℂ)‖ := by
  have hr0 : (0 : ℝ) < r := by
    have : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
    linarith
  have hb : 0 < Real.pi / r := div_pos Real.pi_pos hr0
  have hsmall : ∀ᶠ δ in 𝓝[>] (0 : ℝ), δ < Real.pi / r := by
    refine eventually_nhdsWithin_of_eventually_nhds ?_
    exact (continuousAt_id (x := (0 : ℝ))).eventually_lt_const hb
  have hmap : Filter.Tendsto (fun δ : ℝ => Real.pi / r - δ) (𝓝[>] (0 : ℝ))
      (𝓝[Set.Ioo 0 (Real.pi / r)] (Real.pi / r)) := by
    refine Filter.tendsto_inf.2 ⟨?_, ?_⟩
    · have hcont : Continuous fun δ : ℝ => Real.pi / r - δ := by fun_prop
      simpa using (hcont.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
    · rw [Filter.tendsto_principal]
      filter_upwards [self_mem_nhdsWithin, hsmall] with δ hδ hδb
      have hδ0 : (0 : ℝ) < δ := hδ
      exact Set.mem_Ioo.2 ⟨by linarith, by linarith⟩
  have hcomp := (tendsto_ftBranchZ_atTop_arc_end_of_pos hn ha hc hr).comp hmap
  have hev := hcomp.eventually_ge_atTop (ftUpperWindow c a x₁ r)
  rw [eventually_nhdsWithin_iff] at hev
  obtain ⟨ε₀, hε₀, hball⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨ε₀ / 2, by linarith, fun δ hδ hδe => ?_⟩
  have hd : dist δ (0 : ℝ) < ε₀ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hδ]; linarith
  have hge := hball hd hδ
  rw [Complex.norm_real, Real.norm_eq_abs]
  exact le_trans hge (le_abs_self _)

end ForgacsTran
