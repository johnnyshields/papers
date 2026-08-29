/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import ForgacsTran.PhaseSupplyLowerCollar
import ForgacsTran.PhaseSupplyUpperRegion

/-!
# `eq:phase-derivative-bound` at a general pencil

The last group the general phase supply carries as hypotheses is the three region bounds on
`Im(W'/W)` — the only place the weight `B` enters.  This module produces them.

**The three regions are three different arguments, and the amplitude divisor is why.**
`ArcPhaseLocal`'s observation is that a zero of `W` along the arc contributes a *real*
residue to `W'/W`, so it is invisible to the imaginary part; what remains is bounded by the
branch's own data.  `ArcPhaseBound` turns that into a per-zero collar, and
`exists_bound_im_logDeriv_ftAmp_interiorRegion_of_deriv2` into one constant across a
compact sub-arc, once the divisor is a `Finset` — which `InteriorSupply.ftAmplitudeDivisor`
supplies, because the branch meets each root of `B` at one angle.

At the collision endpoint the same estimate runs against the *endpoint* factorization,
where `E` degenerates too, and takes the branch data
`PhaseSupplyLowerCollar.ft_endpoint_branch_data` packages.

At the origin endpoint no factorization is needed at all: the branch runs into `0`, and
neither `B` nor `E` vanishes there, so `W` does not vanish on that region and the bound is
the two halves of `AmplitudeAlong.abs_im_logDeriv_ftAmpAlong_le` added — the cofactor half
from `PhaseSupplyUpperRegion` and the numerator half from `‖γ'‖` against a ratio that
converges.

Sorry-free.

## Main statements

* `ft_region_lower` — the bound on `Ioc 0 b₁`, at the collision.
* `ft_region_mid` — the bound on `Icc b₁ b₂`, across the whole divisor.
* `ft_region_upper` — the bound on `Ico b₂ (π/r)`, at the origin.

## References

Formalizes `../../shields-2026-forgacs-tran-numerators.tex`,
`lem:amplitude-divisor`, `eq:amplitude-zero-count`, `eq:phase-derivative-bound`.

## Tags

phase derivative, amplitude divisor, region bound, Forgács–Tran
-/

namespace ForgacsTran

open Polynomial Set Real Filter Topology

variable {n r ρ : ℕ} {a : Fin n → ℝ} {c x₁ : ℝ}

/-- **The amplitude's derivative along the arc is its `deriv`.**  `ArcPhaseBound`'s
estimates are stated through `deriv`; the amplitude group names the same function. -/
theorem ft_deriv_ftAmp_eq (B : Polynomial ℂ) (hn : 0 < n) (ha : ∀ k, 0 < a k)
    (hc : c ≠ 0) (hr : 1 ≤ r) (hnr : 2 ≤ n ∨ 2 ≤ r) {s : ℝ}
    (hs : s ∈ Ioo (0 : ℝ) (π / r)) :
    deriv (fun t : ℝ => ftAmp (ftRootPoly c a) B r
        ((ftBranchZLower a c r (n - 1) t : ℝ) : ℂ)
        (ftPrincipal (ftTauArc a r (n - 1) x₁) t)) s = ftArcAmpDeriv a B c r x₁ s :=
  ((ft_amplitude_group (x₁ := x₁) B hn ha hc hr hnr).1 s hs).deriv

/-- **`eq:phase-derivative-bound` on the region at the collision.**  The endpoint
factorization of `ArcPhaseBound`, against the branch data
`ft_endpoint_branch_data` packages — and `E`'s own degeneracy at the collision is what
makes this the endpoint estimate rather than the interior one. -/
theorem ft_region_lower (B : Polynomial ℂ) (hB : B ≠ 0) (hn2 : 2 ≤ n) (ha : ∀ k, 0 < a k)
    (hc : c ≠ 0) (hr : 1 ≤ r) (hx₁ : 0 < x₁) (hmin : ∀ k, x₁ ≤ a k)
    (hcard : (Finset.univ.filter fun k => a k = x₁).card = ρ) (hρ : 2 ≤ ρ) :
    ∃ b₁ C₁ : ℝ, 0 < b₁ ∧ b₁ < π / r ∧ ∀ s ∈ Ioc (0 : ℝ) b₁,
      |(ftArcAmpDeriv a B c r x₁ s / ftAmp (ftRootPoly c a) B r
        ((ftBranchZLower a c r (n - 1) s : ℝ) : ℂ)
        (ftPrincipal (ftTauArc a r (n - 1) x₁) s)).im| ≤ C₁ := by
  classical
  have hn : 0 < n := by omega
  have hnr : 2 ≤ n ∨ 2 ≤ r := Or.inl hn2
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have harc : (0 : ℝ) < π / r := by positivity
  have hstate := ft_branch_state_arc (x₁ := x₁) hn ha hc hr hnr
  obtain ⟨v, L, b, hb0, hblt, hL, hne0, hd0, hd, hlip⟩ :=
    ft_endpoint_branch_data (n := n) (r := r) (ρ := ρ) (a := a) (x₁ := x₁)
      hn2 ha hr hx₁ hmin hcard hρ
  have hE : ftCritical (ftRootPoly c a) r ≠ 0 := by
    intro h
    have hθ : (π / r) / 2 ∈ Ioo (0 : ℝ) (π / r) := ⟨by positivity, by linarith⟩
    exact (hstate _ hθ).2.2 (by rw [ftCriticalAlong, h]; simp)
  have hte : ftPrincipal (ftTauArc a r (n - 1) x₁) 0 ≠ 0 := by
    refine ftPrincipal_ne_zero ?_
    rw [ftTauArc_eq_ftTauArcAt, ftTauArcAt_zero a r (n - 1) x₁ 0 harc]
    exact hx₁.ne'
  obtain ⟨b', C, hb'0, hb'b, hC0, hbd⟩ :=
    exists_bound_im_logDeriv_ftAmp_endpoint (Q := ftRootPoly c a) (B := B) (r := r)
      (γ := ftPrincipal (ftTauArc a r (n - 1) x₁)) (dγ := ftGammaDerivAt a r (n - 1) v)
      (zf := fun s : ℝ => ((ftBranchZLower a c r (n - 1) s : ℝ) : ℂ))
      (te := ftPrincipal (ftTauArc a r (n - 1) x₁) 0)
      (H := ftCriticalReduced (ftRootPoly c a) r (ftTauArc a r (n - 1) x₁) 0)
      (m := ftCollisionOrder (ftRootPoly c a) r (ftTauArc a r (n - 1) x₁) 0)
      hB hr hb0 hL
      (ftCritical_eq_pow_mul_ftCriticalReduced _ _ _ 0)
      (eval_ftCriticalReduced_ne_zero hE 0) hte rfl hd0 hd hlip hne0
      (fun δ hδ => (hstate δ ⟨hδ.1, lt_of_le_of_lt hδ.2 hblt⟩).2.1)
  refine ⟨b', C, hb'0, lt_of_le_of_lt hb'b hblt, fun s hs => ?_⟩
  have hsarc : s ∈ Ioo (0 : ℝ) (π / r) :=
    ⟨hs.1, lt_of_le_of_lt (le_trans hs.2 hb'b) hblt⟩
  rw [← ft_deriv_ftAmp_eq (x₁ := x₁) B hn ha hc hr hnr hsarc]
  exact hbd s hs

/-- **`eq:phase-derivative-bound` on the region at the origin endpoint.**  No factorization
is needed: the branch runs into `0`, where neither `B` nor `E` vanishes, so `W'/W` has no
pole there at all and the bound is the two halves of `abs_im_logDeriv_ftAmpAlong_le` added.

The numerator half is `‖γ'‖` — bounded by `ft_upper_gammaDeriv_bound` — against
`‖B'(γ)‖/‖B(γ)‖`, which converges because `B(0) ≠ 0`. -/
theorem ft_region_upper (B : Polynomial ℂ) (hBev : B.eval 0 ≠ 0) (hn2 : 2 ≤ n)
    (ha : ∀ k, 0 < a k) (hc : c ≠ 0) (hr : 2 ≤ r) :
    ∃ b₂ C₃ : ℝ, 0 < b₂ ∧ b₂ < π / r ∧ ∀ s ∈ Ico b₂ (π / r),
      ftAmp (ftRootPoly c a) B r ((ftBranchZLower a c r (n - 1) s : ℝ) : ℂ)
          (ftPrincipal (ftTauArc a r (n - 1) x₁) s) ≠ 0 →
      |(ftArcAmpDeriv a B c r x₁ s / ftAmp (ftRootPoly c a) B r
        ((ftBranchZLower a c r (n - 1) s : ℝ) : ℂ)
        (ftPrincipal (ftTauArc a r (n - 1) x₁) s)).im| ≤ C₃ := by
  classical
  have hn : 0 < n := by omega
  have hr1 : 1 ≤ r := by omega
  have hnr : 2 ≤ n ∨ 2 ≤ r := Or.inl hn2
  have hrR : (0 : ℝ) < r := by positivity
  have harc : (0 : ℝ) < π / r := by positivity
  obtain ⟨-, -, hS0⟩ := ft_cofactor_group (x₁ := x₁) hn ha hc hr1 hnr
  obtain ⟨bS, CS, hbS0, hbS, hSbd⟩ := ft_upper_region (x₁ := x₁) hn2 ha hc hr
  obtain ⟨bD, D, hbD0, hbD, hDbd⟩ := ft_upper_gammaDeriv_bound (a := a) hn2 ha hr
  -- the numerator ratio converges, because `B` does not vanish at the origin
  set KB : ℝ := ‖(derivative B).eval 0‖ / ‖B.eval 0‖ + 1 with hKB
  have hγ0 := ft_tendsto_ftPrincipal_upper (x₁ := x₁) hn2 ha hr
  have hΛt : Tendsto (fun θ : ℝ =>
      ‖(derivative B).eval (ftPrincipal (ftTauArc a r (n - 1) x₁) θ)‖
        / ‖B.eval (ftPrincipal (ftTauArc a r (n - 1) x₁) θ)‖)
      (𝓝[<] (π / r)) (𝓝 (KB - 1)) := by
    have hp : ∀ P : Polynomial ℂ,
        Tendsto (fun θ : ℝ => P.eval (ftPrincipal (ftTauArc a r (n - 1) x₁) θ))
          (𝓝[<] (π / r)) (𝓝 (P.eval 0)) :=
      fun P => ((Polynomial.continuous P).tendsto 0).comp hγ0
    have hdiv := (hp (derivative B)).norm.div (hp B).norm (norm_ne_zero_iff.2 hBev)
    have hval : KB - 1 = ‖(derivative B).eval 0‖ / ‖B.eval 0‖ := by rw [hKB]; ring
    rw [hval]
    exact hdiv
  have hev : ∀ᶠ θ in 𝓝[<] (π / r),
      ‖(derivative B).eval (ftPrincipal (ftTauArc a r (n - 1) x₁) θ)‖
        / ‖B.eval (ftPrincipal (ftTauArc a r (n - 1) x₁) θ)‖ ≤ KB :=
    (hΛt.eventually (eventually_lt_nhds (by linarith : KB - 1 < KB))).mono fun _ h => h.le
  obtain ⟨bB, hbB, hbBsub⟩ := mem_nhdsLT_iff_exists_Ioo_subset.1 hev
  set b₀ : ℝ := max bS (max bD (max bB (π / (2 * r)))) with hb₀
  have hhalf : π / (2 * r) < π / r := div_lt_div_of_pos_left pi_pos hrR (by linarith)
  have hb₀lt : b₀ < π / r := max_lt hbS (max_lt hbD (max_lt hbB hhalf))
  have hb₀0 : 0 < b₀ := lt_of_lt_of_le hbS0 (le_max_left _ _)
  set b₂ : ℝ := (b₀ + π / r) / 2 with hb₂
  have hb₂0 : 0 < b₂ := by rw [hb₂]; linarith
  have hb₂lt : b₂ < π / r := by rw [hb₂]; linarith
  have hb₀b₂ : b₀ < b₂ := by rw [hb₂]; linarith
  have hsub : ∀ s ∈ Ico b₂ (π / r), s ∈ Ioo b₀ (π / r) :=
    fun s hs => ⟨lt_of_lt_of_le hb₀b₂ hs.1, hs.2⟩
  have hsubS : Ioo b₀ (π / r) ⊆ Ioo bS (π / r) :=
    fun θ hθ => ⟨lt_of_le_of_lt (le_max_left _ _) hθ.1, hθ.2⟩
  have hsubD : Ioo b₀ (π / r) ⊆ Ioo bD (π / r) :=
    fun θ hθ => ⟨lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_right _ _)) hθ.1, hθ.2⟩
  have hsubB : Ioo b₀ (π / r) ⊆ Ioo bB (π / r) := fun θ hθ =>
    ⟨lt_of_le_of_lt (le_trans (le_max_left _ _)
      (le_trans (le_max_right _ _) (le_max_right _ _))) hθ.1, hθ.2⟩
  have hsubarc : Ioo b₀ (π / r) ⊆ Ioo (0 : ℝ) (π / r) :=
    fun θ hθ => ⟨lt_trans hb₀0 hθ.1, hθ.2⟩
  refine ⟨b₂, D * KB + CS, hb₂0, hb₂lt, fun s hs hW0 => ?_⟩
  have hs₀ : s ∈ Ioo b₀ (π / r) := hsub s hs
  have hnum : |((ftGammaDeriv a r (n - 1) s
      * (derivative B).eval (ftPrincipal (ftTauArc a r (n - 1) x₁) s))
      / B.eval (ftPrincipal (ftTauArc a r (n - 1) x₁) s)).im| ≤ D * KB := by
    refine le_trans (Complex.abs_im_le_norm _) ?_
    rw [norm_div, norm_mul, mul_div_assoc]
    have hD0 : 0 ≤ D := le_trans (norm_nonneg _) (hDbd s (hsubD hs₀))
    exact mul_le_mul (hDbd s (hsubD hs₀)) (hbBsub (hsubB hs₀)) (by positivity) hD0
  exact abs_im_logDeriv_ftAmpAlong_le (hS0 s (hsubarc hs₀)) hW0 hnum
    (hSbd s (hsubS hs₀))

/-- **`eq:phase-derivative-bound` on the interior region, across the whole divisor.**
`ArcPhaseLocal`'s estimate is that an amplitude zero contributes a real residue to `W'/W`
and so is invisible to the imaginary part; `ArcPhaseBound` turns the per-zero collars into
one constant over a compact sub-arc, and `InteriorSupply.ftAmplitudeDivisor` is what makes
the exceptional set a `Finset` — the branch meets each root of `B` at exactly one angle,
because the argument recovers the parameter.

The divisor is the zero set itself and not the set of candidates for it: the conclusion
*excludes* `S`, while the binder asks wherever the amplitude is nonzero, so a larger `S`
would leave the binder unreachable at the excess. -/
theorem ft_region_mid (B : Polynomial ℂ) (hB : B ≠ 0) (hn2 : 2 ≤ n) (ha : ∀ k, 0 < a k)
    (hc : c ≠ 0) (hr : 1 ≤ r) {b₁ b₂ : ℝ} (hsub : Icc b₁ b₂ ⊆ Ioo (0 : ℝ) (π / r)) :
    ∃ C₂ : ℝ, ∀ s ∈ Icc b₁ b₂,
      ftAmp (ftRootPoly c a) B r ((ftBranchZLower a c r (n - 1) s : ℝ) : ℂ)
          (ftPrincipal (ftTauArc a r (n - 1) x₁) s) ≠ 0 →
      |(ftArcAmpDeriv a B c r x₁ s / ftAmp (ftRootPoly c a) B r
        ((ftBranchZLower a c r (n - 1) s : ℝ) : ℂ)
        (ftPrincipal (ftTauArc a r (n - 1) x₁) s)).im| ≤ C₂ := by
  classical
  have hn : 0 < n := by omega
  have hnr : 2 ≤ n ∨ 2 ≤ r := Or.inl hn2
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have harc : (0 : ℝ) < π / r := by positivity
  have hbranch : ∀ θ ∈ Ioo (0 : ℝ) (π / r), FTBranchAt a r (n - 1) θ :=
    fun θ hθ => ftBranchAt_of_arc_principal hn ha hr hnr hθ
  obtain ⟨hγd, hd2, -, -⟩ := ft_geometry_group hn ha hr hnr hbranch x₁ 0
  rw [← ftTauArc_eq_ftTauArcAt] at hγd
  obtain ⟨-, -, hS0⟩ := ft_cofactor_group (x₁ := x₁) hn ha hc hr hnr
  have hstate := ft_branch_state_arc (x₁ := x₁) hn ha hc hr hnr
  obtain ⟨hWd, hWc⟩ := ft_amplitude_group (x₁ := x₁) B hn ha hc hr hnr
  set S : Finset ℝ := ftAmplitudeDivisor (ftRootPoly c a) B r
    (ftBranchZLower a c r (n - 1)) (ftTauArc a r (n - 1) x₁) b₁ b₂ with hS
  -- every parameter of the interval off the divisor has a nonvanishing amplitude
  have hτpos : ∀ θ ∈ Icc b₁ b₂, 0 < ftTauArc a r (n - 1) x₁ θ := by
    intro θ hθ
    rw [ftTauArc_agree a r (n - 1) x₁ (hsub hθ).1 (hsub hθ).2]
    exact ftTau_pos (hbranch θ (hsub hθ))
  have hsimple : ∀ θ ∈ Icc b₁ b₂,
      (derivative (ftDen (ftRootPoly c a) r
          ((ftBranchZLower a c r (n - 1) θ : ℝ) : ℂ))).eval
        (ftPrincipal (ftTauArc a r (n - 1) x₁) θ) ≠ 0 := by
    intro θ hθ
    rw [eval_derivative_ftDen ((hstate θ (hsub hθ)).2.1)]
    exact hS0 θ (hsub hθ)
  have hWne : ∀ θ ∈ Icc b₁ b₂, θ ∉ S →
      ftAmp (ftRootPoly c a) B r ((ftBranchZLower a c r (n - 1) θ : ℝ) : ℂ)
        (ftPrincipal (ftTauArc a r (n - 1) x₁) θ) ≠ 0 := by
    intro θ hθ hθS hzero
    exact hθS (ftAmplitudeDivisor_complete hB
      (fun s hs => ftArc_subset hr (hsub hs)) hτpos
      (fun s hs => (hstate s (hsub hs)).2.1) hsimple hθ hzero)
  -- continuity off the divisor
  have hsubdiff : Icc b₁ b₂ \ (↑S : Set ℝ) ⊆ Ioo (0 : ℝ) (π / r) := fun θ hθ => hsub hθ.1
  have hWcont : ContinuousOn (fun θ : ℝ => ftAmp (ftRootPoly c a) B r
      ((ftBranchZLower a c r (n - 1) θ : ℝ) : ℂ)
      (ftPrincipal (ftTauArc a r (n - 1) x₁) θ)) (Ioo (0 : ℝ) (π / r)) :=
    fun θ hθ => (hWd θ hθ).continuousAt.continuousWithinAt
  have hcont : ContinuousOn (fun θ : ℝ =>
      (deriv (fun t : ℝ => ftAmp (ftRootPoly c a) B r
          ((ftBranchZLower a c r (n - 1) t : ℝ) : ℂ)
          (ftPrincipal (ftTauArc a r (n - 1) x₁) t)) θ
        / ftAmp (ftRootPoly c a) B r ((ftBranchZLower a c r (n - 1) θ : ℝ) : ℂ)
            (ftPrincipal (ftTauArc a r (n - 1) x₁) θ)).im) (Icc b₁ b₂ \ (↑S : Set ℝ)) := by
    have hbase : ContinuousOn (fun θ : ℝ => (ftArcAmpDeriv a B c r x₁ θ
        / ftAmp (ftRootPoly c a) B r ((ftBranchZLower a c r (n - 1) θ : ℝ) : ℂ)
            (ftPrincipal (ftTauArc a r (n - 1) x₁) θ)).im)
        (Icc b₁ b₂ \ (↑S : Set ℝ)) :=
      Complex.continuous_im.comp_continuousOn
        (((hWc.mono hsubdiff)).div (hWcont.mono hsubdiff)
          (fun θ hθ => hWne θ hθ.1 hθ.2))
    exact hbase.congr fun θ hθ => by
      rw [ft_deriv_ftAmp_eq (x₁ := x₁) B hn ha hc hr hnr (hsubdiff hθ)]
  -- the per-zero data
  have hloc : ∀ z ∈ S, z ∈ Ioo (0 : ℝ) (π / r) ∧
      ftGammaDeriv a r (n - 1) z ≠ 0 ∧
      ftPrincipal (ftTauArc a r (n - 1) x₁) z ≠ 0 ∧
      (ftCritical (ftRootPoly c a) r).eval (ftPrincipal (ftTauArc a r (n - 1) x₁) z) ≠ 0 ∧
      (∀ᶠ θ in nhds z, (ftDen (ftRootPoly c a) r
        ((ftBranchZLower a c r (n - 1) θ : ℝ) : ℂ)).eval
          (ftPrincipal (ftTauArc a r (n - 1) x₁) θ) = 0) := by
    intro z hz
    have hzI : z ∈ Icc b₁ b₂ := ftAmplitudeDivisor_subset (Finset.mem_coe.2 hz)
    have hzV : z ∈ Ioo (0 : ℝ) (π / r) := hsub hzI
    refine ⟨hzV, ftGammaDeriv_ne_zero (hbranch z hzV), (hstate z hzV).1,
      (hstate z hzV).2.2, ?_⟩
    filter_upwards [isOpen_Ioo.mem_nhds hzV] with θ hθ
    exact (hstate θ hθ).2.1
  obtain ⟨κ, hκ0, hbd⟩ :=
    exists_bound_im_logDeriv_ftAmp_interiorRegion_of_deriv2 (Q := ftRootPoly c a) (B := B)
      (r := r) (γ := ftPrincipal (ftTauArc a r (n - 1) x₁))
      (dγ := ftGammaDeriv a r (n - 1)) (d2γ := ftGammaDeriv2 a r (n - 1))
      (zf := fun s : ℝ => ((ftBranchZLower a c r (n - 1) s : ℝ) : ℂ))
      (S := S) (V := Ioo (0 : ℝ) (π / r))
      hB hr isOpen_Ioo hγd hd2
      (fun θ hθ => continuousAt_ftGammaDeriv2 hn ha hr hθ hbranch) hcont hloc
  refine ⟨κ, fun s hs hW0 => ?_⟩
  have hsS : s ∉ S := fun hmem => hW0 (ftAmplitudeDivisor_zero hmem)
  rw [← ft_deriv_ftAmp_eq (x₁ := x₁) B hn ha hc hr hnr (hsub hs)]
  exact hbd s hs hsS

end ForgacsTran
