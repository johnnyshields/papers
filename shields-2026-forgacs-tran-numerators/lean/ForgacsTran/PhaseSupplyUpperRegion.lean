/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import ForgacsTran.FTBranchUpper
import ForgacsTran.PhaseSupplyKappaZero

/-!
# `κ₀`'s outer region at the origin endpoint

`PhaseSupplyKappaZero.ft_kappaZero_of_collars` asks for one bound per endpoint.  This
module produces the one at `π/r`, for `2 ≤ r`, where the branch runs into the **origin**
rather than into a collision.

**It is not a collar, and that is the point.**  At `2 ≤ r` the radius collapses
(`FTBranchUpper.tendsto_ftTau_nhdsLT_upper`) but `E = XQ' - rQ` does not degenerate there:
`E(0) = -rQ(0) ≠ 0`.  So `BranchSupply.abs_im_logDeriv_ftCofactorAlong_le_of_bounds`
applies — the ordinary bound, which pays exactly `+1` for the `1/γ` of `∂_tD = E(γ)/γ` and
so survives `‖γ‖ → 0`, where any estimate through the modulus would not.

Its two inputs both come from the collapse.  `‖E'(γ)‖/‖E(γ)‖` is bounded because `E(γ)`
converges to a nonzero value, and `‖γ'‖` is bounded by
`BranchSupplyGeometry.norm_ftGammaDeriv_le`, whose two hypotheses — the branch point well
inside the smallest zero, and the arc off the real axis — are respectively the collapse
itself and positivity of `\sin` on a compact sub-arc.

**The cut point is chosen here and returned**, since both inputs hold only near the
endpoint and the width at which they do is not something a caller could know.

Sorry-free.

## Main statements

* `ft_upper_gammaDeriv_bound` — `‖γ'‖` bounded near the endpoint.
* `ft_upper_region` — the bound on `Ioo b₂ (π/r)`, with nothing assumed.

## References

Formalizes `../../shields-2026-forgacs-tran-numerators.tex`, `sec:geometry`,
`eq:Dprime-identity`, `cor:linear-phase-variation`.

## Tags

upper endpoint, origin, viewing arc, bounded variation, Forgács–Tran
-/

namespace ForgacsTran

open Polynomial Set Real Filter Topology

variable {n r : ℕ} {a : Fin n → ℝ} {c x₁ : ℝ}

/-- **The branch point collapses to the origin at `π/r`, for `2 ≤ r`**, in the arc's own
radius.  `ftTauArc` agrees with `ftTau` below `π/r`, and that is where the filter lives. -/
theorem ft_tendsto_ftPrincipal_upper (hn2 : 2 ≤ n) (ha : ∀ k, 0 < a k) (hr : 2 ≤ r) :
    Tendsto (ftPrincipal (ftTauArc a r (n - 1) x₁)) (𝓝[<] (π / r)) (𝓝 0) := by
  have hrR : (0 : ℝ) < r := by positivity
  have harc : (0 : ℝ) < π / r := by positivity
  have hτ0 : Tendsto (ftTau a r (n - 1)) (𝓝[<] (π / r)) (𝓝 0) :=
    tendsto_ftTau_nhdsLT_upper hn2 ha hr
  have hτarc : Tendsto (ftTauArc a r (n - 1) x₁) (𝓝[<] (π / r)) (𝓝 0) := by
    refine hτ0.congr' ?_
    filter_upwards [Ioo_mem_nhdsLT harc] with θ hθ
    exact (ftTauArc_agree a r (n - 1) x₁ hθ.1 hθ.2).symm
  have h1 : Tendsto (fun θ : ℝ => ((ftTauArc a r (n - 1) x₁ θ : ℝ) : ℂ))
      (𝓝[<] (π / r)) (𝓝 0) := by
    simpa [Function.comp_def] using (Complex.continuous_ofReal.tendsto (0 : ℝ)).comp hτarc
  have h2 : Tendsto (fun θ : ℝ => Complex.exp ((θ : ℂ) * Complex.I)) (𝓝[<] (π / r))
      (𝓝 (Complex.exp (((π / r : ℝ) : ℂ) * Complex.I))) := by
    have : Continuous fun θ : ℝ => Complex.exp ((θ : ℂ) * Complex.I) := by fun_prop
    exact (this.tendsto _).mono_left nhdsWithin_le_nhds
  have hmul : Tendsto (fun θ : ℝ => ((ftTauArc a r (n - 1) x₁ θ : ℝ) : ℂ)
      * Complex.exp ((θ : ℂ) * Complex.I)) (𝓝[<] (π / r)) (𝓝 0) := by
    simpa using h1.mul h2
  exact hmul

/-- **`γ'` is bounded near the origin endpoint.**  `norm_ftGammaDeriv_le` asks the branch
point to sit well inside the smallest zero and the arc to sit off the real axis; the
collapse of the radius supplies the first and positivity of `\sin` on a compact sub-arc
the second.

Returned with its own cut point, since neither holds on the whole arc. -/
theorem ft_upper_gammaDeriv_bound (hn2 : 2 ≤ n) (ha : ∀ k, 0 < a k) (hr : 2 ≤ r) :
    ∃ b D : ℝ, 0 < b ∧ b < π / r ∧
      ∀ θ ∈ Ioo b (π / r), ‖ftGammaDeriv a r (n - 1) θ‖ ≤ D := by
  classical
  have hn : 0 < n := by omega
  have hr1 : 1 ≤ r := by omega
  have hnr : 2 ≤ n ∨ 2 ≤ r := Or.inl hn2
  have hrR : (0 : ℝ) < r := by positivity
  have harc : (0 : ℝ) < π / r := by positivity
  have hbranch : ∀ θ ∈ Ioo (0 : ℝ) (π / r), FTBranchAt a r (n - 1) θ :=
    fun θ hθ => ftBranchAt_of_arc_principal hn ha hr1 hnr hθ
  have hne : (Finset.univ : Finset (Fin n)).Nonempty :=
    Finset.univ_nonempty_iff.2 (Fin.pos_iff_nonempty.1 hn)
  obtain ⟨m, -, hmle⟩ := Finset.exists_min_image Finset.univ a hne
  set T₀ : ℝ := a m / 2 with hT₀
  have hT₀0 : 0 < T₀ := by rw [hT₀]; have := ha m; linarith
  have hev : ∀ᶠ θ in 𝓝[<] (π / r), ftTau a r (n - 1) θ ≤ T₀ :=
    ((tendsto_ftTau_nhdsLT_upper hn2 ha hr).eventually
      (eventually_lt_nhds hT₀0)).mono fun _ h => h.le
  obtain ⟨b₀, hb₀, hb₀sub⟩ := mem_nhdsLT_iff_exists_Ioo_subset.1 hev
  have hhalf : π / (2 * r) < π / r := div_lt_div_of_pos_left pi_pos hrR (by linarith)
  set b : ℝ := max b₀ (π / (2 * r)) with hb
  have hb0 : 0 < b := lt_of_lt_of_le (by positivity) (le_max_right _ _)
  have hblt : b < π / r := max_lt hb₀ hhalf
  have hbsub : Ioo b (π / r) ⊆ Ioo b₀ (π / r) :=
    fun θ hθ => ⟨lt_of_le_of_lt (le_max_left _ _) hθ.1, hθ.2⟩
  have hsubarc : Ioo b (π / r) ⊆ Ioo (0 : ℝ) (π / r) :=
    fun θ hθ => ⟨lt_trans hb0 hθ.1, hθ.2⟩
  have hsinpos : ∀ θ ∈ Icc b (π / r), 0 < Real.sin θ := by
    intro θ hθ
    have h1 : 0 < θ := lt_of_lt_of_le hb0 hθ.1
    have hhalfpi : π / r ≤ π / 2 := by
      have h2r : (2 : ℝ) ≤ r := by exact_mod_cast hr
      exact div_le_div_of_nonneg_left pi_pos.le (by norm_num) h2r
    have h2 : θ < π := lt_of_le_of_lt (le_trans hθ.2 hhalfpi) (by linarith [pi_pos])
    exact Real.sin_pos_of_pos_of_lt_pi h1 h2
  obtain ⟨s₀, hs₀, hs₀min⟩ := (isCompact_Icc (a := b) (b := π / r)).exists_isMinOn
    ⟨b, ⟨le_rfl, hblt.le⟩⟩ Real.continuous_sin.continuousOn
  set c₀ : ℝ := Real.sin s₀ with hc₀
  have hc₀0 : 0 < c₀ := hsinpos s₀ hs₀
  set S8 : ℝ := ∑ k, 8 / a k with hS8
  set S1 : ℝ := ∑ k, 1 / a k with hS1
  have hS80 : 0 ≤ S8 := Finset.sum_nonneg fun k _ => by have := ha k; positivity
  have hS10 : 0 < S1 := Finset.sum_pos (fun k _ => by have := ha k; positivity) hne
  have hden : 0 < c₀ / 4 * S1 := by positivity
  refine ⟨b, (T₀ * S8 + r) / (c₀ / 4 * S1) + T₀, hb0, hblt, fun θ hθ => ?_⟩
  have hθarc := hsubarc hθ
  have hτpos : 0 < ftTau a r (n - 1) θ := ftTau_pos (hbranch θ hθarc)
  have hτle : ftTau a r (n - 1) θ ≤ T₀ := hb₀sub (hbsub hθ)
  have hsmall : ∀ k, 2 * ftTau a r (n - 1) θ ≤ a k := by
    intro k
    have := hmle k (Finset.mem_univ k)
    rw [hT₀] at hτle
    linarith
  have hcs : c₀ ≤ Real.sin θ := hs₀min ⟨hθ.1.le, hθ.2.le⟩
  refine le_trans (norm_ftGammaDeriv_le hn ha hτpos (ftArc_subset hr1 hθarc)
    hsmall hc₀0 hcs) ?_
  rw [← hS8, ← hS1]
  gcongr

/-- **The outer region at the origin endpoint, with nothing assumed.**  The cut point and
the constant are produced together, since neither input to
`abs_im_logDeriv_ftCofactorAlong_le_of_bounds` holds on the whole arc. -/
theorem ft_upper_region (hn2 : 2 ≤ n) (ha : ∀ k, 0 < a k) (hc : c ≠ 0) (hr : 2 ≤ r) :
    ∃ b₂ C₃ : ℝ, 0 < b₂ ∧ b₂ < π / r ∧ ∀ θ ∈ Ioo b₂ (π / r),
      |(ftArcCofactorDeriv a c r x₁ θ
        / ftCofactorAlong (ftRootPoly c a) r (ftBranchZLower a c r (n - 1))
            (ftTauArc a r (n - 1) x₁) θ).im| ≤ C₃ := by
  classical
  have hn : 0 < n := by omega
  have hr1 : 1 ≤ r := by omega
  have hnr : 2 ≤ n ∨ 2 ≤ r := Or.inl hn2
  have hrR : (0 : ℝ) < r := by positivity
  have harc : (0 : ℝ) < π / r := by positivity
  have hbranch : ∀ θ ∈ Ioo (0 : ℝ) (π / r), FTBranchAt a r (n - 1) θ :=
    fun θ hθ => ftBranchAt_of_arc_principal hn ha hr1 hnr hθ
  obtain ⟨hγd, -, -, -⟩ := ft_geometry_group hn ha hr1 hnr hbranch x₁ 0
  rw [← ftTauArc_eq_ftTauArcAt] at hγd
  obtain ⟨hSd, hSc, hS0⟩ := ft_cofactor_group (x₁ := x₁) hn ha hc hr1 hnr
  have hstate := ft_branch_state_arc (x₁ := x₁) hn ha hc hr1 hnr
  obtain ⟨bD, D, hbD0, hbD, hDbd⟩ := ft_upper_gammaDeriv_bound hn2 ha hr
  -- `E` does not degenerate at the origin
  have hQ0 : (ftRootPoly c a).eval 0 ≠ 0 := by
    rw [← Polynomial.coeff_zero_eq_eval_zero]
    exact ftRootPoly_coeff_zero_ne_zero hc ha
  have hE0 : (ftCritical (ftRootPoly c a) r).eval 0 ≠ 0 :=
    eval_ftCritical_zero_ne_zero hr1 hQ0
  set K : ℝ := ‖(derivative (ftCritical (ftRootPoly c a) r)).eval 0‖
    / ‖(ftCritical (ftRootPoly c a) r).eval 0‖ + 1 with hK
  set Ψ : ℝ → ℝ := fun θ =>
    ‖(derivative (ftCritical (ftRootPoly c a) r)).eval
        (ftPrincipal (ftTauArc a r (n - 1) x₁) θ)‖
      / ‖ftCriticalAlong (ftRootPoly c a) r (ftTauArc a r (n - 1) x₁) θ‖ with hΨ
  have hγ0 := ft_tendsto_ftPrincipal_upper (x₁ := x₁) hn2 ha hr
  have hΨt : Tendsto Ψ (𝓝[<] (π / r)) (𝓝 (K - 1)) := by
    have hp : ∀ P : Polynomial ℂ,
        Tendsto (fun θ : ℝ => P.eval (ftPrincipal (ftTauArc a r (n - 1) x₁) θ))
          (𝓝[<] (π / r)) (𝓝 (P.eval 0)) :=
      fun P => ((Polynomial.continuous P).tendsto 0).comp hγ0
    have hdiv := (hp (derivative (ftCritical (ftRootPoly c a) r))).norm.div
      (hp (ftCritical (ftRootPoly c a) r)).norm (norm_ne_zero_iff.2 hE0)
    have hval : K - 1 = ‖(derivative (ftCritical (ftRootPoly c a) r)).eval 0‖
        / ‖(ftCritical (ftRootPoly c a) r).eval 0‖ := by rw [hK]; ring
    rw [hval]
    exact hdiv
  have hev : ∀ᶠ θ in 𝓝[<] (π / r), Ψ θ ≤ K :=
    (hΨt.eventually (eventually_lt_nhds (by linarith : K - 1 < K))).mono fun _ h => h.le
  obtain ⟨bK, hbK, hbKsub⟩ := mem_nhdsLT_iff_exists_Ioo_subset.1 hev
  set b₂ : ℝ := max bD (max bK (π / (2 * r))) with hb₂
  have hhalf : π / (2 * r) < π / r := div_lt_div_of_pos_left pi_pos hrR (by linarith)
  have hb₂0 : 0 < b₂ :=
    lt_of_lt_of_le (by positivity) (le_trans (le_max_right _ _) (le_max_right _ _))
  have hb₂lt : b₂ < π / r := max_lt hbD (max_lt hbK hhalf)
  have hsubD : Ioo b₂ (π / r) ⊆ Ioo bD (π / r) :=
    fun θ hθ => ⟨lt_of_le_of_lt (le_max_left _ _) hθ.1, hθ.2⟩
  have hsubK : Ioo b₂ (π / r) ⊆ Ioo bK (π / r) :=
    fun θ hθ => ⟨lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_right _ _)) hθ.1, hθ.2⟩
  have hsubarc : Ioo b₂ (π / r) ⊆ Ioo (0 : ℝ) (π / r) :=
    fun θ hθ => ⟨lt_trans hb₂0 hθ.1, hθ.2⟩
  have hτd : ∀ θ ∈ Ioo b₂ (π / r),
      HasDerivAt (ftTauArc a r (n - 1) x₁) (ftTauDeriv a r (n - 1) θ) θ := by
    intro θ hθ
    refine (hasDerivAt_ftTau hn ha hr1 (hsubarc hθ) hbranch).congr_of_eventuallyEq ?_
    filter_upwards [isOpen_Ioo.mem_nhds (hsubarc hθ)] with s hs
    exact ftTauArc_agree a r (n - 1) x₁ hs.1 hs.2
  exact ⟨b₂, D * K + 1, hb₂0, hb₂lt,
    abs_im_logDeriv_ftCofactorAlong_le_of_bounds hr1
      (fun θ hθ => hstate θ (hsubarc hθ)) hτd
      (fun θ hθ => hγd θ (hsubarc hθ))
      (fun θ hθ => hSd θ (hsubarc hθ))
      (fun θ hθ => hDbd θ (hsubD hθ)) (fun θ hθ => hbKsub (hsubK hθ))⟩

end ForgacsTran
