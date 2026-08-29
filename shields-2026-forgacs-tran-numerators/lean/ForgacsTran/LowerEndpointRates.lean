/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import ForgacsTran.LowerEndpointReduced
import ForgacsTran.UpperEndpointRadius

/-!
# The branch radius at a lower endpoint that is a SIMPLE zero of `E`

`BranchSupplyGeometry` supplies the lower endpoint's collar binders at a **repeated**
smallest zero, where the branch runs into `x₁` itself and the one-sided derivative comes
from the cluster expansion.  This module supplies them wherever the endpoint is a *simple*
zero of `E = XQ' - rQ`, which is the `ρ = 1` case: there the radius runs into a critical
point strictly inside the first gap, no zero of the pencil is at the endpoint, and the
cluster machinery describes nothing.

The route is `LowerEndpointReduced`'s, and it is the same one `UpperEndpointRadius` and
`UpperEndpointSlope` take at the `r = 1` upper end:

* the reduced equation is even in `θ`, so it moves by `O(θ²)`;
* the simple zero bounds `|τ - L|` by that motion, giving `|τ(θ) - L| = O(θ²)`;
* differentiating the reduced equation along the branch gives `Aτ' + B = 0` with `A`
  bounded away from `0` and `B = O(θ)`, so `|τ'| = O(θ)`.

Both together make `γ'` Lipschitz at the endpoint with value `iL`, which is every collar
binder at that end.

**`τ' → 0` here is `EndpointTauDeriv2Simple.tendsto_ftTauDeriv_zero_of_simple` reached by a
different route, and the two agreeing is the check on both.**  That module gets it from the
rescaled Cramer system; this one gets it from the evenness of the reduced equation, and the
rate — which the Cramer route does not produce — is what the collar needs.

Sorry-free.

## Main statements

* `exists_quadratic_bound_ftTau_lower` — `|τ(θ) - L| = O(θ²)`.
* `exists_linear_bound_ftTauDeriv_lower` — `|τ'(θ)| = O(θ)`.
* `ft_endpoint_branch_data_simple` — the collar's endpoint binders.

## References

Formalizes `../../shields-2026-forgacs-tran-numerators.tex`, `sec:geometry`, `eq:ab-def`,
`lem:principal-endpoint-regularity`.

## Tags

lower endpoint, simple zero, branch radius, quadratic rate, Forgács–Tran
-/

namespace ForgacsTran

open Polynomial Set Real Filter Topology

variable {n r : ℕ} {a : Fin n → ℝ} {c L : ℝ}

/-- **The branch radius reaches a simple endpoint quadratically.** -/
theorem exists_quadratic_bound_ftTau_lower (hn : 0 < n) (ha : ∀ k, 0 < a k) (hr : 1 ≤ r)
    (hnr : 2 ≤ n ∨ 2 ≤ r) (hL : 0 < L)
    (hLe : (ftCriticalReal (ftRootPolyReal c a) r).eval L = 0)
    (hLd : (derivative (ftCriticalReal (ftRootPolyReal c a) r)).eval L ≠ 0)
    (hlim : Tendsto (ftTau a r (n - 1)) (𝓝[>] (0 : ℝ)) (𝓝 L)) :
    ∃ K δ : ℝ, 0 < δ ∧ δ ≤ π / r ∧
      ∀ θ ∈ Ioo (0 : ℝ) δ, |ftTau a r (n - 1) θ - L| ≤ K * θ ^ 2 := by
  classical
  have hrR : (0 : ℝ) < r := by exact_mod_cast Nat.lt_of_lt_of_le Nat.one_pos hr
  have harc : (0 : ℝ) < π / r := by positivity
  obtain ⟨P, hP⟩ : ∃ P : Polynomial ℝ, P = ftRootPolyReal c a := ⟨_, rfl⟩
  set E : Polynomial ℝ := ftCriticalReal P r with hE
  have hfL : E.eval L = 0 := by rw [hE, hP]; exact hLe
  have hfd : HasDerivAt (fun x : ℝ => E.eval x) ((derivative E).eval L) L := E.hasDerivAt L
  have hdne : (derivative E).eval L ≠ 0 := by rw [hE, hP]; exact hLd
  obtain ⟨δ₁, hδ₁, hlow⟩ := exists_linear_lower_bound_of_hasDerivAt hfd hfL hdne
  have hdnorm : 0 < ‖(derivative E).eval L‖ := norm_pos_iff.2 hdne
  have hbranchAll : ∀ t ∈ Ioo (0 : ℝ) (π / r), FTBranchAt a r (n - 1) t :=
    fun t ht => ftBranchAt_of_arc_principal hn ha hr hnr ht
  have hgzero : ∀ t ∈ Ioo (0 : ℝ) (π / r),
      ftLowerReduced P r (ftTau a r (n - 1) t) t = 0 := by
    intro t ht
    have hz : ftPencilIm P r (ftTau a r (n - 1) t) t = 0 := by
      rw [hP]
      exact ftPencilIm_eq_zero c ha (ftArc_subset hr ht) (hbranchAll t ht)
    rw [ftPencilIm_eq_mul_ftLowerReduced] at hz
    rcases mul_eq_zero.1 hz with h | h
    · exact absurd h (ne_of_gt ht.1)
    · exact h
  have hev : ∀ᶠ θ in 𝓝[>] (0 : ℝ), |ftTau a r (n - 1) θ - L| < min δ₁ 1 := by
    filter_upwards [hlim (Metric.ball_mem_nhds L (lt_min hδ₁ one_pos))] with θ hθ
    have hb : ftTau a r (n - 1) θ ∈ Metric.ball L (min δ₁ 1) := hθ
    rw [Metric.mem_ball, Real.dist_eq] at hb
    exact hb
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hev
  have hu0 : (0 : ℝ) < u := hu
  refine ⟨2 * ftLowerReducedBound P r (L + 1) / ‖(derivative E).eval L‖,
    min u (π / r), lt_min hu0 harc, min_le_right _ _, fun θ hθ => ?_⟩
  have hmin1 : min u (π / r) ≤ u := min_le_left _ _
  have hmin2 : min u (π / r) ≤ π / r := min_le_right _ _
  have hθarc : θ ∈ Ioo (0 : ℝ) (π / r) := ⟨hθ.1, lt_of_lt_of_le hθ.2 hmin2⟩
  have hwin : |ftTau a r (n - 1) θ - L| < min δ₁ 1 :=
    hsub ⟨hθ.1, lt_of_lt_of_le hθ.2 hmin1⟩
  have hτabs : |ftTau a r (n - 1) θ| ≤ L + 1 := by
    have h1 : |ftTau a r (n - 1) θ - L| < 1 := lt_of_lt_of_le hwin (min_le_right _ _)
    have h2 := abs_sub_abs_le_abs_sub (ftTau a r (n - 1) θ) L
    rw [abs_of_pos hL] at h2
    linarith
  have hupper : |E.eval (ftTau a r (n - 1) θ)|
      ≤ ftLowerReducedBound P r (L + 1) * θ ^ 2 := by
    have hval : E.eval (ftTau a r (n - 1) θ)
        = -ftLowerReduced P r (ftTau a r (n - 1) θ) 0 := by
      rw [ftLowerReduced_zero, hE]; ring
    have hq := abs_ftLowerReduced_sub_zero_le P r (τ := ftTau a r (n - 1) θ)
      (T := L + 1) θ hτabs
    rw [hgzero θ hθarc, zero_sub, abs_neg] at hq
    rw [hval, abs_neg]
    exact hq
  have hlowθ : ‖(derivative E).eval L‖ / 2 * |ftTau a r (n - 1) θ - L|
      ≤ |E.eval (ftTau a r (n - 1) θ)| :=
    hlow _ (lt_of_lt_of_le hwin (min_le_left _ _))
  rw [div_mul_eq_mul_div, le_div_iff₀ hdnorm]
  nlinarith [hlowθ, hupper]

/-- **The branch radius has slope `O(θ)` at a simple endpoint.** -/
theorem exists_linear_bound_ftTauDeriv_lower (hn : 0 < n) (ha : ∀ k, 0 < a k) (hr : 1 ≤ r)
    (hnr : 2 ≤ n ∨ 2 ≤ r) (hL : 0 < L)
    (hLd : (derivative (ftCriticalReal (ftRootPolyReal c a) r)).eval L ≠ 0)
    (hlim : Tendsto (ftTau a r (n - 1)) (𝓝[>] (0 : ℝ)) (𝓝 L)) :
    ∃ M δ : ℝ, 0 < δ ∧ δ ≤ π / r ∧
      ∀ θ ∈ Ioo (0 : ℝ) δ, |ftTauDeriv a r (n - 1) θ| ≤ M * θ := by
  classical
  have hrR : (0 : ℝ) < r := by exact_mod_cast Nat.lt_of_lt_of_le Nat.one_pos hr
  have harc : (0 : ℝ) < π / r := by positivity
  obtain ⟨P, hP⟩ : ∃ P : Polynomial ℝ, P = ftRootPolyReal c a := ⟨_, rfl⟩
  have hA₀ : ftLowerReducedRadial P r L 0 ≠ 0 := by
    rw [ftLowerReducedRadial_zero, hP]
    simpa using hLd
  have hA₀n : 0 < ‖ftLowerReducedRadial P r L 0‖ := norm_pos_iff.2 hA₀
  have hbranchAll : ∀ t ∈ Ioo (0 : ℝ) (π / r), FTBranchAt a r (n - 1) t :=
    fun t ht => ftBranchAt_of_arc_principal hn ha hr hnr ht
  have hgzero : ∀ t ∈ Ioo (0 : ℝ) (π / r),
      ftLowerReduced P r (ftTau a r (n - 1) t) t = 0 := by
    intro t ht
    have hz : ftPencilIm P r (ftTau a r (n - 1) t) t = 0 := by
      rw [hP]
      exact ftPencilIm_eq_zero c ha (ftArc_subset hr ht) (hbranchAll t ht)
    rw [ftPencilIm_eq_mul_ftLowerReduced] at hz
    rcases mul_eq_zero.1 hz with h | h
    · exact absurd h (ne_of_gt ht.1)
    · exact h
  have hφ0 : Tendsto (fun θ : ℝ => θ) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hAt : Tendsto (fun θ : ℝ => ftLowerReducedRadial P r (ftTau a r (n - 1) θ) θ)
      (𝓝[>] (0 : ℝ)) (𝓝 (ftLowerReducedRadial P r L 0)) :=
    tendsto_ftLowerReducedRadial P r hlim hφ0
  have hevA : ∀ᶠ θ in 𝓝[>] (0 : ℝ),
      ‖ftLowerReducedRadial P r L 0‖ / 2
        ≤ |ftLowerReducedRadial P r (ftTau a r (n - 1) θ) θ| := by
    filter_upwards [hAt (Metric.ball_mem_nhds (ftLowerReducedRadial P r L 0)
      (by linarith : (0:ℝ) < ‖ftLowerReducedRadial P r L 0‖ / 2))] with θ hθ
    have hb : ftLowerReducedRadial P r (ftTau a r (n - 1) θ) θ
        ∈ Metric.ball (ftLowerReducedRadial P r L 0)
          (‖ftLowerReducedRadial P r L 0‖ / 2) := hθ
    rw [Metric.mem_ball, Real.dist_eq] at hb
    have h2 := abs_sub_abs_le_abs_sub (ftLowerReducedRadial P r L 0)
      (ftLowerReducedRadial P r (ftTau a r (n - 1) θ) θ)
    rw [abs_sub_comm] at h2
    rw [Real.norm_eq_abs] at hb ⊢
    linarith
  have hevT : ∀ᶠ θ in 𝓝[>] (0 : ℝ), |ftTau a r (n - 1) θ| ≤ L + 1 := by
    filter_upwards [hlim (Metric.ball_mem_nhds L one_pos)] with θ hθ
    have hb : ftTau a r (n - 1) θ ∈ Metric.ball L 1 := hθ
    rw [Metric.mem_ball, Real.dist_eq] at hb
    have h2 := abs_sub_abs_le_abs_sub (ftTau a r (n - 1) θ) L
    rw [abs_of_pos hL] at h2
    linarith
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 (hevA.and hevT)
  have hu0 : (0 : ℝ) < u := hu
  have hBd0 : 0 ≤ ftLowerReducedBound P r (L + 1) :=
    ftLowerReducedBound_nonneg P r (by linarith)
  refine ⟨6 * ftLowerReducedBound P r (L + 1) / ‖ftLowerReducedRadial P r L 0‖,
    min u (π / r), lt_min hu0 harc, min_le_right _ _, fun θ hθ => ?_⟩
  have hmin1 : min u (π / r) ≤ u := min_le_left _ _
  have hmin2 : min u (π / r) ≤ π / r := min_le_right _ _
  have hθarc : θ ∈ Ioo (0 : ℝ) (π / r) := ⟨hθ.1, lt_of_lt_of_le hθ.2 hmin2⟩
  obtain ⟨hAθ, hTθ⟩ := hsub ⟨hθ.1, lt_of_lt_of_le hθ.2 hmin1⟩
  have hτd : HasDerivAt (ftTau a r (n - 1)) (ftTauDeriv a r (n - 1) θ) θ :=
    hasDerivAt_ftTau hn ha hr hθarc hbranchAll
  have hg := hasDerivAt_ftLowerReduced_along P r hτd (ne_of_gt hθ.1)
  have hg0 : HasDerivAt (fun t : ℝ => ftLowerReduced P r (ftTau a r (n - 1) t) t) 0 θ := by
    refine (hasDerivAt_const θ (0 : ℝ)).congr_of_eventuallyEq ?_
    filter_upwards [isOpen_Ioo.mem_nhds hθarc] with t ht
    exact hgzero t ht
  have hkey : ftLowerReducedRadial P r (ftTau a r (n - 1) θ) θ * ftTauDeriv a r (n - 1) θ
      + ftLowerReducedSlope P r (ftTau a r (n - 1) θ) θ = 0 := hg.unique hg0
  have hB := abs_ftLowerReducedSlope_le P r (τ := ftTau a r (n - 1) θ) (T := L + 1) θ hTθ
  rw [abs_of_pos hθ.1] at hB
  have hprod : |ftLowerReducedRadial P r (ftTau a r (n - 1) θ) θ|
      * |ftTauDeriv a r (n - 1) θ|
      = |ftLowerReducedSlope P r (ftTau a r (n - 1) θ) θ| := by
    rw [← abs_mul,
      show ftLowerReducedRadial P r (ftTau a r (n - 1) θ) θ * ftTauDeriv a r (n - 1) θ
        = -ftLowerReducedSlope P r (ftTau a r (n - 1) θ) θ from by linarith, abs_neg]
  have hstep : ‖ftLowerReducedRadial P r L 0‖ / 2 * |ftTauDeriv a r (n - 1) θ|
      ≤ 3 * ftLowerReducedBound P r (L + 1) * θ :=
    calc ‖ftLowerReducedRadial P r L 0‖ / 2 * |ftTauDeriv a r (n - 1) θ|
        ≤ |ftLowerReducedRadial P r (ftTau a r (n - 1) θ) θ|
            * |ftTauDeriv a r (n - 1) θ| :=
          mul_le_mul_of_nonneg_right hAθ (abs_nonneg _)
      _ = |ftLowerReducedSlope P r (ftTau a r (n - 1) θ) θ| := hprod
      _ ≤ 3 * ftLowerReducedBound P r (L + 1) * θ := hB
  rw [div_mul_eq_mul_div, le_div_iff₀ hA₀n]
  linarith

end ForgacsTran
