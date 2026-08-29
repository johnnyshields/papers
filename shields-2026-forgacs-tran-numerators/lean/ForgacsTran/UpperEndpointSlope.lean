/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import ForgacsTran.UpperEndpointRadius

/-!
# The branch radius has slope `O(π - θ)` at the `r = 1` upper endpoint

`UpperEndpointRadius` gets `|τ(θ) - L| = O((π - θ)^2)` from the reduced equation's evenness,
which is enough for the endpoint's one-sided derivative and not enough for the collar's
Lipschitz binder — that asks for `‖γ'(θ) - γ'(π)‖ = O(π - θ)`, and a quadratic bound on a
function says nothing about its derivative.

The same reduced equation supplies it.  `ftUpperReduced P (τ(θ)) (θ - π) = 0` on the collar,
so differentiating along the branch gives `A(θ)τ'(θ) + B(θ) = 0` with

* `A` the radial partial, continuous, and `A(L, 0) = -E'(-L) ≠ 0` because the collision is
  a simple zero;
* `B` the `φ`-partial, a sum of `sinc` derivatives, and `|\operatorname{sinc}'(x)| ≤ |x|/2`
  because `\sin` and `\cos` are within a cubic and a quadratic of their linearizations.

So `|τ'| = |B|/|A| = O(π - θ)`.  Nothing here is a two-variable derivative: the sum is
finite and each term is differentiated along the branch by the ordinary product rule, so
the whole argument is one-variable calculus over an explicit `Finset.sum`.

Sorry-free.

## Main statements

* `hasDerivAt_sinc`, `abs_sincDeriv_le` — the cardinal sine's derivative and its bound.
* `hasDerivAt_ftUpperReduced_along` — the reduced equation differentiated along the branch.
* `exists_linear_bound_ftTauDeriv_upper` — the slope bound.

## References

Formalizes `../../shields-2026-forgacs-tran-numerators.tex`, `sec:geometry`, `eq:ab-def`,
`lem:principal-endpoint-regularity`.

## Tags

upper endpoint, branch radius, slope, sinc, Forgács–Tran
-/

namespace ForgacsTran

open Polynomial Set Real Filter Topology

/-! ### The cardinal sine's derivative -/

/-- `\operatorname{sinc}'` away from the origin.  At `0` the quotient convention returns `0`,
which is also the true value, so no case split is needed downstream. -/
noncomputable def sincDeriv (x : ℝ) : ℝ := (x * Real.cos x - Real.sin x) / x ^ 2

theorem hasDerivAt_sinc {x : ℝ} (hx : x ≠ 0) : HasDerivAt Real.sinc (sincDeriv x) x := by
  have hdiv : HasDerivAt (fun t : ℝ => Real.sin t / t)
      ((Real.cos x * x - Real.sin x * 1) / x ^ 2) x :=
    (Real.hasDerivAt_sin x).div (hasDerivAt_id x) hx
  have heq : Real.sinc =ᶠ[nhds x] fun t : ℝ => Real.sin t / t := by
    filter_upwards [isOpen_ne.mem_nhds hx] with t ht
    exact Real.sinc_of_ne_zero ht
  have h := hdiv.congr_of_eventuallyEq heq
  refine h.congr_deriv ?_
  rw [sincDeriv]
  ring

/-- **`|\operatorname{sinc}'(x)| ≤ |x|/2`.**  `\cos` is between `1 - x^2/2` and `1` and
`\sin` between `x - x^3/6` and `x`, so `x\cos x - \sin x` is within `|x|^3/2` of `0`. -/
theorem abs_sincDeriv_le (x : ℝ) : |sincDeriv x| ≤ |x| / 2 := by
  have hcube : |x * Real.cos x - Real.sin x| ≤ |x| ^ 3 / 2 := by
    rcases lt_trichotomy x 0 with hx | rfl | hx
    · have hx' : 0 < -x := by linarith
      have hc1 : Real.cos (-x) ≤ 1 := Real.cos_le_one _
      have hc2 : 1 - (-x) ^ 2 / 2 ≤ Real.cos (-x) := Real.one_sub_sq_div_two_le_cos
      have hs1 := Real.sin_lt hx'
      have hs2 := Real.sin_gt_sub_cube hx'
      rw [Real.cos_neg] at hc1 hc2
      rw [Real.sin_neg] at hs1 hs2
      rw [abs_of_neg hx, abs_le]
      constructor <;> nlinarith
    · simp
    · have hc1 : Real.cos x ≤ 1 := Real.cos_le_one _
      have hc2 : 1 - x ^ 2 / 2 ≤ Real.cos x := Real.one_sub_sq_div_two_le_cos
      have hs1 := Real.sin_lt hx
      have hs2 := Real.sin_gt_sub_cube hx
      rw [abs_of_pos hx, abs_le]
      constructor <;> nlinarith
  rcases eq_or_ne x 0 with rfl | hx
  · simp [sincDeriv]
  · rw [sincDeriv, abs_div, abs_pow, div_le_div_iff₀ (by positivity) (by norm_num : (0:ℝ) < 2)]
    have h3 : |x| ^ 3 = |x| ^ 2 * |x| := by ring
    nlinarith [abs_nonneg x, hcube, sq_nonneg |x|]

/-- The chart a collar is read in: `t ↦ \operatorname{sinc}(m(t - p))`, at either endpoint. -/
theorem hasDerivAt_sinc_mul_sub (m p : ℝ) {θ : ℝ} (hθ : θ ≠ p) :
    HasDerivAt (fun t : ℝ => Real.sinc (m * (t - p))) (m * sincDeriv (m * (θ - p))) θ := by
  rcases eq_or_ne m 0 with rfl | hm
  · simpa using hasDerivAt_const θ (1 : ℝ)
  · have hne : m * (θ - p) ≠ 0 := mul_ne_zero hm (sub_ne_zero.2 hθ)
    have hin : HasDerivAt (fun t : ℝ => m * (t - p)) (m * 1) θ :=
      HasDerivAt.const_mul m ((hasDerivAt_id θ).sub_const p)
    have h := (hasDerivAt_sinc hne).comp θ hin
    refine h.congr_deriv ?_
    ring

/-! ### The reduced equation's two partials -/

/-- The radial partial of `ftUpperReduced`. -/
noncomputable def ftUpperReducedRadial (P : Polynomial ℝ) (τ φ : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (P.natDegree + 1),
    P.coeff j * (-1) ^ (j + 1) * ((j : ℝ) * τ ^ (j - 1))
      * ((1 - (j : ℝ)) * Real.sinc ((1 - (j : ℝ)) * φ))

/-- The angular partial of `ftUpperReduced`. -/
noncomputable def ftUpperReducedSlope (P : Polynomial ℝ) (τ φ : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (P.natDegree + 1),
    P.coeff j * (-1) ^ (j + 1) * τ ^ j
      * ((1 - (j : ℝ)) * ((1 - (j : ℝ)) * sincDeriv ((1 - (j : ℝ)) * φ)))

/-- **The reduced equation differentiated along the branch.**  The sum is finite and each
term is a product, so this is the ordinary product rule and no two-variable derivative is
involved. -/
theorem hasDerivAt_ftUpperReduced_along (P : Polynomial ℝ) {T : ℝ → ℝ} {dT θ : ℝ}
    (hT : HasDerivAt T dT θ) (hθ : θ ≠ π) :
    HasDerivAt (fun t : ℝ => ftUpperReduced P (T t) (t - π))
      (ftUpperReducedRadial P (T θ) (θ - π) * dT
        + ftUpperReducedSlope P (T θ) (θ - π)) θ := by
  have hterm : ∀ j ∈ Finset.range (P.natDegree + 1),
      HasDerivAt (fun t : ℝ => P.coeff j * (-1) ^ (j + 1) * T t ^ j
          * ((1 - (j : ℝ)) * Real.sinc ((1 - (j : ℝ)) * (t - π))))
        (P.coeff j * (-1) ^ (j + 1) * ((j : ℝ) * T θ ^ (j - 1))
            * ((1 - (j : ℝ)) * Real.sinc ((1 - (j : ℝ)) * (θ - π))) * dT
          + P.coeff j * (-1) ^ (j + 1) * T θ ^ j
            * ((1 - (j : ℝ)) * ((1 - (j : ℝ)) * sincDeriv ((1 - (j : ℝ)) * (θ - π))))) θ := by
    intro j _
    have hpow : HasDerivAt (fun t : ℝ => P.coeff j * (-1) ^ (j + 1) * T t ^ j)
        (P.coeff j * (-1) ^ (j + 1) * ((j : ℝ) * T θ ^ (j - 1) * dT)) θ :=
      (hT.pow j).const_mul _
    have hs : HasDerivAt
        (fun t : ℝ => (1 - (j : ℝ)) * Real.sinc ((1 - (j : ℝ)) * (t - π)))
        ((1 - (j : ℝ)) * ((1 - (j : ℝ)) * sincDeriv ((1 - (j : ℝ)) * (θ - π)))) θ :=
      (hasDerivAt_sinc_mul_sub (1 - (j : ℝ)) π hθ).const_mul _
    have h := hpow.mul hs
    refine h.congr_deriv ?_
    ring
  have hsum := HasDerivAt.fun_sum hterm
  have hfun : (fun t : ℝ => ∑ j ∈ Finset.range (P.natDegree + 1),
      P.coeff j * (-1) ^ (j + 1) * T t ^ j
        * ((1 - (j : ℝ)) * Real.sinc ((1 - (j : ℝ)) * (t - π))))
      = fun t : ℝ => ftUpperReduced P (T t) (t - π) := rfl
  rw [hfun] at hsum
  refine hsum.congr_deriv ?_
  rw [ftUpperReducedRadial, ftUpperReducedSlope, Finset.sum_mul, ← Finset.sum_add_distrib]

/-! ### The two partials at the endpoint -/

/-- The radial partial is the `τ`-derivative of the endpoint equation. -/
theorem hasDerivAt_ftUpperReduced_radial (P : Polynomial ℝ) (τ : ℝ) :
    HasDerivAt (fun x : ℝ => ftUpperReduced P x 0) (ftUpperReducedRadial P τ 0) τ := by
  have hterm : ∀ j ∈ Finset.range (P.natDegree + 1),
      HasDerivAt (fun x : ℝ => P.coeff j * (-1) ^ (j + 1) * x ^ j
          * ((1 - (j : ℝ)) * Real.sinc ((1 - (j : ℝ)) * 0)))
        (P.coeff j * (-1) ^ (j + 1) * ((j : ℝ) * τ ^ (j - 1))
          * ((1 - (j : ℝ)) * Real.sinc ((1 - (j : ℝ)) * 0))) τ := by
    intro j _
    have h := ((hasDerivAt_pow j τ).const_mul (P.coeff j * (-1) ^ (j + 1))).mul_const
      ((1 - (j : ℝ)) * Real.sinc ((1 - (j : ℝ)) * 0))
    refine h.congr_deriv ?_
    ring
  have hsum := HasDerivAt.fun_sum hterm
  have hfun : (fun x : ℝ => ∑ j ∈ Finset.range (P.natDegree + 1),
      P.coeff j * (-1) ^ (j + 1) * x ^ j
        * ((1 - (j : ℝ)) * Real.sinc ((1 - (j : ℝ)) * 0)))
      = fun x : ℝ => ftUpperReduced P x 0 := rfl
  rw [hfun] at hsum
  exact hsum

/-- **The radial partial at the endpoint is `-E'(-τ)`**, so at the collision it is nonzero
exactly because the zero is simple. -/
theorem ftUpperReducedRadial_zero (P : Polynomial ℝ) (τ : ℝ) :
    ftUpperReducedRadial P τ 0 = -((derivative (ftCriticalReal P 1)).eval (-τ)) := by
  have h1 := hasDerivAt_ftUpperReduced_radial P τ
  have hfun : (fun x : ℝ => ftUpperReduced P x 0)
      = fun x : ℝ => (ftCriticalReal P 1).eval (-x) := funext fun x => ftUpperReduced_zero P x
  rw [hfun] at h1
  have h2 : HasDerivAt (fun x : ℝ => (ftCriticalReal P 1).eval (-x))
      (-((derivative (ftCriticalReal P 1)).eval (-τ))) τ := by
    have hcomp : HasDerivAt ((fun x : ℝ => (ftCriticalReal P 1).eval x) ∘ (fun x : ℝ => -x))
        ((derivative (ftCriticalReal P 1)).eval (-τ) * (-1)) τ :=
      ((ftCriticalReal P 1).hasDerivAt (-τ)).comp τ (hasDerivAt_neg' τ)
    have hf : ((fun x : ℝ => (ftCriticalReal P 1).eval x) ∘ (fun x : ℝ => -x))
        = fun x : ℝ => (ftCriticalReal P 1).eval (-x) := rfl
    rw [hf] at hcomp
    refine hcomp.congr_deriv ?_
    ring
  exact h1.unique h2

/-- The radial partial is continuous along any pair of limits, stated as a `Tendsto` rather
than as joint continuity: the pencil's degree bounds the sum, and asking the elaborator to
unfold that inside a two-variable composition is expensive where this is used. -/
theorem tendsto_ftUpperReducedRadial (P : Polynomial ℝ) {ι : Type*} {F : Filter ι}
    {T φ : ι → ℝ} {L : ℝ} (hT : Tendsto T F (𝓝 L)) (hφ : Tendsto φ F (𝓝 0)) :
    Tendsto (fun i => ftUpperReducedRadial P (T i) (φ i)) F
      (𝓝 (ftUpperReducedRadial P L 0)) := by
  simp only [ftUpperReducedRadial]
  refine tendsto_finsetSum _ fun j _ => ?_
  have h1 : Tendsto (fun i => P.coeff j * (-1) ^ (j + 1) * ((j : ℝ) * T i ^ (j - 1))) F
      (𝓝 (P.coeff j * (-1) ^ (j + 1) * ((j : ℝ) * L ^ (j - 1)))) :=
    ((hT.pow (j - 1)).const_mul _).const_mul _
  have h2 : Tendsto (fun i => (1 - (j : ℝ)) * Real.sinc ((1 - (j : ℝ)) * φ i)) F
      (𝓝 ((1 - (j : ℝ)) * Real.sinc ((1 - (j : ℝ)) * 0))) :=
    (((Real.continuous_sinc.tendsto ((1 - (j : ℝ)) * 0)).comp
      (hφ.const_mul (1 - (j : ℝ)))).const_mul _)
  exact h1.mul h2

/-- **The angular partial is `O(φ)`**, with the same constant the quadratic rate is measured
with.  `\operatorname{sinc}'` vanishes at the origin, which is the evenness of
`ftUpperReduced` seen one derivative down. -/
theorem abs_ftUpperReducedSlope_le (P : Polynomial ℝ) {τ T : ℝ} (φ : ℝ) (hτ : |τ| ≤ T) :
    |ftUpperReducedSlope P τ φ| ≤ 3 * ftUpperReducedBound P T * |φ| := by
  have hT0 : 0 ≤ T := le_trans (abs_nonneg τ) hτ
  rw [ftUpperReducedSlope, ftUpperReducedBound, Finset.mul_sum, Finset.sum_mul]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun j _ => ?_)
  rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, mul_one,
    abs_pow, abs_mul]
  have hτj : |τ| ^ j ≤ T ^ j := pow_le_pow_left₀ (abs_nonneg τ) hτ j
  have hsinc := abs_sincDeriv_le ((1 - (j : ℝ)) * φ)
  rw [abs_mul] at hsinc
  have hstep : |P.coeff j| * |τ| ^ j * (|1 - (j : ℝ)|
        * (|1 - (j : ℝ)| * |sincDeriv ((1 - (j : ℝ)) * φ)|))
      ≤ |P.coeff j| * T ^ j * (|1 - (j : ℝ)|
        * (|1 - (j : ℝ)| * (|1 - (j : ℝ)| * |φ| / 2))) := by
    have h1 : |P.coeff j| * |τ| ^ j ≤ |P.coeff j| * T ^ j :=
      mul_le_mul_of_nonneg_left hτj (abs_nonneg _)
    have h2 : |1 - (j : ℝ)| * (|1 - (j : ℝ)| * |sincDeriv ((1 - (j : ℝ)) * φ)|)
        ≤ |1 - (j : ℝ)| * (|1 - (j : ℝ)| * (|1 - (j : ℝ)| * |φ| / 2)) := by
      have := mul_le_mul_of_nonneg_left hsinc (abs_nonneg (1 - (j : ℝ)))
      exact mul_le_mul_of_nonneg_left this (abs_nonneg (1 - (j : ℝ)))
    exact mul_le_mul h1 h2 (by positivity) (by positivity)
  refine le_trans hstep (le_of_eq ?_)
  have habs : |1 - (j : ℝ)| ^ 3 = |1 - (j : ℝ)| * (|1 - (j : ℝ)| * |1 - (j : ℝ)|) := by ring
  rw [habs]
  ring

/-! ### The slope bound -/

/-- **The branch radius has slope `O(π - θ)` at the `r = 1` upper endpoint.**  The reduced
equation vanishes identically along the branch, so its derivative there does too:
`A(θ)τ'(θ) + B(θ) = 0` with `A` bounded away from `0` by the simple zero of `E` and `B`
bounded by `O(π - θ)` by the vanishing of `\operatorname{sinc}'` at the origin.

This is what `UpperEndpointRadius`' quadratic rate cannot give — a bound on a function says
nothing about its derivative — and it is what the collar's Lipschitz binder asks for.

The endpoint equation `E(-L) = 0` is not among the hypotheses: it is implied by the radius
converging to `L`, since the reduced equation vanishes along the branch and is continuous. -/
theorem exists_linear_bound_ftTauDeriv_upper {n : ℕ} {a : Fin n → ℝ} {c L : ℝ}
    (hn2 : 2 ≤ n) (ha : ∀ k, 0 < a k) (hc : 0 < c) (hL : 0 < L)
    (hlim : Tendsto (ftTau a 1 (n - 1)) (𝓝[<] π) (𝓝 L)) :
    ∃ M δ : ℝ, 0 < δ ∧ ∀ θ ∈ Ioo (π - δ) π,
      |ftTauDeriv a 1 (n - 1) θ| ≤ M * (π - θ) := by
  classical
  have hn : 0 < n := by omega
  have hπ := Real.pi_pos
  have hpi : π / ((1 : ℕ) : ℝ) = π := pi_div_natCast_one
  -- the pencil is kept opaque: it is a product over `Fin n`, and letting the elaborator
  -- unfold it inside `ftUpperReducedRadial`'s degree bound is what makes this expensive
  obtain ⟨P, hP⟩ : ∃ P : Polynomial ℝ, P = ftRootPolyReal c a := ⟨_, rfl⟩
  have hA₀pos : 0 < ftUpperReducedRadial P L 0 := by
    rw [ftUpperReducedRadial_zero, hP]
    have := eval_derivative_ftCriticalReal_one_neg_lt_zero (a := a) (c := c) hn2 ha hc hL
    linarith
  have hbranchAll : ∀ t ∈ Ioo (0 : ℝ) (π / ((1 : ℕ) : ℝ)), FTBranchAt a 1 (n - 1) t :=
    fun t ht => ftBranchAt_of_arc_principal hn ha le_rfl (Or.inl hn2) ht
  have hgzero : ∀ t ∈ Ioo (0 : ℝ) π,
      ftUpperReduced P (ftTau a 1 (n - 1) t) (t - π) = 0 := by
    intro t ht
    have hz : ftPencilIm P 1 (ftTau a 1 (n - 1) t) t = 0 := by
      rw [hP]
      exact ftPencilIm_eq_zero c ha ht (hbranchAll t (by rw [hpi]; exact ht))
    have hfac : (t - π) * ftUpperReduced P (ftTau a 1 (n - 1) t) (t - π) = 0 := by
      rw [← ftPencilIm_pi_add, show π + (t - π) = t from by ring]
      exact hz
    rcases mul_eq_zero.1 hfac with h | h
    · exact absurd h (sub_ne_zero.2 (ne_of_lt ht.2))
    · exact h
  have hφ0 : Tendsto (fun θ : ℝ => θ - π) (𝓝[<] π) (𝓝 0) := by
    have h : Tendsto (fun θ : ℝ => θ - π) (𝓝[<] π) (𝓝 (π - π)) :=
      ((continuous_id.sub continuous_const).tendsto π).mono_left nhdsWithin_le_nhds
    simpa using h
  have hAt : Tendsto (fun θ : ℝ => ftUpperReducedRadial P (ftTau a 1 (n - 1) θ) (θ - π))
      (𝓝[<] π) (𝓝 (ftUpperReducedRadial P L 0)) :=
    tendsto_ftUpperReducedRadial P hlim hφ0
  have hevA : ∀ᶠ θ in 𝓝[<] π,
      ftUpperReducedRadial P L 0 / 2
        ≤ |ftUpperReducedRadial P (ftTau a 1 (n - 1) θ) (θ - π)| := by
    filter_upwards [hAt (Metric.ball_mem_nhds (ftUpperReducedRadial P L 0)
      (by linarith : (0:ℝ) < ftUpperReducedRadial P L 0 / 2))] with θ hθ
    have hb : ftUpperReducedRadial P (ftTau a 1 (n - 1) θ) (θ - π)
        ∈ Metric.ball (ftUpperReducedRadial P L 0) (ftUpperReducedRadial P L 0 / 2) := hθ
    rw [Metric.mem_ball, Real.dist_eq] at hb
    have h2 := abs_sub_abs_le_abs_sub (ftUpperReducedRadial P L 0)
      (ftUpperReducedRadial P (ftTau a 1 (n - 1) θ) (θ - π))
    rw [abs_of_pos hA₀pos, abs_sub_comm] at h2
    linarith
  have hevT : ∀ᶠ θ in 𝓝[<] π, |ftTau a 1 (n - 1) θ| ≤ L + 1 := by
    filter_upwards [hlim (Metric.ball_mem_nhds L one_pos)] with θ hθ
    have hb : ftTau a 1 (n - 1) θ ∈ Metric.ball L 1 := hθ
    rw [Metric.mem_ball, Real.dist_eq] at hb
    have h2 := abs_sub_abs_le_abs_sub (ftTau a 1 (n - 1) θ) L
    rw [abs_of_pos hL] at h2
    linarith
  obtain ⟨u, hu, hsub⟩ := mem_nhdsLT_iff_exists_Ioo_subset.1 (hevA.and hevT)
  have huπ : u < π := hu
  have hBd0 : 0 ≤ ftUpperReducedBound P (L + 1) := by
    rw [ftUpperReducedBound]
    refine Finset.sum_nonneg fun j _ => ?_
    have hL1 : (0 : ℝ) ≤ L + 1 := by linarith
    positivity
  refine ⟨6 * ftUpperReducedBound P (L + 1) / ftUpperReducedRadial P L 0,
    min (π - u) π, lt_min (by linarith) hπ, fun θ hθ => ?_⟩
  have hmin1 : min (π - u) π ≤ π - u := min_le_left _ _
  have hmin2 : min (π - u) π ≤ π := min_le_right _ _
  have hθu : u < θ := by linarith [hθ.1]
  have hθ0 : 0 < θ := by linarith [hθ.1]
  have hθπ : θ ∈ Ioo (0 : ℝ) π := ⟨hθ0, hθ.2⟩
  obtain ⟨hAθ, hTθ⟩ := hsub ⟨hθu, hθ.2⟩
  have hτd : HasDerivAt (ftTau a 1 (n - 1)) (ftTauDeriv a 1 (n - 1) θ) θ :=
    hasDerivAt_ftTau hn ha le_rfl (by rw [hpi]; exact hθπ) hbranchAll
  have hg := hasDerivAt_ftUpperReduced_along P hτd (ne_of_lt hθ.2)
  have hg0 : HasDerivAt (fun t : ℝ => ftUpperReduced P (ftTau a 1 (n - 1) t) (t - π)) 0 θ := by
    refine (hasDerivAt_const θ (0 : ℝ)).congr_of_eventuallyEq ?_
    filter_upwards [isOpen_Ioo.mem_nhds (show θ ∈ Ioo (π - min (π - u) π) π from hθ)] with t ht
    have ht0 : 0 < t := by linarith [ht.1]
    exact hgzero t ⟨ht0, ht.2⟩
  have hkey : ftUpperReducedRadial P (ftTau a 1 (n - 1) θ) (θ - π) * ftTauDeriv a 1 (n - 1) θ
      + ftUpperReducedSlope P (ftTau a 1 (n - 1) θ) (θ - π) = 0 := hg.unique hg0
  have hB := abs_ftUpperReducedSlope_le P (τ := ftTau a 1 (n - 1) θ) (T := L + 1) (θ - π) hTθ
  have habsφ : |θ - π| = π - θ := by
    rw [abs_of_nonpos (by linarith [hθ.2])]; ring
  rw [habsφ] at hB
  have hprod : |ftUpperReducedRadial P (ftTau a 1 (n - 1) θ) (θ - π)|
      * |ftTauDeriv a 1 (n - 1) θ|
      = |ftUpperReducedSlope P (ftTau a 1 (n - 1) θ) (θ - π)| := by
    rw [← abs_mul,
      show ftUpperReducedRadial P (ftTau a 1 (n - 1) θ) (θ - π) * ftTauDeriv a 1 (n - 1) θ
        = -ftUpperReducedSlope P (ftTau a 1 (n - 1) θ) (θ - π) from by linarith, abs_neg]
  have hstep : ftUpperReducedRadial P L 0 / 2 * |ftTauDeriv a 1 (n - 1) θ|
      ≤ 3 * ftUpperReducedBound P (L + 1) * (π - θ) :=
    calc ftUpperReducedRadial P L 0 / 2 * |ftTauDeriv a 1 (n - 1) θ|
        ≤ |ftUpperReducedRadial P (ftTau a 1 (n - 1) θ) (θ - π)|
            * |ftTauDeriv a 1 (n - 1) θ| :=
          mul_le_mul_of_nonneg_right hAθ (abs_nonneg _)
      _ = |ftUpperReducedSlope P (ftTau a 1 (n - 1) θ) (θ - π)| := hprod
      _ ≤ 3 * ftUpperReducedBound P (L + 1) * (π - θ) := hB
  rw [div_mul_eq_mul_div, le_div_iff₀ hA₀pos]
  linarith

end ForgacsTran
