/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import ForgacsTran.EndpointUpperOne
import ForgacsTran.TauArcAt
import ForgacsTran.UpperEndpointReduced

/-!
# The branch radius reaches the `r = 1` upper endpoint quadratically

`UpperEndpointReduced` divides the branch equation's degeneracy at `θ = π` out and leaves
`ftUpperReduced`, which is even in `φ = θ - π` and equals `E(-τ)` at `φ = 0`.  Those two
facts bracket the radius from opposite sides:

* the equation gives `|E(-τ(θ))| = |H(τ, 0) - H(τ, φ)| ≤ Bφ^2`, because `H` is even;
* the collision gives `m|τ(θ) - L| ≤ |E(-τ(θ))|`, because `-L` is a **simple** zero of `E`
  — `E' = XQ''` at `r = 1` and `Q''` is a sum of positive terms on the negative axis
  (`EndpointUpperOne.eval_derivative_two_ftRootPolyReal_pos`), the same positivity that
  makes the pencil's own root there exactly double.

So `|τ(θ) - L| ≤ (B/m)(π - θ)^2`.  This is the rate every endpoint binder at the `r = 1`
upper end is built on, and it is strictly stronger than the `O(π - θ)` a one-sided
derivative alone would give: the branch and its conjugate meet at `-L`, so the radius is
even about `π` and its slope there is `0`.

`scripts/check_r_one_upper_endpoint_regularity.py` measures the rate and the two constants
at `a = (1,1,3)`, `a = (1,1,1)` and `a = (1,2,4)`.

Sorry-free.

## Main statements

* `exists_linear_lower_bound_of_hasDerivAt` — a simple zero bounds a function from below
  linearly near it.
* `eval_derivative_ftCriticalReal_one` — `E' = XQ''` at `r = 1`, evaluated.
* `exists_quadratic_bound_ftTau_upper` — the rate.

## References

Formalizes `../../shields-2026-forgacs-tran-numerators.tex`, `sec:geometry`, `eq:ab-def`,
`lem:principal-endpoint-regularity`.

## Tags

upper endpoint, branch radius, simple zero, quadratic rate, Forgács–Tran
-/

namespace ForgacsTran

open Polynomial Set Real Filter Topology

/-- **A simple zero bounds its function from below linearly.**  If `f` vanishes at `x₀` with
nonzero derivative there, then `|f|` is at least `|d|/2` times the distance on a
neighbourhood.  This is the definition of the derivative read as a two-sided estimate, and
it needs no polynomial structure. -/
theorem exists_linear_lower_bound_of_hasDerivAt {f : ℝ → ℝ} {x₀ d : ℝ}
    (hf : HasDerivAt f d x₀) (h0 : f x₀ = 0) (hd : d ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x, |x - x₀| < δ → ‖d‖ / 2 * |x - x₀| ≤ |f x| := by
  have hslope : Tendsto (slope f x₀) (𝓝[≠] x₀) (𝓝 d) := hasDerivAt_iff_tendsto_slope.1 hf
  have hdpos : 0 < ‖d‖ := norm_pos_iff.2 hd
  have hev : ∀ᶠ x in 𝓝[≠] x₀, ‖d‖ / 2 ≤ ‖slope f x₀ x‖ := by
    filter_upwards [hslope (Metric.ball_mem_nhds d (by linarith : (0:ℝ) < ‖d‖ / 2))] with x hx
    have hlt : ‖slope f x₀ x - d‖ < ‖d‖ / 2 := mem_ball_iff_norm.1 hx
    have h1 : ‖d‖ - ‖slope f x₀ x‖ ≤ ‖slope f x₀ x - d‖ := by
      rw [← norm_sub_rev]
      exact norm_sub_norm_le d (slope f x₀ x)
    linarith
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hev
  obtain ⟨δ, hδ, hsub⟩ := hev
  refine ⟨δ, hδ, fun x hx => ?_⟩
  rcases eq_or_ne x x₀ with rfl | hne
  · simp
  · have hdist : dist x x₀ < δ := by rwa [Real.dist_eq]
    have hmem : ‖d‖ / 2 ≤ ‖slope f x₀ x‖ := hsub hdist hne
    have hx0 : x - x₀ ≠ 0 := sub_ne_zero.2 hne
    have hslopeval : slope f x₀ x = f x / (x - x₀) := by
      rw [slope_def_field, h0, sub_zero]
    rw [hslopeval] at hmem
    simp only [Real.norm_eq_abs, abs_div] at hmem
    rw [le_div_iff₀ (abs_pos.2 hx0)] at hmem
    exact hmem

/-- **`E' = XQ''` at `r = 1`.** -/
theorem derivative_ftCriticalReal_one (P : Polynomial ℝ) :
    derivative (ftCriticalReal P 1) = X * derivative (derivative P) := by
  rw [ftCriticalReal, derivative_sub, derivative_mul, derivative_X, derivative_C_mul]
  push_cast
  simp only [Polynomial.C_1, one_mul]
  ring

/-- **The endpoint's derivative does not vanish**, so the collision is a simple zero of `E`.
`E' = XQ''` at `r = 1`, and `Q''` is a sum of positive terms on the negative axis. -/
theorem eval_derivative_ftCriticalReal_one_neg_lt_zero {n : ℕ} {a : Fin n → ℝ} {c : ℝ}
    (hn2 : 2 ≤ n) (ha : ∀ k, 0 < a k) (hc : 0 < c) {L : ℝ} (hL : 0 < L) :
    (derivative (ftCriticalReal (ftRootPolyReal c a) 1)).eval (-L) < 0 := by
  rw [derivative_ftCriticalReal_one, eval_mul, eval_X]
  have h2 := eval_derivative_two_ftRootPolyReal_pos hn2 ha hc (by linarith : -L < 0)
  nlinarith

/-- **The branch radius reaches the `r = 1` upper endpoint quadratically.**  The reduced
equation is even in `φ = θ - π`, so it moves by `O(φ^2)`; the collision is a simple zero of
`E`, so `|τ - L|` is controlled by that motion.  Neither half is available at `2 ≤ r`, where
the endpoint is the origin and the radius reaches it linearly. -/
theorem exists_quadratic_bound_ftTau_upper {n : ℕ} {a : Fin n → ℝ} {c L : ℝ}
    (hn2 : 2 ≤ n) (ha : ∀ k, 0 < a k) (hc : 0 < c) (hL : 0 < L)
    (hLe : (ftCriticalReal (ftRootPolyReal c a) 1).eval (-L) = 0)
    (hlim : Tendsto (ftTau a 1 (n - 1)) (𝓝[<] π) (𝓝 L)) :
    ∃ K δ : ℝ, 0 < δ ∧ ∀ θ ∈ Ioo (π - δ) π,
      |ftTau a 1 (n - 1) θ - L| ≤ K * (π - θ) ^ 2 := by
  classical
  have hn : 0 < n := by omega
  have hπ := Real.pi_pos
  set P : Polynomial ℝ := ftRootPolyReal c a with hP
  set E : Polynomial ℝ := ftCriticalReal P 1 with hE
  set f : ℝ → ℝ := fun x => E.eval (-x) with hf
  have hfL : f L = 0 := hLe
  have hdE : (derivative E).eval (-L) < 0 :=
    eval_derivative_ftCriticalReal_one_neg_lt_zero hn2 ha hc hL
  have hfd : HasDerivAt f (-((derivative E).eval (-L))) L := by
    have hcomp : HasDerivAt ((fun x : ℝ => E.eval x) ∘ (fun x : ℝ => -x))
        ((derivative E).eval (-L) * (-1)) L :=
      (E.hasDerivAt (-L)).comp L (hasDerivAt_neg' L)
    have hfun : ((fun x : ℝ => E.eval x) ∘ (fun x : ℝ => -x)) = f := rfl
    rw [hfun] at hcomp
    have hval : (derivative E).eval (-L) * (-1) = -((derivative E).eval (-L)) := by ring
    rw [hval] at hcomp
    exact hcomp
  set d : ℝ := -((derivative E).eval (-L)) with hd
  have hdne : d ≠ 0 := by rw [hd]; linarith
  obtain ⟨δ₁, hδ₁, hlow⟩ := exists_linear_lower_bound_of_hasDerivAt hfd hfL hdne
  have hdnorm : 0 < ‖d‖ := norm_pos_iff.2 hdne
  have hev : ∀ᶠ θ in 𝓝[<] π, |ftTau a 1 (n - 1) θ - L| < min δ₁ 1 := by
    have h := hlim (Metric.ball_mem_nhds L (lt_min hδ₁ one_pos))
    filter_upwards [h] with θ hθ
    have hθ' : ftTau a 1 (n - 1) θ ∈ Metric.ball L (min δ₁ 1) := hθ
    rw [Metric.mem_ball, Real.dist_eq] at hθ'
    exact hθ'
  obtain ⟨u, hu, hsub⟩ := mem_nhdsLT_iff_exists_Ioo_subset.1 hev
  have huπ : u < π := hu
  refine ⟨2 * ftUpperReducedBound P (L + 1) / ‖d‖, min (π - u) π, lt_min (by linarith) hπ,
    fun θ hθ => ?_⟩
  have hmin1 : min (π - u) π ≤ π - u := min_le_left _ _
  have hmin2 : min (π - u) π ≤ π := min_le_right _ _
  have hθu : u < θ := by linarith [hθ.1]
  have hθ0 : 0 < θ := by linarith [hθ.1]
  have hθπ : θ ∈ Ioo (0 : ℝ) π := ⟨hθ0, hθ.2⟩
  have hwin : |ftTau a 1 (n - 1) θ - L| < min δ₁ 1 := hsub ⟨hθu, hθ.2⟩
  have harc : θ ∈ Ioo (0 : ℝ) (π / ((1 : ℕ) : ℝ)) := by
    rw [pi_div_natCast_one]; exact hθπ
  have hbranch : FTBranchAt a 1 (n - 1) θ :=
    ftBranchAt_of_arc_principal hn ha le_rfl (Or.inl hn2) harc
  have hzero : ftPencilIm P 1 (ftTau a 1 (n - 1) θ) θ = 0 :=
    ftPencilIm_eq_zero c ha hθπ hbranch
  have hfac : (θ - π) * ftUpperReduced P (ftTau a 1 (n - 1) θ) (θ - π) = 0 := by
    rw [← ftPencilIm_pi_add, show π + (θ - π) = θ from by ring]
    exact hzero
  have hφ : θ - π ≠ 0 := sub_ne_zero.2 (ne_of_lt hθ.2)
  have hred : ftUpperReduced P (ftTau a 1 (n - 1) θ) (θ - π) = 0 := by
    rcases mul_eq_zero.1 hfac with h | h
    · exact absurd h hφ
    · exact h
  have hτabs : |ftTau a 1 (n - 1) θ| ≤ L + 1 := by
    have h1 : |ftTau a 1 (n - 1) θ - L| < 1 := lt_of_lt_of_le hwin (min_le_right _ _)
    have h2 := abs_sub_abs_le_abs_sub (ftTau a 1 (n - 1) θ) L
    rw [abs_of_pos hL] at h2
    linarith
  have hupper : |f (ftTau a 1 (n - 1) θ)| ≤ ftUpperReducedBound P (L + 1) * (π - θ) ^ 2 := by
    have hval : f (ftTau a 1 (n - 1) θ) = ftUpperReduced P (ftTau a 1 (n - 1) θ) 0 := by
      rw [hf, ftUpperReduced_zero]
    have hq := abs_ftUpperReduced_sub_zero_le P (τ := ftTau a 1 (n - 1) θ)
      (T := L + 1) (θ - π) hτabs
    rw [hred, zero_sub, abs_neg] at hq
    rw [hval]
    refine le_trans hq (le_of_eq ?_)
    congr 1
    rw [← neg_sub π θ]
    ring
  have hlowθ : ‖d‖ / 2 * |ftTau a 1 (n - 1) θ - L| ≤ |f (ftTau a 1 (n - 1) θ)| :=
    hlow _ (lt_of_lt_of_le hwin (min_le_left _ _))
  rw [div_mul_eq_mul_div, le_div_iff₀ hdnorm]
  nlinarith [hlowθ, hupper]

/-- **The branch enters the `r = 1` upper endpoint with derivative `-iL`.**  `hd0` at the
collision, in the arc's own parameter, and the binder every endpoint estimate at that end
asks for.  The radius contributes nothing: it reaches `L` quadratically, so the whole
derivative is the rotation's, `L\,\tfrac{d}{dθ}e^{iθ}` at `π`.

The value is nonzero — its modulus is exactly `L` — which is what
`CollisionCollarLeft.exists_bound_im_logDeriv_ftCofactorAlong_at_collision_left` needs and
what the `2 ≤ r` endpoint gets from a rate into the origin instead. -/
theorem hasDerivWithinAt_ftPrincipal_ftTauArcAt_pi {n : ℕ} {a : Fin n → ℝ} {c x₁ L : ℝ}
    (hn2 : 2 ≤ n) (ha : ∀ k, 0 < a k) (hc : 0 < c) (hL : 0 < L)
    (hLe : (ftCriticalReal (ftRootPolyReal c a) 1).eval (-L) = 0)
    (hlim : Tendsto (ftTau a 1 (n - 1)) (𝓝[<] π) (𝓝 L)) :
    HasDerivWithinAt (ftPrincipal (ftTauArcAt a 1 (n - 1) x₁ L))
      (-(((L : ℝ) : ℂ) * Complex.I)) (Iic π) π := by
  have hπ := Real.pi_pos
  have hpi : π / ((1 : ℕ) : ℝ) = π := pi_div_natCast_one
  set τ : ℝ → ℝ := ftTauArcAt a 1 (n - 1) x₁ L with hτdef
  have hτπ : τ π = L := by
    rw [hτdef, ftTauArcAt, if_neg (by rw [hpi]; exact lt_irrefl π)]
  -- the rotation alone
  have hrot : HasDerivAt (fun θ : ℝ => ((L : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))
      (((L : ℝ) : ℂ) * (Complex.exp ((π : ℂ) * Complex.I) * (1 * Complex.I))) π :=
    ((((hasDerivAt_id π).ofReal_comp).mul_const Complex.I).cexp).const_mul _
  have hrotval : ((L : ℝ) : ℂ) * (Complex.exp ((π : ℂ) * Complex.I) * (1 * Complex.I))
      = -(((L : ℝ) : ℂ) * Complex.I) := by
    rw [show ((π : ℝ) : ℂ) = (π : ℂ) from rfl, Complex.exp_pi_mul_I]
    ring
  rw [hrotval] at hrot
  -- the radius contributes nothing, because it reaches `L` quadratically
  obtain ⟨K, δ, hδ, hquad⟩ :=
    exists_quadratic_bound_ftTau_upper (c := c) hn2 ha hc hL hLe hlim
  have hrem : HasDerivWithinAt
      (fun θ : ℝ => ((τ θ - L : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) 0 (Iic π) π := by
    rw [hasDerivWithinAt_iff_tendsto_slope]
    have hset : Iic π \ {π} = Iio π := by
      ext y; simp only [Set.mem_sdiff, mem_Iic, mem_singleton_iff, mem_Iio]
      constructor
      · rintro ⟨h1, h2⟩; exact lt_of_le_of_ne h1 h2
      · intro h; exact ⟨h.le, ne_of_lt h⟩
    rw [hset]
    have hz : ∀ᶠ y in 𝓝[<] π,
        ‖slope (fun θ : ℝ => ((τ θ - L : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) π y‖
          ≤ |K| * |y - π| := by
      have hmin1 : min δ π ≤ δ := min_le_left _ _
      have hmin2 : min δ π ≤ π := min_le_right _ _
      have hminpos : 0 < min δ π := lt_min hδ hπ
      filter_upwards [Ioo_mem_nhdsLT (by linarith : π - min δ π < π)] with y hy
      have hyδ : y ∈ Ioo (π - δ) π := ⟨by linarith [hy.1], hy.2⟩
      have hy0 : 0 < y := by linarith [hy.1]
      have hτy : τ y = ftTau a 1 (n - 1) y := by
        rw [hτdef, ftTauArcAt_agree a 1 (n - 1) x₁ L hy0 (by rw [hpi]; exact hy.2)]
      have hbd : |τ y - L| ≤ K * (π - y) ^ 2 := by rw [hτy]; exact hquad y hyδ
      have hyne : y - π ≠ 0 := sub_ne_zero.2 (ne_of_lt hy.2)
      have hfπ : ((τ π - L : ℝ) : ℂ) * Complex.exp ((π : ℂ) * Complex.I) = 0 := by
        rw [hτπ]; simp
      rw [slope, hfπ, vsub_eq_sub, sub_zero, norm_smul, norm_inv, Real.norm_eq_abs, norm_mul,
        Complex.norm_real, Complex.norm_exp_ofReal_mul_I, mul_one,
        inv_mul_le_iff₀ (abs_pos.2 hyne)]
      have hsq : (π - y) ^ 2 = |y - π| ^ 2 := by rw [sq_abs]; ring
      calc |τ y - L| ≤ K * (π - y) ^ 2 := hbd
        _ = K * |y - π| ^ 2 := by rw [hsq]
        _ ≤ |K| * |y - π| ^ 2 := by nlinarith [le_abs_self K, sq_nonneg (|y - π|)]
        _ = |y - π| * (|K| * |y - π|) := by ring
    have hg : Tendsto (fun y : ℝ => |K| * |y - π|) (𝓝[<] π) (𝓝 0) := by
      have h : Tendsto (fun y : ℝ => |K| * |y - π|) (𝓝[<] π) (𝓝 (|K| * |π - π|)) :=
        ((continuous_const.mul ((continuous_id.sub continuous_const).abs)).tendsto π).mono_left
          nhdsWithin_le_nhds
      simpa using h
    exact squeeze_zero_norm' hz hg
  -- the two pieces sum to the branch point
  have hsum := (hrot.hasDerivWithinAt (s := Iic π)).add hrem
  rw [add_zero] at hsum
  refine hsum.congr (fun y _ => ?_) ?_
  · simp only [ftPrincipal, Pi.add_apply]; push_cast; ring
  · simp only [ftPrincipal, Pi.add_apply, hτπ]; push_cast; ring

/-- `‖e^{iθ} - e^{iψ}‖ ≤ 2|θ - ψ|`, by the two coordinates separately. -/
theorem norm_exp_sub_exp_le (θ ψ : ℝ) :
    ‖Complex.exp ((θ : ℂ) * Complex.I) - Complex.exp ((ψ : ℂ) * Complex.I)‖
      ≤ 2 * |θ - ψ| := by
  have hre : (Complex.exp ((θ : ℂ) * Complex.I)
      - Complex.exp ((ψ : ℂ) * Complex.I)).re = Real.cos θ - Real.cos ψ := by
    rw [Complex.sub_re, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_re]
  have him : (Complex.exp ((θ : ℂ) * Complex.I)
      - Complex.exp ((ψ : ℂ) * Complex.I)).im = Real.sin θ - Real.sin ψ := by
    rw [Complex.sub_im, Complex.exp_ofReal_mul_I_im, Complex.exp_ofReal_mul_I_im]
  refine le_trans (Complex.norm_le_abs_re_add_abs_im _) ?_
  rw [hre, him]
  have h1 := Real.abs_cos_sub_cos_le θ ψ
  have h2 := Real.abs_sin_sub_sin_le θ ψ
  linarith


end ForgacsTran
