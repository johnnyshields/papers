/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import ForgacsTran.EndpointUpperBinders

/-!
# `eq:endpoint-linear-gap` at the upper endpoint

`hgapin₁`: the retained members' normalized moduli rise off `1` at a positive
linear rate, `‖g_j‖/τ ≥ 1 + c_1δ`.  The coefficient is
`(\cos(π/r) - \Re ω_j)/\sin(π/r)` with `ω_j = μ_je^{iπ/r}` an `r`-th root of
`-1` — the manuscript's own display, at `r` rather than at the lower endpoint's
`ρ`, and with the principal pair `ω = e^{\pm iπ/r}` excluded because those two
indices are the pair that was erased.

## The route, and why it is not the second-order one

The ratio is taken against the *principal point*, not against `τ`.  Then
`\overline{g_j/t_+} \to μ_j` and the `z`-free relation `Q(g)/Q(t_+) = (g/t_+)^r`
gives, to first order, `g_j/(μ_jt_+) = 1 + (β/r)(μ_j - 1)t_+ + o(t_+)` with
`β = Q'(0)/Q(0)`.  With `β = -\sum 1/a_k` and `t_+ \sim Le^{iπ/r}δ`,
`L = r/(\sin(π/r)\sum 1/a_k)`, the `\sum 1/a_k` cancels and the slope is
`-(μ_j - 1)e^{iπ/r}/\sin(π/r)`, whose real part is the display.

Taking the ratio against `τ` instead — which is what
`FTMinModulus.UpperEndpoint.norm_upper_member_expansion_le` prepares — carries the
`δ`-dependent rotation `t_+/τ = e^{i(π/r-δ)}` and so an extra `-i` in the slope.
That `-i` is purely imaginary and does not reach `\Re`, so both routes give the
same coefficient; this one never acquires it, and needs a limit rather than a
pointwise `O(δ^2)` bound.

## Main statements

* `eval_derivative_ftRootPoly_zero` — `Q'(0) = -Q(0)\sum 1/a_k` for the pencil.
* `tendsto_upper_member_slope` — the first-order relation, for any two colliding
  zeros of one pencil.
* `exists_upper_linear_gap` — `hgapin₁` at the branch.

## References

* `../../shields-2026-forgacs-tran-numerators.tex`, `eq:endpoint-linear-gap`.

## Tags

upper endpoint, linear gap, normalized root, weighted dominance
-/

namespace ForgacsTran

open Complex Filter Topology Polynomial
open scoped Topology

/-! ### `β = -\sum 1/a_k` -/

/-- **The pencil's logarithmic derivative at the origin.**  `Q = c\prod(a_k - t)`
gives `Q'(0) = -c\sum_k\prod_{m\ne k}a_m = -Q(0)\sum_k 1/a_k`.  This is the `β`
whose product with the collapse rate `L` cancels the pencil out of the gap
coefficient — a version losing it would pass at `\sum 1/a_k = 1` and fail
everywhere else. -/
theorem eval_derivative_ftRootPoly_zero {n : ℕ} {c : ℝ} {a : Fin n → ℝ}
    (ha : ∀ k, 0 < a k) :
    (Polynomial.derivative (ftRootPoly c a)).eval 0
      = -((ftRootPoly c a).eval 0 * ((∑ k, (a k)⁻¹ : ℝ) : ℂ)) := by
  classical
  have hane : ∀ k : Fin n, ((a k : ℝ) : ℂ) ≠ 0 := fun k => by exact_mod_cast (ha k).ne'
  have hstep : (Polynomial.derivative (ftRootPoly c a)).eval 0
      = -((c : ℂ) * ∑ k : Fin n, ∏ m ∈ (Finset.univ : Finset (Fin n)).erase k,
          ((a m : ℝ) : ℂ)) := by
    rw [ftRootPoly, Polynomial.derivative_mul, Polynomial.derivative_C, zero_mul, zero_add,
      Polynomial.derivative_prod_finset]
    simp [Polynomial.eval_finsetSum, Polynomial.eval_prod, Finset.mul_sum]
  rw [hstep, eval_ftRootPoly]
  push_cast
  rw [Finset.mul_sum, Finset.mul_sum, neg_inj]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h := Finset.prod_erase_mul (Finset.univ : Finset (Fin n))
    (fun m => ((a m : ℝ) : ℂ)) (Finset.mem_univ i)
  simp only [sub_zero]
  field_simp [hane i]
  linear_combination (c : ℂ) * h

/-! ### The first-order relation between two colliding zeros -/

/-- **The slope of a member against the principal point.**  If two zeros of one
pencil run into the origin with `g/t_+ \to μ` and `μ^r = 1`, then

`g/(μt_+) = 1 + (β/r)(μ - 1)t_+ + o(t_+)`,  `β = Q'(0)/Q(0)`.

The whole content is the `z`-free relation `Q(g)/Q(t_+) = (g/t_+)^r`, which needs
neither a factorization of `Q` nor a chart: at the origin `Q(0) \ne 0`, so `Q` is
its own cofactor.  `(1+v)^r - 1 = v\sum_{i<r}(1+v)^i` supplies the `r`, and
`Q(t) = tQ'(0) + Q(0) + o(t)` — read off `divX` rather than off a Taylor
estimate — supplies the `β`. -/
theorem tendsto_upper_member_slope {Q : Polynomial ℂ} {r : ℕ} (hr : 1 ≤ r)
    (hQ0 : Q.eval 0 ≠ 0) {g p zf : ℝ → ℂ} {μ : ℂ} (hμ : μ ^ r = 1)
    (hzne : ∀ᶠ δ in 𝓝[>] (0 : ℝ), zf δ ≠ 0)
    (hp0 : ∀ᶠ δ in 𝓝[>] (0 : ℝ), p δ ≠ 0)
    (hproot : ∀ᶠ δ in 𝓝[>] (0 : ℝ), (ftDen Q r (zf δ)).eval (p δ) = 0)
    (hgroot : ∀ᶠ δ in 𝓝[>] (0 : ℝ), (ftDen Q r (zf δ)).eval (g δ) = 0)
    (hptend : Filter.Tendsto p (𝓝[>] (0 : ℝ)) (𝓝 0))
    (hgtend : Filter.Tendsto g (𝓝[>] (0 : ℝ)) (𝓝 0))
    (hq : Filter.Tendsto (fun δ => g δ / p δ) (𝓝[>] (0 : ℝ)) (𝓝 μ)) :
    Filter.Tendsto (fun δ => (g δ / (μ * p δ) - 1) / p δ) (𝓝[>] (0 : ℝ))
      (𝓝 ((μ - 1) * (Polynomial.derivative Q).eval 0 / ((r : ℂ) * Q.eval 0))) := by
  classical
  have hrC : ((r : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hμ0 : μ ≠ 0 := by
    intro h0; rw [h0, zero_pow (by omega : r ≠ 0)] at hμ; exact zero_ne_one hμ
  set A : Polynomial ℂ := Polynomial.divX Q with hA
  have hAeval : ∀ t : ℂ, Q.eval t = t * A.eval t + Q.eval 0 := by
    intro t
    have h := congrArg (fun f : Polynomial ℂ => f.eval t) (Polynomial.X_mul_divX_add Q)
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
      Polynomial.eval_C] at h
    rw [← h, hA, Polynomial.coeff_zero_eq_eval_zero]
  have hA0 : A.eval 0 = (Polynomial.derivative Q).eval 0 := by
    rw [← Polynomial.coeff_zero_eq_eval_zero, ← Polynomial.coeff_zero_eq_eval_zero, hA,
      Polynomial.coeff_divX, Polynomial.coeff_derivative]
    simp
  set v : ℝ → ℂ := fun δ => g δ / (μ * p δ) - 1 with hv
  have hvtend : Filter.Tendsto v (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h1 : Filter.Tendsto (fun δ => (g δ / p δ) / μ) (𝓝[>] (0 : ℝ)) (𝓝 (μ / μ)) :=
      hq.div_const μ
    rw [div_self hμ0] at h1
    have h2 := h1.sub_const (1 : ℂ)
    rw [sub_self] at h2
    refine h2.congr' ?_
    filter_upwards [hp0] with δ hpne
    rw [hv]
    field_simp
  set W : ℝ → ℂ := fun δ => ∑ i ∈ Finset.range r, (1 + v δ) ^ i with hW
  have hWtend : Filter.Tendsto W (𝓝[>] (0 : ℝ)) (𝓝 (r : ℂ)) := by
    have hcont : Filter.Tendsto (fun δ => ∑ i ∈ Finset.range r, (1 + v δ) ^ i)
        (𝓝[>] (0 : ℝ)) (𝓝 (∑ i ∈ Finset.range r, (1 + (0 : ℂ)) ^ i)) :=
      tendsto_finsetSum _ fun i _ => ((hvtend.const_add 1).pow i)
    simpa using hcont
  -- `(1+v)^r - 1 = v·W` and `(1+v)^r = Q(g)/Q(p)`
  have hQp : ∀ᶠ δ in 𝓝[>] (0 : ℝ), Q.eval (p δ) ≠ 0 := by
    have := (((Q.continuous).tendsto 0).comp hptend).eventually_ne hQ0
    exact this
  have hkey : ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      v δ * W δ = (Q.eval (g δ) - Q.eval (p δ)) / Q.eval (p δ) := by
    filter_upwards [hzne, hp0, hproot, hgroot, hQp] with δ hzn hpn hpr hgr hqp
    have hgz : zf δ * g δ ^ r = -Q.eval (g δ) := by
      rw [ftDen_eval] at hgr; linear_combination hgr
    have hpz : zf δ * p δ ^ r = -Q.eval (p δ) := by
      rw [ftDen_eval] at hpr; linear_combination hpr
    have hratio : (g δ / p δ) ^ r = Q.eval (g δ) / Q.eval (p δ) := by
      rw [div_pow, div_eq_div_iff (pow_ne_zero _ hpn) hqp]
      linear_combination (g δ ^ r) * hpz - (p δ ^ r) * hgz
    have hone : (1 + v δ) ^ r = Q.eval (g δ) / Q.eval (p δ) := by
      have hid : 1 + v δ = (g δ / p δ) / μ := by rw [hv]; field_simp; ring
      rw [hid, div_pow, hμ, div_one, hratio]
    have hgeom : (∑ i ∈ Finset.range r, (1 + v δ) ^ i) * ((1 + v δ) - 1)
        = (1 + v δ) ^ r - 1 := geom_sum_mul _ _
    rw [hone] at hgeom
    have : v δ * W δ = (∑ i ∈ Finset.range r, (1 + v δ) ^ i) * ((1 + v δ) - 1) := by
      rw [hW]; ring
    rw [this, hgeom]
    field_simp
  -- the numerator's slope
  have hnum : Filter.Tendsto (fun δ => (Q.eval (g δ) - Q.eval (p δ)) / p δ)
      (𝓝[>] (0 : ℝ)) (𝓝 ((μ - 1) * A.eval 0)) := by
    have hAg : Filter.Tendsto (fun δ => A.eval (g δ)) (𝓝[>] (0 : ℝ)) (𝓝 (A.eval 0)) :=
      ((A.continuous).tendsto 0).comp hgtend
    have hAp : Filter.Tendsto (fun δ => A.eval (p δ)) (𝓝[>] (0 : ℝ)) (𝓝 (A.eval 0)) :=
      ((A.continuous).tendsto 0).comp hptend
    have hmain := (hq.mul hAg).sub hAp
    have hval : μ * A.eval 0 - A.eval 0 = (μ - 1) * A.eval 0 := by ring
    rw [hval] at hmain
    refine hmain.congr' ?_
    filter_upwards [hp0] with δ hpn
    rw [hAeval (g δ), hAeval (p δ)]
    field_simp
    ring
  -- assemble
  have hcomb : Filter.Tendsto (fun δ => v δ * W δ / p δ) (𝓝[>] (0 : ℝ))
      (𝓝 ((μ - 1) * A.eval 0 / Q.eval 0)) := by
    have hd := hnum.div (((Q.continuous).tendsto 0).comp hptend) hQ0
    refine hd.congr' ?_
    filter_upwards [hkey, hp0, hQp] with δ hk hpn hqp
    simp only [Pi.div_apply, Function.comp_apply]
    rw [hk]
    field_simp
  have hfinal := hcomb.div hWtend hrC
  have hval : (μ - 1) * A.eval 0 / Q.eval 0 / (r : ℂ)
      = (μ - 1) * (Polynomial.derivative Q).eval 0 / ((r : ℂ) * Q.eval 0) := by
    rw [hA0]; field_simp
  rw [hval] at hfinal
  refine hfinal.congr' ?_
  filter_upwards [hp0, hWtend.eventually_ne hrC] with δ hpn hwn
  simp only [Pi.div_apply]
  rw [hv]
  field_simp

/-! ### The gap coefficient at the branch -/

/-- The principal point's slope in the chart, as a quotient rather than a
derivative: `t_+(π/r - δ)/δ \to Le^{iπ/r}`. -/
theorem tendsto_ftPrincipal_div_upper {n r : ℕ} {a : Fin n → ℝ} {x₁ : ℝ}
    (hn2 : 2 ≤ n) (ha : ∀ k, 0 < a k) (hr : 2 ≤ r) :
    Filter.Tendsto
      (fun δ : ℝ => ftPrincipal (ftTauArc a r (n - 1) x₁) (Real.pi / r - δ) / (δ : ℂ))
      (𝓝[>] (0 : ℝ))
      (𝓝 ((((r : ℝ) / (Real.sin (Real.pi / r) * ∑ k, (a k)⁻¹) : ℝ) : ℂ)
        * Complex.exp (((Real.pi / r : ℝ) : ℂ) * Complex.I))) := by
  have hd := hasDerivWithinAt_ftPrincipal_ftTauArc_upper (x₁ := x₁) hn2 ha hr
  have hdiff : (Set.Ici (0 : ℝ)) \ {(0 : ℝ)} = Set.Ioi (0 : ℝ) := by
    ext u
    simp only [Set.mem_sdiff, Set.mem_Ici, Set.mem_singleton_iff, Set.mem_Ioi]
    exact ⟨fun h => lt_of_le_of_ne h.1 (Ne.symm h.2), fun h => ⟨h.le, ne_of_gt h⟩⟩
  rw [hasDerivWithinAt_iff_tendsto_slope, hdiff] at hd
  refine hd.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  have hδC : ((δ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt (show (0:ℝ) < δ from hδ)
  simp only [slope, vsub_eq_sub, sub_zero, Complex.real_smul, Complex.ofReal_inv]
  rw [ftPrincipal_ftTauArc_arc_end]
  field_simp
  ring

/-- **`eq:endpoint-linear-gap`'s coefficient, as a limit.**  A retained member's
normalized modulus rises off `1` at exactly
`(\cos(π/r) - \Re ω_j)/\sin(π/r)`, `ω_j = μ_je^{iπ/r}`.

The `\sum 1/a_k` cancels: it enters once through `β = Q'(0)/Q(0) = -\sum 1/a_k`
and once through the collapse rate `L = r/(\sin(π/r)\sum 1/a_k)`, so the
coefficient is a function of `r` and the direction alone.  A version that lost one
of the two would pass at `\sum 1/a_k = 1` and fail at every other pencil. -/
theorem tendsto_upper_normalized_modulus {n r : ℕ} {a : Fin n → ℝ} {c x₁ : ℝ}
    (hn2 : 2 ≤ n) (ha : ∀ k, 0 < a k) (hc : 0 < c) (hr : 2 ≤ r)
    {g : ℝ → ℂ} {j : ℕ}
    (hgroot : ∀ᶠ δ in 𝓝[>] (0 : ℝ), (ftDen (ftRootPoly c a) r
      ((ftBranchZ a c r (n - 1) (Real.pi / r - δ) : ℝ) : ℂ)).eval (g δ) = 0)
    (hgtend : Filter.Tendsto g (𝓝[>] (0 : ℝ)) (𝓝 0))
    (hq : Filter.Tendsto
      (fun δ => g δ / ftPrincipal (ftTauArc a r (n - 1) x₁) (Real.pi / r - δ))
      (𝓝[>] (0 : ℝ)) (𝓝 (clusterDir r j))) :
    Filter.Tendsto
      (fun δ : ℝ => (‖g δ‖ / ftTau a r (n - 1) (Real.pi / r - δ) - 1) / δ)
      (𝓝[>] (0 : ℝ))
      (𝓝 ((Real.cos (Real.pi / r)
        - (clusterDir r j * Complex.exp (((Real.pi / r : ℝ) : ℂ) * Complex.I)).re)
        / Real.sin (Real.pi / r))) := by
  classical
  have hπ := Real.pi_pos
  have hn : 0 < n := by omega
  have hr1 : 1 ≤ r := by omega
  have hrR : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hr0 : (0 : ℝ) < r := by linarith
  have hrC : ((r : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hmemπ : Real.pi / r ∈ Set.Ioo 0 Real.pi :=
    ⟨div_pos hπ hr0, by rw [div_lt_iff₀ hr0]; nlinarith⟩
  have hsin : 0 < Real.sin (Real.pi / r) :=
    Real.sin_pos_of_pos_of_lt_pi hmemπ.1 hmemπ.2
  have hnef : (Finset.univ : Finset (Fin n)).Nonempty :=
    Finset.univ_nonempty_iff.2 (Fin.pos_iff_nonempty.1 hn)
  have hS : 0 < ∑ k, (a k)⁻¹ := Finset.sum_pos (fun k _ => inv_pos.2 (ha k)) hnef
  have hQ0 : (ftRootPoly c a).eval 0 ≠ 0 := eval_ftRootPoly_zero_ne_zero hc.ne' ha
  set L : ℝ := (r : ℝ) / (Real.sin (Real.pi / r) * ∑ k, (a k)⁻¹) with hLdef
  set P : ℝ → ℂ := fun δ => ftPrincipal (ftTauArc a r (n - 1) x₁) (Real.pi / r - δ) with hP
  set T : ℝ → ℝ := fun δ => ftTau a r (n - 1) (Real.pi / r - δ) with hT
  set Z : ℝ → ℂ := fun δ => ((ftBranchZ a c r (n - 1) (Real.pi / r - δ) : ℝ) : ℂ) with hZ
  -- the branch's own data
  obtain ⟨eb, heb, hbw⟩ := exists_upper_branch_window (x₁ := x₁) hn2 ha hc hr (M := 1) one_pos
  have hwin : ∀ᶠ δ in 𝓝[>] (0 : ℝ), 0 < T δ ∧ ‖P δ‖ = T δ ∧ P δ ≠ 0
      ∧ (ftDen (ftRootPoly c a) r (Z δ)).eval (P δ) = 0 ∧ Z δ ≠ 0 := by
    refine eventually_of_window heb fun δ hδ hδe => ?_
    obtain ⟨hτpos, hagree, -, hProot, hZne⟩ := hbw δ hδ hδe
    have hτA : 0 < ftTauArc a r (n - 1) x₁ (Real.pi / r - δ) := by rw [hagree]; exact hτpos
    exact ⟨hτpos, by rw [hP, norm_ftPrincipal_eq hτA, hagree],
      ftPrincipal_ne_zero_of_pos hτA, hProot, hZne⟩
  have hPtend : Filter.Tendsto P (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hTtend : Filter.Tendsto T (𝓝[>] (0 : ℝ)) (𝓝 0) :=
      (tendsto_ftTau_nhdsLT_upper hn2 ha hr).comp tendsto_sub_nhdsGT_zero
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have habs : Filter.Tendsto (fun δ : ℝ => |T δ|) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      simpa using hTtend.abs
    refine habs.congr' ?_
    filter_upwards [hwin] with δ hd
    rw [hd.2.1, abs_of_pos hd.1]
  -- the slope against the principal point
  have hslope := tendsto_upper_member_slope (Q := ftRootPoly c a) hr1 hQ0
    (clusterDir_pow (by omega : r ≠ 0) j)
    (by filter_upwards [hwin] with δ hd using hd.2.2.2.2)
    (by filter_upwards [hwin] with δ hd using hd.2.2.1)
    (by filter_upwards [hwin] with δ hd using hd.2.2.2.1)
    hgroot hPtend hgtend hq
  -- times the principal point's own slope
  have hcomb := hslope.mul (tendsto_ftPrincipal_div_upper (x₁ := x₁) hn2 ha hr)
  -- the value of that product
  have hβ : (Polynomial.derivative (ftRootPoly c a)).eval 0
      = -((ftRootPoly c a).eval 0 * ((∑ k, (a k)⁻¹ : ℝ) : ℂ)) :=
    eval_derivative_ftRootPoly_zero ha
  have hSC : (((∑ k, (a k)⁻¹ : ℝ)) : ℂ) ≠ 0 := by exact_mod_cast hS.ne'
  have hsinC : ((Real.sin (Real.pi / r) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hsin.ne'
  have hval : (clusterDir r j - 1) * (Polynomial.derivative (ftRootPoly c a)).eval 0
        / ((r : ℂ) * (ftRootPoly c a).eval 0) * (((L : ℝ) : ℂ)
          * Complex.exp (((Real.pi / r : ℝ) : ℂ) * Complex.I))
      = (Complex.exp (((Real.pi / r : ℝ) : ℂ) * Complex.I)
          - clusterDir r j * Complex.exp (((Real.pi / r : ℝ) : ℂ) * Complex.I))
        / ((Real.sin (Real.pi / r) : ℝ) : ℂ) := by
    have hLC : ((L : ℝ) : ℂ) = (r : ℂ) / (((Real.sin (Real.pi / r) : ℝ) : ℂ)
        * (((∑ k, (a k)⁻¹ : ℝ)) : ℂ)) := by
      rw [hLdef]
      simp only [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_natCast]
    rw [hβ, hLC]
    have hcan : (((∑ k, (a k)⁻¹ : ℝ)) : ℂ) * (((∑ k, (a k)⁻¹ : ℝ)) : ℂ)⁻¹ = 1 :=
      mul_inv_cancel₀ hSC
    field_simp [hQ0, hrC, hsinC, hSC]
    simp only [one_div]
    linear_combination (1 - clusterDir r j) * hcan
  rw [hval] at hcomb
  -- transfer to the modulus
  have hFslope : Filter.Tendsto
      (fun δ : ℝ => (g δ / (clusterDir r j * P δ) - 1) / ((δ : ℝ) : ℂ))
      (𝓝[>] (0 : ℝ))
      (𝓝 ((Complex.exp (((Real.pi / r : ℝ) : ℂ) * Complex.I)
          - clusterDir r j * Complex.exp (((Real.pi / r : ℝ) : ℂ) * Complex.I))
        / ((Real.sin (Real.pi / r) : ℝ) : ℂ))) := by
    refine hcomb.congr' ?_
    filter_upwards [hwin, self_mem_nhdsWithin] with δ hd hδ
    have hδC : ((δ : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast ne_of_gt (show (0 : ℝ) < δ from hδ)
    have hPne : P δ ≠ 0 := hd.2.2.1
    rw [div_mul_div_comm, mul_comm (g δ / (clusterDir r j * P δ) - 1) (P δ),
      mul_div_mul_left _ _ hPne]
  have hnorm := tendsto_norm_sub_one_div_of_slope hFslope
  have hre : ((Complex.exp (((Real.pi / r : ℝ) : ℂ) * Complex.I)
        - clusterDir r j * Complex.exp (((Real.pi / r : ℝ) : ℂ) * Complex.I))
      / ((Real.sin (Real.pi / r) : ℝ) : ℂ)).re
      = (Real.cos (Real.pi / r)
        - (clusterDir r j * Complex.exp (((Real.pi / r : ℝ) : ℂ) * Complex.I)).re)
        / Real.sin (Real.pi / r) := by
    rw [Complex.div_ofReal_re, Complex.sub_re, Complex.exp_ofReal_mul_I_re]
  rw [hre] at hnorm
  refine hnorm.congr' ?_
  filter_upwards [hwin] with δ hd
  rw [norm_div, norm_mul, norm_clusterDir hr1, one_mul, hd.2.1]

/-! ### From the coefficients to `hgapin₁` -/

/-- **One rate for the whole family.**  Each normalized modulus rises at its own
positive rate; half the least of them is a rate that serves every member on one
window.  The lower endpoint's `exists_linear_gap_of_slopes` closes the same way,
from slopes rather than from moduli. -/
theorem exists_linear_gap_of_modulus_slopes {m : ℕ} {G : Fin m → ℝ → ℝ} {R : Fin m → ℝ}
    (hR : ∀ i, 0 < R i)
    (hlim : ∀ i, Filter.Tendsto (fun δ : ℝ => (G i δ - 1) / δ) (𝓝[>] (0 : ℝ)) (𝓝 (R i))) :
    ∃ c₁ > (0 : ℝ), ∃ e > (0 : ℝ), ∀ δ : ℝ, 0 < δ → δ ≤ e → ∀ i, 1 + c₁ * δ ≤ G i δ := by
  classical
  rcases isEmpty_or_nonempty (Fin m) with hem | hnem
  · exact ⟨1, one_pos, 1, one_pos, fun δ _ _ i => (hem.false i).elim⟩
  set c₁ : ℝ := (Finset.univ.inf' Finset.univ_nonempty R) / 2 with hc₁
  have hc₁pos : 0 < c₁ := by
    have : 0 < Finset.univ.inf' Finset.univ_nonempty R :=
      (Finset.lt_inf'_iff Finset.univ_nonempty).2 fun i _ => hR i
    rw [hc₁]; linarith
  have hc₁lt : ∀ i, c₁ < R i := by
    intro i
    have hle : Finset.univ.inf' Finset.univ_nonempty R ≤ R i :=
      Finset.inf'_le _ (Finset.mem_univ i)
    have := hR i
    rw [hc₁]; linarith
  have hev : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∀ i ∈ (Finset.univ : Finset (Fin m)),
      c₁ < (G i δ - 1) / δ :=
    (Filter.eventually_all_finset _).2 fun i _ => (hlim i).eventually_const_lt (hc₁lt i)
  obtain ⟨e, he, hw⟩ := window_of_eventually hev
  refine ⟨c₁, hc₁pos, e, he, fun δ hδ hδe i => ?_⟩
  have h := hw δ hδ hδe i (Finset.mem_univ i)
  rw [lt_div_iff₀ hδ] at h
  linarith

/-- **The gap coefficient is positive on the retained directions.**  `ω_j` is an
`r`-th root of `-1`, and the two directions excluded — `μ_j = 1` and
`μ_j = μ_{r-1}` — are exactly the ones whose `ω` is the principal pair
`e^{\pm iπ/r}`.  Those two are the indices `hgmem₁` erased, so every retained
member has a positive rate. -/
theorem upper_gap_coeff_pos {r j : ℕ} (hr : 2 ≤ r) (hj : j < r) (hj0 : j ≠ 0)
    (hjr : j ≠ r - 1) :
    0 < (Real.cos (Real.pi / r)
      - (clusterDir r j * Complex.exp (((Real.pi / r : ℝ) : ℂ) * Complex.I)).re)
      / Real.sin (Real.pi / r) := by
  have hrC : ((r : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  set ω₁ : ℂ := Complex.exp (((Real.pi / r : ℝ) : ℂ) * Complex.I) with hω₁
  have hω₁r : ω₁ ^ r = -1 := by
    rw [hω₁, ← Complex.exp_nat_mul]
    have : (r : ℂ) * (((Real.pi / r : ℝ) : ℂ) * Complex.I) = (Real.pi : ℂ) * Complex.I := by
      push_cast
      field_simp
    rw [this, Complex.exp_pi_mul_I]
  refine endpoint_linear_coeff_pos hr ?_ ?_ ?_
  · rw [mul_pow, clusterDir_pow (by omega : r ≠ 0) j, one_mul, hω₁r]
  · intro hEq
    have hd : clusterDir r j = clusterDir r 0 := by
      rw [clusterDir_zero]
      have hω0 : ω₁ ≠ 0 := Complex.exp_ne_zero _
      field_simp at hEq ⊢
      exact mul_right_cancel₀ hω0 (by rw [hEq, one_mul])
    exact hj0 (clusterDir_inj (by omega) hj (by omega) hd)
  · intro hEq
    have hlast : Complex.exp (((-(Real.pi / r) : ℝ) : ℂ) * Complex.I)
        = clusterDir r (r - 1) * ω₁ := by
      rw [clusterDir_last (by omega : 1 ≤ r), hω₁, ← Complex.exp_add]
      congr 1
      push_cast
      field_simp
      ring
    rw [hlast] at hEq
    have hω0 : ω₁ ≠ 0 := Complex.exp_ne_zero _
    exact hjr (clusterDir_inj (by omega) hj (by omega) (mul_right_cancel₀ hω0 hEq))

/-! ### The upper endpoint's block

One producer for the upper side of
`weighted_dominance_of_branch_any_multiplicity_at_of_threshold`: the retained set,
the enumeration, `hL₁`/`hratio₁`, and `hgapin₁`, all against one `R₁`, one `g₁`
and one window.  Stating them separately would leave three existentials that need
not name the same enumeration, which is exactly the defect the "which index"
family produces. -/

/-- **`thm:weighted-dominance`'s upper endpoint at the branch.**  `n_1 = r - 2`,
the separating circle is `R₁` with `τ ≤ R₁/2` so `σ₁ = 1/2`, and the retained
group is the directions `1, …, r-2` — the two the principal pair occupies are
erased.

What this does **not** carry is `hamp₁`, which is
`EndpointUpperPackage.exists_upper_amplitude_floor`, and `hCbd₁`, the contour
bound.  Neither is a consequence of the cluster geometry. -/
theorem exists_upper_endpoint_block {n r : ℕ} {a : Fin n → ℝ} {c x₁ : ℝ}
    (hn2 : 2 ≤ n) (ha : ∀ k, 0 < a k) (hc : 0 < c) (hr : 2 ≤ r)
    (hx₁ : 0 < x₁) :
    ∃ R₁ > (0 : ℝ), ∃ (sfun₁ : ℝ → Finset ℂ) (g₁ : ℝ → Fin (r - 2) → ℂ)
      (c₁ : ℝ), 0 < c₁
      ∧ (∃ e > (0 : ℝ), ∀ δ : ℝ, 0 < δ → δ ≤ e → ∀ i : Fin (r - 2),
          1 + c₁ * δ ≤ ‖g₁ (Real.pi / r - δ) i‖
            / ftTauArc a r (n - 1) x₁ (Real.pi / r - δ))
      ∧ (∃ e₁ > (0 : ℝ), ∀ δ : ℝ, 0 < δ → δ ≤ e₁ →
        0 < ftTauArc a r (n - 1) x₁ (Real.pi / r - δ)
        ∧ ftTauArc a r (n - 1) x₁ (Real.pi / r - δ) ≤ R₁ / 2
        ∧ (∀ t ∈ sfun₁ δ, (ftDen (ftRootPoly c a) r
            ((ftBranchZ a c r (n - 1) (Real.pi / r - δ) : ℝ) : ℂ)).eval t = 0)
        ∧ (∀ t ∈ sfun₁ δ, (Polynomial.derivative (ftDen (ftRootPoly c a) r
            ((ftBranchZ a c r (n - 1) (Real.pi / r - δ) : ℝ) : ℂ))).eval t ≠ 0)
        ∧ (∀ t ∈ sfun₁ δ, ‖t‖ < R₁)
        ∧ (∀ t : ℂ, ‖t‖ ≤ R₁ → (ftDen (ftRootPoly c a) r
            ((ftBranchZ a c r (n - 1) (Real.pi / r - δ) : ℝ) : ℂ)).eval t = 0 → t ∈ sfun₁ δ)
        ∧ (ftDen (ftRootPoly c a) r
            ((ftBranchZ a c r (n - 1) (Real.pi / r - δ) : ℝ) : ℂ)).eval
            (ftPrincipal (ftTauArc a r (n - 1) x₁) (Real.pi / r - δ)) = 0
        ∧ ftPrincipal (ftTauArc a r (n - 1) x₁) (Real.pi / r - δ)
            ≠ ((ftTauArc a r (n - 1) x₁ (Real.pi / r - δ) : ℝ) : ℂ)
              * Complex.exp (-((Real.pi / r - δ : ℝ) : ℂ) * I)
        ∧ Function.Injective (g₁ (Real.pi / r - δ))
        ∧ (∀ i : Fin (r - 2), g₁ (Real.pi / r - δ) i ∈
            ((sfun₁ δ).erase (ftPrincipal (ftTauArc a r (n - 1) x₁) (Real.pi / r - δ))).erase
              (((ftTauArc a r (n - 1) x₁ (Real.pi / r - δ) : ℝ) : ℂ)
                * Complex.exp (-((Real.pi / r - δ : ℝ) : ℂ) * I)))
        ∧ (((sfun₁ δ).erase (ftPrincipal (ftTauArc a r (n - 1) x₁) (Real.pi / r - δ))).erase
            (((ftTauArc a r (n - 1) x₁ (Real.pi / r - δ) : ℝ) : ℂ)
              * Complex.exp (-((Real.pi / r - δ : ℝ) : ℂ) * I))).card = r - 2)
      ∧ ∀ (B : Polynomial ℂ), B.eval 0 ≠ 0 → ∃ L₁ : Fin (r - 2) → ℂ,
          (∀ i, ‖L₁ i‖ = 1)
        ∧ (∀ i : Fin (r - 2), Filter.Tendsto
            (fun δ : ℝ => ftAmp (ftRootPoly c a) B r
                ((ftBranchZ a c r (n - 1) (Real.pi / r - δ) : ℝ) : ℂ)
                (g₁ (Real.pi / r - δ) i)
              / ftAmp (ftRootPoly c a) B r
                ((ftBranchZ a c r (n - 1) (Real.pi / r - δ) : ℝ) : ℂ)
                (ftPrincipal (ftTauArc a r (n - 1) x₁) (Real.pi / r - δ)))
            (𝓝[>] (0 : ℝ)) (𝓝 (L₁ i)))
           := by
  classical
  have hπ := Real.pi_pos
  have hn : 0 < n := by omega
  have hr1 : 1 ≤ r := by omega
  have hrR : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hr0 : (0 : ℝ) < r := by linarith
  have hbπ : Real.pi / r < Real.pi := by rw [div_lt_iff₀ hr0]; nlinarith
  have hQ0 : (ftRootPoly c a).eval 0 ≠ 0 := eval_ftRootPoly_zero_ne_zero hc.ne' ha
  obtain ⟨R₁, hR₁, G, happrox, e₁, he₁, hpk⟩ := exists_upper_cluster_package hn2 ha hc hr hx₁
  set P : ℝ → ℂ := fun δ => ftPrincipal (ftTauArc a r (n - 1) x₁) (Real.pi / r - δ) with hP
  set T : ℝ → ℝ := fun δ => ftTau a r (n - 1) (Real.pi / r - δ) with hT
  -- the eventual branch facts
  have hwin : ∀ᶠ δ in 𝓝[>] (0 : ℝ), 0 < T δ ∧ ‖P δ‖ = T δ ∧ P δ ≠ 0
      ∧ P δ ∈ ftUpperSet a c r (n - 1) R₁ δ
      ∧ (∀ t ∈ ftUpperSet a c r (n - 1) R₁ δ, (ftDen (ftRootPoly c a) r
          ((ftBranchZ a c r (n - 1) (Real.pi / r - δ) : ℝ) : ℂ)).eval t = 0)
      ∧ (∀ j : ℕ, G δ j ∈ ftUpperSet a c r (n - 1) R₁ δ) := by
    refine eventually_of_window he₁ fun δ hδ hδe => ?_
    obtain ⟨hτpos, hagree, -, -, hroot, -, -, -, hPmem, -, -, -, -, hGmem⟩ := hpk δ hδ hδe
    have hτA : 0 < ftTauArc a r (n - 1) x₁ (Real.pi / r - δ) := by rw [hagree]; exact hτpos
    exact ⟨hτpos, by rw [hP, norm_ftPrincipal_eq hτA, hagree],
      ftPrincipal_ne_zero_of_pos hτA, hPmem, hroot, hGmem⟩
  have hTtend : Filter.Tendsto T (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    (tendsto_ftTau_nhdsLT_upper hn2 ha hr).comp tendsto_sub_nhdsGT_zero
  have hPtend : Filter.Tendsto P (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have habs : Filter.Tendsto (fun δ : ℝ => |T δ|) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      simpa using hTtend.abs
    refine habs.congr' ?_
    filter_upwards [hwin] with δ hd
    rw [hd.2.1, abs_of_pos hd.1]
  have hGratio : ∀ j : ℕ, Filter.Tendsto (fun δ : ℝ => G δ j / P δ)
      (𝓝[>] (0 : ℝ)) (𝓝 (clusterDir r j)) := by
    intro j
    refine Metric.tendsto_nhds.2 fun ε hε => ?_
    obtain ⟨e, he, hw⟩ := happrox (ε / 2) (by linarith)
    filter_upwards [hwin, eventually_of_window he fun δ hδ hδe => hw δ hδ hδe j] with δ hd hb
    have hb' : ‖G δ j - clusterDir r j * P δ‖ ≤ ε / 2 * T δ := hb
    have hPne0 : P δ ≠ 0 := hd.2.2.1
    have hid : G δ j / P δ - clusterDir r j = (G δ j - clusterDir r j * P δ) / P δ := by
      field_simp
    rw [dist_eq_norm, hid, norm_div, hd.2.1, div_lt_iff₀ hd.1]
    nlinarith [hb', hd.1, hε]
  have hGtend : ∀ j : ℕ, Filter.Tendsto (fun δ : ℝ => G δ j) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    intro j
    have hmul := (hGratio j).mul hPtend
    rw [mul_zero] at hmul
    refine hmul.congr' ?_
    filter_upwards [hwin] with δ hd
    have hPne : P δ ≠ 0 := hd.2.2.1
    field_simp
  have hGroot : ∀ j : ℕ, ∀ᶠ δ in 𝓝[>] (0 : ℝ), (ftDen (ftRootPoly c a) r
      ((ftBranchZ a c r (n - 1) (Real.pi / r - δ) : ℝ) : ℂ)).eval (G δ j) = 0 := by
    intro j
    filter_upwards [hwin] with δ hd using hd.2.2.2.2.1 _ (hd.2.2.2.2.2 j)
  have hGne : ∀ j : ℕ, ∀ᶠ δ in 𝓝[>] (0 : ℝ), G δ j ≠ 0 := by
    intro j
    obtain ⟨e, he, hw⟩ := happrox (1 / 2) (by norm_num)
    filter_upwards [hwin, eventually_of_window he fun δ hδ hδe => hw δ hδ hδe j] with δ hd hb
    intro h0
    have hb' : ‖G δ j - clusterDir r j * P δ‖ ≤ 1 / 2 * T δ := hb
    rw [h0] at hb'
    simp only [zero_sub, norm_neg, norm_mul, norm_clusterDir hr1, one_mul, hd.2.1] at hb'
    linarith [hd.1]
  have hPne : ∀ᶠ δ in 𝓝[>] (0 : ℝ), P δ ≠ 0 := by
    filter_upwards [hwin] with δ hd using hd.2.2.1
  have hProot : ∀ᶠ δ in 𝓝[>] (0 : ℝ), (ftDen (ftRootPoly c a) r
      ((ftBranchZ a c r (n - 1) (Real.pi / r - δ) : ℝ) : ℂ)).eval (P δ) = 0 := by
    filter_upwards [hwin] with δ hd using hd.2.2.2.2.1 _ hd.2.2.2.1
  -- the gap
  obtain ⟨c₁, hc₁, eg, heg, hgap⟩ := exists_linear_gap_of_modulus_slopes
    (G := fun (i : Fin (r - 2)) (δ : ℝ) => ‖G δ ((i : ℕ) + 1)‖ / T δ)
    (R := fun i : Fin (r - 2) => (Real.cos (Real.pi / r)
      - (clusterDir r ((i : ℕ) + 1)
        * Complex.exp (((Real.pi / r : ℝ) : ℂ) * Complex.I)).re) / Real.sin (Real.pi / r))
    (fun i => by
      have hi := i.isLt
      exact upper_gap_coeff_pos hr (by omega) (by omega) (by omega))
    (fun i => tendsto_upper_normalized_modulus hn2 ha hc hr
      (hGroot ((i : ℕ) + 1)) (hGtend ((i : ℕ) + 1)) (hGratio ((i : ℕ) + 1)))
  refine ⟨R₁, hR₁, ftUpperSet a c r (n - 1) R₁,
    fun θ i => G (Real.pi / r - θ) ((i : ℕ) + 1), c₁, hc₁, ?_, ?_,
    fun B hB0 => ⟨fun i => clusterDir r ((i : ℕ) + 1),
      fun i => norm_clusterDir hr1 _, fun i => ?_⟩⟩
  · refine ⟨min eg e₁, lt_min heg he₁, fun δ hδ hδe i => ?_⟩
    obtain ⟨-, hagree, -, -, -, -, -, -, -, -, -, -, -, -⟩ :=
      hpk δ hδ (le_trans hδe (min_le_right _ _))
    simp only [show Real.pi / r - (Real.pi / r - δ) = δ from by ring, hagree]
    exact hgap δ hδ (le_trans hδe (min_le_left _ _)) i
  · refine ⟨min e₁ (Real.pi / (2 * r)), lt_min he₁ (by positivity), fun δ hδ hδe => ?_⟩
    obtain ⟨hτpos, hagree, hτR, hcard, hroot, haR, hsimp, huniq, hPmem, hcjmem, h0, hcj,
      hinj, hGmem⟩ := hpk δ hδ (le_trans hδe (min_le_left _ _))
    have hδb : δ < Real.pi / r := by
      have h1 : δ ≤ Real.pi / (2 * r) := le_trans hδe (min_le_right _ _)
      have h2 : Real.pi / (2 * r) < Real.pi / r := by
        rw [div_lt_div_iff₀ (by positivity) hr0]; nlinarith
      linarith
    have hτA : 0 < ftTauArc a r (n - 1) x₁ (Real.pi / r - δ) := by rw [hagree]; exact hτpos
    have hcancel : Real.pi / r - (Real.pi / r - δ) = δ := by ring
    have hcjeq : ((ftTauArc a r (n - 1) x₁ (Real.pi / r - δ) : ℝ) : ℂ)
        * Complex.exp (-((Real.pi / r - δ : ℝ) : ℂ) * I)
        = (starRingEnd ℂ) (ftPrincipal (ftTauArc a r (n - 1) x₁) (Real.pi / r - δ)) :=
      (conj_ftPrincipal' _ _).symm
    have hmemθ : Real.pi / r - δ ∈ Set.Ioo 0 Real.pi := ⟨by linarith, by linarith⟩
    have hne : ftPrincipal (ftTauArc a r (n - 1) x₁) (Real.pi / r - δ)
        ≠ ((ftTauArc a r (n - 1) x₁ (Real.pi / r - δ) : ℝ) : ℂ)
          * Complex.exp (-((Real.pi / r - δ : ℝ) : ℂ) * I) :=
      fun hEq => ftPrincipal_ne_conj_of_pos hτA hmemθ (hEq.trans hcjeq)
    have hcjS : (starRingEnd ℂ) (ftPrincipal (ftTauArc a r (n - 1) x₁) (Real.pi / r - δ))
        ∈ (ftUpperSet a c r (n - 1) R₁ δ).erase
          (ftPrincipal (ftTauArc a r (n - 1) x₁) (Real.pi / r - δ)) := by
      refine Finset.mem_erase.2 ⟨fun hEq => hne ?_, hcjmem⟩
      rw [hcjeq, hEq]
    refine ⟨hτA, by rw [hagree]; linarith, hroot, hsimp, haR, huniq, hroot _ hPmem, hne,
      ?_, ?_, ?_⟩
    · intro i j hij
      simp only [hcancel] at hij
      have hi := i.isLt
      have hj := j.isLt
      have := hinj ((i : ℕ) + 1) ((j : ℕ) + 1) (by omega) (by omega) hij
      exact Fin.ext (by omega)
    · intro i
      simp only [hcancel, hcjeq]
      have hilt := i.isLt
      have hi : (i : ℕ) + 1 < r := by omega
      refine Finset.mem_erase.2 ⟨fun hEq => ?_, Finset.mem_erase.2 ⟨fun hEq => ?_, hGmem _⟩⟩
      · rw [← hcj] at hEq
        have := hinj ((i : ℕ) + 1) (r - 1) hi (by omega) hEq
        omega
      · rw [← h0] at hEq
        have := hinj ((i : ℕ) + 1) 0 hi (by omega) hEq
        omega
    · rw [hcjeq, Finset.card_erase_of_mem hcjS, Finset.card_erase_of_mem hPmem, hcard]
      omega
  · simp only [show ∀ δ : ℝ, Real.pi / r - (Real.pi / r - δ) = δ from fun δ => by ring]
    exact tendsto_upper_amp_ratio hr1 hQ0 hB0 hPne (hGne _) hProot (hGroot _) hPtend
      (hGtend _) (hGratio _)

/-! ### `hCbd₁`: the contour bound at the upper endpoint

The binder is the *punctured* statement — `δ > 0` — rather than the closed-window
one, and that is not a convenience.  At `r ≥ 2` the closed form is unmeetable
here: `z` is unbounded as `δ \to 0` and a continuous function on a compact set is
bounded.  The punctured form is met with room to spare, because the same
divergence that breaks the closed form drives `|D|` up on the circle. -/

/-- **`hCbd₁` at the branch.**  On the separating circle `|D| \ge 1` once `|z|`
clears the same threshold the retained-set count uses, so the ratio is bounded by
a bound on `|B|` alone — no compactness in `δ`, and no uniformity assumed. -/
theorem exists_upper_contour_bound {n r : ℕ} {a : Fin n → ℝ} {c : ℝ} {B : Polynomial ℂ}
    (hn : 0 < n) (ha : ∀ k, 0 < a k) (hc : 0 < c) (hr : 2 ≤ r) {R₁ : ℝ} (hR₁ : 0 < R₁) :
    ∃ C₁, 0 ≤ C₁ ∧ ∃ e > (0 : ℝ), ∀ δ : ℝ, 0 < δ → δ ≤ e →
      ∀ t ∈ Metric.sphere (0 : ℂ) R₁,
        ‖B.eval t / (ftDen (ftRootPoly c a) r
          ((ftBranchZ a c r (n - 1) (Real.pi / r - δ) : ℝ) : ℂ)).eval t‖ ≤ C₁ := by
  classical
  -- a bound on the numerator over the circle
  obtain ⟨MB, hMB⟩ := (isCompact_sphere (0 : ℂ) R₁).exists_bound_of_continuousOn
    (B.continuous.continuousOn)
  have hMB0 : 0 ≤ MB := by
    have hmem : ((R₁ : ℝ) : ℂ) ∈ Metric.sphere (0 : ℂ) R₁ := by
      simp [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR₁]
    exact le_trans (norm_nonneg _) (hMB _ hmem)
  set Cq : ℝ := |c| * ∏ k, (a k + R₁) with hCq
  have hCq0 : 0 ≤ Cq := by
    refine mul_nonneg (abs_nonneg c) (Finset.prod_nonneg fun k _ => ?_)
    have := ha k; linarith
  obtain ⟨e, he, hzw⟩ := exists_upper_z_window_ge hn ha hc hr ((Cq + 1) / R₁ ^ r)
  refine ⟨MB, hMB0, e, he, fun δ hδ hδe t ht => ?_⟩
  have htn : ‖t‖ = R₁ := by
    simpa [Complex.dist_eq, sub_zero] using Metric.mem_sphere.1 ht
  set z : ℂ := ((ftBranchZ a c r (n - 1) (Real.pi / r - δ) : ℝ) : ℂ) with hz
  have hzge : (Cq + 1) / R₁ ^ r ≤ ‖z‖ := hzw δ hδ hδe
  have hzt : Cq + 1 ≤ ‖z * t ^ r‖ := by
    rw [norm_mul, norm_pow, htn]
    have := mul_le_mul_of_nonneg_right hzge (by positivity : (0 : ℝ) ≤ R₁ ^ r)
    rwa [div_mul_cancel₀ _ (by positivity : (R₁ : ℝ) ^ r ≠ 0)] at this
  have hQle : ‖(ftRootPoly c a).eval t‖ ≤ Cq :=
    norm_eval_ftRootPoly_le_of_norm_le ha (le_of_eq htn)
  have hDge : 1 ≤ ‖(ftDen (ftRootPoly c a) r z).eval t‖ := by
    rw [ftDen_eval]
    have hsplit := norm_sub_norm_le (z * t ^ r) (-(ftRootPoly c a).eval t)
    rw [sub_neg_eq_add, norm_neg] at hsplit
    rw [add_comm]
    linarith
  have hDne : (0 : ℝ) < ‖(ftDen (ftRootPoly c a) r z).eval t‖ := by linarith
  rw [norm_div, div_le_iff₀ hDne]
  nlinarith [hMB t ht, hDge, hMB0]

end ForgacsTran
