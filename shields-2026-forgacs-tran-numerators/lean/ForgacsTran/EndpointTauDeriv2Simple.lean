/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib
import ForgacsTran.EndpointTauDeriv2
import ForgacsTran.LowerEndpointTangent
import ForgacsTran.FTBranchGap

/-!
# `τ''` at a **simple** smallest zero

`EndpointTauDeriv2` closes the `τ''` limit when the smallest zero is repeated.
This module is the other multiplicity, and it is not that argument with a
hypothesis relaxed: at `ρ = 1` the system there is **degenerate**.

At a repeated zero the branch runs into `x_1` itself, the cluster angle tends to
`π - π/ρ`, and the matrix `[[\sin(β-θ), Δ], [σ, ρ]]` has determinant tending to
`ρ\sin(π/ρ) ≠ 0`.  At a simple one the endpoint `L` is a critical point strictly
inside the first gap, no zero of the pencil is there, and every entry collapses:
`\sin(β-θ) → 0` because `β → 0`, `σ → 0`, `Δ → L - x_1 ≠ 0`, and the determinant
and the numerator **both** vanish to first order in `θ`.

The repair is to carry `B = β/θ` in place of `β`.  Dividing the two identities by
`θ` leaves them regular, and the rescaled system has determinant tending to

  `J = (B_0 - 1) + (L - x_1)\sum_{j≠i} a_j/(a_j - L)^2`,   `B_0 = L/(L - x_1)`,

which is positive because `B_0 - 1 = x_1/(L - x_1) > 0`.

**A `ρ ≥ 2` formula evaluated at `ρ = 1` is plausible rather than absurd, and
nothing here reuses one.**  `\cot(π/ρ)` is a pole at `ρ = 1` and Lean's `x/0 = 0`
collapses it to a well-formed value; `π - π/ρ` collapses to `0`, which is even the
*correct* limit of `β` here.  Both are right by accident and proved for `2 ≤ ρ`.
Every statement below is `ρ = 1`'s own.

## Main statements

* `tendsto_ftTau_slope_zero_of_simple` — `(τ - L)/θ → 0`, the rate the repeated
  case gets from `tendsto_ftTau_blowup` and this one cannot: the blow-up
  `τ = L - sθ` leaves the angle-sum limit independent of `s`, because the chord
  from `x_1` does not degenerate.  It comes instead from
  `LowerEndpointTangent.isLittleO_re_ftBranchPoint_sub`, whose real part is the
  statement itself.

## Implementation notes

Sorry-free.

## References

* `../../shields-2026-forgacs-tran-numerators.tex`, `sec:dominance`,
  `thm:weighted-dominance`.
* `../../scripts/check_endpoint_tau2_limit.py`.

## Tags

branch radius, second derivative, endpoint, simple zero, first gap
-/

namespace ForgacsTran

open Real Set Filter Topology

/-- **`(τ\cos θ - L)/θ → 0`.**  `LowerEndpointTangent`'s little-o, read as a
slope.  This is the one input the repeated case's blow-up cannot supply. -/
theorem tendsto_ftTau_cos_slope_of_simple {n r : ℕ} {a : Fin n → ℝ} {c L : ℝ}
    {i : Fin n} (hn2 : 2 ≤ n) (ha : ∀ k, 0 < a k) (hc : 0 < c) (hr : 1 ≤ r)
    (hLi : a i < L) (hgap : ∀ j, j ≠ i → L < a j)
    (hLe : (ftCriticalReal (ftRootPolyReal c a) r).eval L = 0)
    (hLt : Tendsto (ftTau a r (n - 1)) (𝓝[>] (0 : ℝ)) (𝓝 L)) :
    Tendsto (fun θ => (ftTau a r (n - 1) θ * Real.cos θ - L) / θ) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have h := (isLittleO_re_ftBranchPoint_sub hn2 ha hc hr hLi hgap hLe hLt).tendsto_div_nhds_zero
  refine h.congr fun θ => ?_
  rw [ftBranchPoint_re]
  rfl

/-- **`(τ - L)/θ → 0` at a simple smallest zero.**  The branch arrives at the
endpoint with zero radial slope: it does not come in along a ray, it comes in
across one.  The real part of `LowerEndpointTangent`'s little-o, with the
`\cos θ` divided back out. -/
theorem tendsto_ftTau_slope_zero_of_simple {n r : ℕ} {a : Fin n → ℝ} {c L : ℝ}
    {i : Fin n} (hn2 : 2 ≤ n) (ha : ∀ k, 0 < a k) (hc : 0 < c) (hr : 1 ≤ r)
    (hLi : a i < L) (hgap : ∀ j, j ≠ i → L < a j)
    (hLe : (ftCriticalReal (ftRootPolyReal c a) r).eval L = 0)
    (hLt : Tendsto (ftTau a r (n - 1)) (𝓝[>] (0 : ℝ)) (𝓝 L)) :
    Tendsto (fun θ => (ftTau a r (n - 1) θ - L) / θ) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hsub : 𝓝[>] (0 : ℝ) ≤ 𝓝[≠] (0 : ℝ) := nhdsWithin_mono _ fun x hx => ne_of_gt hx
  have h1 := tendsto_ftTau_cos_slope_of_simple hn2 ha hc hr hLi hgap hLe hLt
  have hcos : Tendsto (fun θ : ℝ => (Real.cos θ - 1) / θ) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h := hasDerivAt_iff_tendsto_slope.1 (Real.hasDerivAt_cos 0)
    simp only [Real.sin_zero, neg_zero] at h
    refine (h.mono_left hsub).congr fun θ => ?_
    simp [slope_def_field, div_eq_inv_mul]
  have h2 := h1.sub (hLt.mul hcos)
  rw [mul_zero, sub_zero] at h2
  refine h2.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with θ hθ
  have hne : θ ≠ 0 := ne_of_gt hθ
  field

/-! ### The endpoint equation

`E(L) = 0` is `\sum_k L/(L - a_k) = r` once the product is divided out, and that
is the value every limit below is measured against. -/

/-- The squared chord at the endpoint is `(c - L)^2`. -/
theorem ftChordSq_endpoint (c L : ℝ) : ftChordSq c L 0 = (c - L) ^ 2 := by
  rw [ftChordSq, Real.cos_zero]; ring

/-- **`E(L) = 0` in logarithmic form.**  At a simple smallest zero no `a_k` is at
`L`, so the product divides out and the critical polynomial's vanishing is the
statement that the reciprocal sum hits `r`.  This is the value every limit below
is measured against. -/
theorem sum_div_sub_eq_of_ftCriticalReal_eval {n r : ℕ} {a : Fin n → ℝ} {c L : ℝ}
    (hc : c ≠ 0) (hne : ∀ k, a k ≠ L)
    (hLe : (ftCriticalReal (ftRootPolyReal c a) r).eval L = 0) :
    ∑ k, L / (L - a k) = r := by
  classical
  have hsub : ∀ k, L - a k ≠ 0 := fun k => sub_ne_zero.2 fun h => (hne k) h.symm
  have hprod : (∏ k, (a k - L)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k _ => sub_ne_zero.2 (hne k)
  have hev : (ftRootPolyReal c a).eval L = c * ∏ k, (a k - L) := by
    simp [ftRootPolyReal, Polynomial.eval_prod]
  have hdev : (Polynomial.derivative (ftRootPolyReal c a)).eval L
      = -(c * ∑ k, ∏ j ∈ Finset.univ.erase k, (a j - L)) := by
    have hterm : ∀ k : Fin n,
        Polynomial.eval L ((∏ b ∈ Finset.univ.erase k, (Polynomial.C (a b) - Polynomial.X))
            * Polynomial.derivative (Polynomial.C (a k) - Polynomial.X))
          = -(∏ j ∈ Finset.univ.erase k, (a j - L)) := by
      intro k
      rw [Polynomial.eval_mul, Polynomial.eval_prod]
      simp
    rw [ftRootPolyReal, Polynomial.derivative_C_mul, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.derivative_prod_finset, Polynomial.eval_finsetSum,
      Finset.sum_congr rfl (fun k (_ : k ∈ Finset.univ) => hterm k), Finset.sum_neg_distrib]
    ring
  rw [eval_ftCriticalReal, hev, hdev] at hLe
  have hkey : ∀ k : Fin n, L / (L - a k) * ∏ j, (a j - L)
      = -(L * ∏ j ∈ Finset.univ.erase k, (a j - L)) := by
    intro k
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ k)]
    field [hsub k]
  have hcongr : ∑ k, (L / (L - a k) * ∏ j, (a j - L))
      = ∑ k, -(L * ∏ j ∈ Finset.univ.erase k, (a j - L)) :=
    Finset.sum_congr rfl fun k _ => hkey k
  refine mul_right_cancel₀ hprod ?_
  rw [Finset.sum_mul, hcongr, Finset.sum_neg_distrib, ← Finset.mul_sum]
  refine mul_left_cancel₀ hc ?_
  linear_combination hLe

/-! ### The two slopes -/

private theorem tendsto_sin_div : Tendsto (fun θ : ℝ => Real.sin θ / θ) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  have hsub : 𝓝[>] (0 : ℝ) ≤ 𝓝[≠] (0 : ℝ) := nhdsWithin_mono _ fun x hx => ne_of_gt hx
  have h := hasDerivAt_iff_tendsto_slope.1 (Real.hasDerivAt_sin 0)
  simp only [Real.cos_zero] at h
  refine (h.mono_left hsub).congr fun θ => ?_
  simp [slope_def_field, div_eq_inv_mul]

private theorem tendsto_ftChordSq_simple {T : ℝ → ℝ} {b L : ℝ}
    (hT : Tendsto T (𝓝[>] (0 : ℝ)) (𝓝 L)) :
    Tendsto (fun θ => ftChordSq b (T θ) θ) (𝓝[>] (0 : ℝ)) (𝓝 ((b - L) ^ 2)) := by
  have hD : ContinuousAt (fun p : ℝ × ℝ => ftChordSq b p.1 p.2) (L, 0) := by
    simp only [ftChordSq]; fun_prop
  have hpair : Tendsto (fun θ : ℝ => (T θ, θ)) (𝓝[>] (0 : ℝ)) (𝓝 (L, 0)) :=
    hT.prodMk_nhds (tendsto_id.mono_left nhdsWithin_le_nhds)
  have := hD.tendsto.comp hpair
  simpa [Function.comp_def, ftChordSq_endpoint] using this

/-! ### The two slopes of the branch equation's partials -/

private theorem eventually_arc_simple {r : ℕ} (hr : 1 ≤ r) :
    ∀ᶠ θ in 𝓝[>] (0 : ℝ), θ ∈ Ioo (0 : ℝ) (π / r) := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  exact Ioo_mem_nhdsGT (by positivity)

/-- **`∂_τΣ` vanishes linearly, with slope `-∑_k a_k/(a_k - L)^2`.**  Every chord
is off zero at a simple smallest zero — that is the whole difference from the
repeated case, where the cluster's chord dies — so all `n` partials are read off
one chart and the slope is a plain sum. -/
theorem tendsto_ftAngleSumDerivTau_slope_of_simple {n r : ℕ} {a : Fin n → ℝ} {L : ℝ}
    (hn : 0 < n) (ha : ∀ k, 0 < a k) (hr : 1 ≤ r) (hnr : 2 ≤ n ∨ 2 ≤ r)
    (hne : ∀ k, a k ≠ L)
    (hLt : Tendsto (ftTau a r (n - 1)) (𝓝[>] (0 : ℝ)) (𝓝 L)) :
    Tendsto (fun θ => ftAngleSumDerivTau a (ftTau a r (n - 1) θ) θ / θ) (𝓝[>] (0 : ℝ))
      (𝓝 (∑ k, -(a k) * 1 / (a k - L) ^ 2)) := by
  have hchart : Tendsto (fun θ => ∑ k, -(a k) * (Real.sin θ / θ)
      / ftChordSq (a k) (ftTau a r (n - 1) θ) θ) (𝓝[>] (0 : ℝ))
      (𝓝 (∑ k, -(a k) * 1 / (a k - L) ^ 2)) := by
    refine tendsto_finsetSum _ fun k _ => ?_
    exact ((tendsto_const_nhds (x := -(a k))).mul tendsto_sin_div).div
      (tendsto_ftChordSq_simple hLt) (pow_ne_zero _ (sub_ne_zero.2 (hne k)))
  refine hchart.congr' ?_
  filter_upwards [eventually_arc_simple (r := r) hr] with θ hθ
  have hpos := ftTau_pos (ftBranchAt_of_arc_principal hn ha hr hnr hθ)
  have hθπ := ftArc_subset hr hθ
  rw [ftAngleSumDerivTau, Finset.sum_div]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [ftAngleDerivTau_chart (ha k) hpos hθπ]
  ring

/-- The per-term algebra behind the second slope: the difference between the
chart form of `∂θ_k/∂θ` and its endpoint value is a combination of the two
slopes that are already known to vanish. -/
private theorem angleDerivAngle_sub_endpoint {b L p q D : ℝ} (hD : D ≠ 0) (hbL : L - b ≠ 0)
    (hDdef : D = b ^ 2 - 2 * b * q + p ^ 2) :
    (p ^ 2 - b * q) / D - L / (L - b)
      = b * (-((p - L) * (p + L)) + (L + b) * (q - L)) / (D * (L - b)) := by
  rw [div_sub_div _ _ hD hbL, hDdef]
  ring

/-- **`(∂_θΣ - r)/θ → 0`.**  The endpoint value of `∂_θΣ` is `r` by
`sum_div_sub_eq_of_ftCriticalReal_eval`, and the difference is carried entirely by
`(τ - L)/θ` and `(τ\cos θ - L)/θ`, both of which vanish. -/
theorem tendsto_ftAngleSumDerivAngle_sub_slope_of_simple {n r : ℕ} {a : Fin n → ℝ}
    {c L : ℝ} {i : Fin n} (hn2 : 2 ≤ n) (ha : ∀ k, 0 < a k) (hc : 0 < c) (hr : 1 ≤ r)
    (hnr : 2 ≤ n ∨ 2 ≤ r) (hLi : a i < L) (hgap : ∀ j, j ≠ i → L < a j)
    (hLe : (ftCriticalReal (ftRootPolyReal c a) r).eval L = 0)
    (hLt : Tendsto (ftTau a r (n - 1)) (𝓝[>] (0 : ℝ)) (𝓝 L)) :
    Tendsto (fun θ => (ftAngleSumDerivAngle a (ftTau a r (n - 1) θ) θ - r) / θ)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hn : 0 < n := by omega
  have hne : ∀ k, a k ≠ L := by
    intro k
    by_cases hk : k = i
    · subst hk; exact ne_of_lt hLi
    · exact ne_of_gt (hgap k hk)
  have hr' : (r : ℝ) = ∑ k, L / (L - a k) :=
    (sum_div_sub_eq_of_ftCriticalReal_eval hc.ne' hne hLe).symm
  have hp := tendsto_ftTau_slope_zero_of_simple hn2 ha hc hr hLi hgap hLe hLt
  have hq := tendsto_ftTau_cos_slope_of_simple hn2 ha hc hr hLi hgap hLe hLt
  have hchart : Tendsto (fun θ => ∑ k, a k
      * (-(((ftTau a r (n - 1) θ - L) / θ) * (ftTau a r (n - 1) θ + L))
        + (L + a k) * ((ftTau a r (n - 1) θ * Real.cos θ - L) / θ))
      / (ftChordSq (a k) (ftTau a r (n - 1) θ) θ * (L - a k))) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hz : (0 : ℝ) = ∑ _k : Fin n, (0 : ℝ) := by simp
    rw [hz]
    refine tendsto_finsetSum _ fun k _ => ?_
    have hden : ((a k - L) ^ 2 * (L - a k) : ℝ) ≠ 0 :=
      mul_ne_zero (pow_ne_zero _ (sub_ne_zero.2 (hne k)))
        (sub_ne_zero.2 fun h => (hne k) h.symm)
    have hnum : Tendsto (fun θ => a k
        * (-(((ftTau a r (n - 1) θ - L) / θ) * (ftTau a r (n - 1) θ + L))
          + (L + a k) * ((ftTau a r (n - 1) θ * Real.cos θ - L) / θ)))
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have := (tendsto_const_nhds (x := a k)).mul
        (((hp.mul (hLt.add (tendsto_const_nhds (x := L)))).neg).add
          ((tendsto_const_nhds (x := L + a k)).mul hq))
      simpa using this
    have hden' : Tendsto (fun θ => ftChordSq (a k) (ftTau a r (n - 1) θ) θ * (L - a k))
        (𝓝[>] (0 : ℝ)) (𝓝 ((a k - L) ^ 2 * (L - a k))) :=
      (tendsto_ftChordSq_simple hLt).mul (tendsto_const_nhds (x := L - a k))
    have h := hnum.mul (hden'.inv₀ hden)
    rw [zero_mul] at h
    simpa [div_eq_mul_inv] using h
  refine hchart.congr' ?_
  filter_upwards [eventually_arc_simple (r := r) hr, self_mem_nhdsWithin] with θ hθ hθ0
  have hpos := ftTau_pos (ftBranchAt_of_arc_principal hn ha hr hnr hθ)
  have hθπ := ftArc_subset hr hθ
  have hne0 : θ ≠ 0 := ne_of_gt hθ0
  rw [ftAngleSumDerivAngle, hr', ← Finset.sum_sub_distrib, Finset.sum_div]
  refine (Finset.sum_congr rfl fun k _ => ?_).symm
  have hterm : Real.sin (ftAngle (a k) (ftTau a r (n - 1) θ) θ)
      * Real.cos (ftAngle (a k) (ftTau a r (n - 1) θ) θ - θ) / Real.sin θ
      - L / (L - a k)
    = a k * (-((ftTau a r (n - 1) θ - L) * (ftTau a r (n - 1) θ + L))
        + (L + a k) * (ftTau a r (n - 1) θ * Real.cos θ - L))
      / (ftChordSq (a k) (ftTau a r (n - 1) θ) θ * (L - a k)) := by
    have hDdef : ftChordSq (a k) (ftTau a r (n - 1) θ) θ
        = a k ^ 2 - 2 * a k * (ftTau a r (n - 1) θ * Real.cos θ)
          + ftTau a r (n - 1) θ ^ 2 := by
      rw [ftChordSq]; ring
    rw [ftAngleDerivAngle_chart (ha k) hpos hθπ,
      show ftTau a r (n - 1) θ * (ftTau a r (n - 1) θ - a k * Real.cos θ)
        = ftTau a r (n - 1) θ ^ 2 - a k * (ftTau a r (n - 1) θ * Real.cos θ) from by ring]
    exact angleDerivAngle_sub_endpoint (ftChordSq_pos (ha k) hpos hθπ).ne'
      (sub_ne_zero.2 fun h => (hne k) h.symm) hDdef
  rw [hterm]
  field_simp

/-- **`τ' → 0` at a simple smallest zero.**  The quotient of the two slopes: the
numerator vanishes to first order and the denominator does not. -/
theorem tendsto_ftTauDeriv_zero_of_simple {n r : ℕ} {a : Fin n → ℝ} {c L : ℝ}
    {i : Fin n} (hn2 : 2 ≤ n) (ha : ∀ k, 0 < a k) (hc : 0 < c) (hr : 1 ≤ r)
    (hnr : 2 ≤ n ∨ 2 ≤ r) (hLi : a i < L) (hgap : ∀ j, j ≠ i → L < a j)
    (hLe : (ftCriticalReal (ftRootPolyReal c a) r).eval L = 0)
    (hLt : Tendsto (ftTau a r (n - 1)) (𝓝[>] (0 : ℝ)) (𝓝 L)) :
    Tendsto (ftTauDeriv a r (n - 1)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hn : 0 < n := by omega
  have hne : ∀ k, a k ≠ L := by
    intro k
    by_cases hk : k = i
    · subst hk; exact ne_of_lt hLi
    · exact ne_of_gt (hgap k hk)
  have hden : ∑ k, -(a k) * 1 / (a k - L) ^ 2 < 0 := by
    have hz : (0 : ℝ) = ∑ _k : Fin n, (0 : ℝ) := by simp
    rw [hz]
    refine Finset.sum_lt_sum_of_nonempty
      (Finset.univ_nonempty_iff.2 (Fin.pos_iff_nonempty.1 hn)) fun k _ => ?_
    have hsq : (0 : ℝ) < (a k - L) ^ 2 := by
      have := sub_ne_zero.2 (hne k)
      positivity
    exact div_neg_of_neg_of_pos (by nlinarith [ha k]) hsq
  have hnum := tendsto_ftAngleSumDerivAngle_sub_slope_of_simple hn2 ha hc hr hnr hLi hgap hLe hLt
  have hslope := tendsto_ftAngleSumDerivTau_slope_of_simple hn ha hr hnr hne hLt
  have hquot := (hnum.neg).div hslope hden.ne
  rw [neg_zero, zero_div] at hquot
  refine hquot.congr' ?_
  filter_upwards [eventually_arc_simple (r := r) hr, self_mem_nhdsWithin] with θ hθ hθ0
  have hpos := ftTau_pos (ftBranchAt_of_arc_principal hn ha hr hnr hθ)
  have hθπ := ftArc_subset hr hθ
  have hne0 : θ ≠ 0 := ne_of_gt hθ0
  have hSt : ftAngleSumDerivTau a (ftTau a r (n - 1) θ) θ ≠ 0 :=
    (ftAngleSumDerivTau_neg hn ha hpos hθπ).ne
  change (-((ftAngleSumDerivAngle a (ftTau a r (n - 1) θ) θ - r) / θ))
      / (ftAngleSumDerivTau a (ftTau a r (n - 1) θ) θ / θ)
    = ftTauDeriv a r (n - 1) θ
  rw [ftTauDeriv]
  field_simp

end ForgacsTran
