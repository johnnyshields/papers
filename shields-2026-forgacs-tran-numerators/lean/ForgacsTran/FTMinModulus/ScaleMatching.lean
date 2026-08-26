/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import ForgacsTran.FTMinModulus.RoucheModel

/-!
# Domination on the small circle, and the two scales matched

The cluster carries two scales: the radius `δ` of the endpoint window and the
radius `η` of the circle Rouché is run on.  The domination `‖pencil - model‖ <
‖model‖` has to hold on the circle for every small `δ`, which forces a relation
between them.  This module proves the domination and matches the scales.

## Main statements

* the domination statements of `### The domination holds for all small δ` — the
  model dominates the difference uniformly on the circle, for every `δ` below a
  threshold that does not depend on the direction.
* the matching statements of `### The two scales, matched` — the choice of `η` as
  a function of `δ` that makes the previous section's threshold non-vacuous, so
  that one `δ`-window serves every cluster member at once.

## References

* `../../shields-2026-forgacs-tran-numerators.tex`, «Spectral geometry, residues,
  and the principal amplitude» — `sec:geometry`, `lem:amplitude-divisor`.
* `Forgacs2017RationalDenominator`, Proposition 3 Case 2.

## Tags

domination, Rouché, scale matching, cluster, endpoint window
-/

namespace ForgacsTran

open Polynomial

/-! ### The domination holds for all small `δ`

Both increments are `o(δ^ρ)` on the circle while the model's lower bound is a
fixed multiple of `δ^ρ`, so `exists_ftDen_root_near_model_root`'s hypothesis is
discharged by taking `δ` small.  The `z`-rate enters as a *limit*, not as a
bound: the lower bound is `‖q(x_1)‖(ρ/2)κ‖u‖^ρ` and `‖u‖^ρ‖q(x_1)‖ = ‖z_0‖x_1^rδ^ρ`,
so the comparison is against `‖z_0‖` itself, which no upper bound on `z` supplies.
-/

/-- From `y^ρ = Kδ^ρ`, the crude linear bound `y ≤ (max\{K,1\})δ`.  The `ρ`-th
root of `K` is never named: `max\{K,1\}` dominates it on either side of `1`, and
a crude constant is all the estimate needs. -/
theorem le_max_one_mul_of_pow_eq {y K δ : ℝ} {ρ : ℕ} (hρ : 1 ≤ ρ) (hy : 0 ≤ y)
    (hK : 0 ≤ K) (hδ : 0 ≤ δ) (h : y ^ ρ = K * δ ^ ρ) : y ≤ max K 1 * δ := by
  have hB1 : (1 : ℝ) ≤ max K 1 := le_max_right _ _
  have hB0 : (0 : ℝ) ≤ max K 1 := le_trans zero_le_one hB1
  have hKB : K ≤ max K 1 ^ ρ :=
    le_trans (le_max_left _ _) (le_self_pow₀ hB1 (by omega))
  have hle : y ^ ρ ≤ (max K 1 * δ) ^ ρ := by
    rw [mul_pow, h]
    exact mul_le_mul_of_nonneg_right hKB (pow_nonneg hδ ρ)
  exact (pow_le_pow_iff_left₀ hy (mul_nonneg hB0 hδ) (by omega)).mp hle

/-- Every model root has the same modulus, `‖u‖^ρ‖c_1‖ = ‖c_0‖`: the `ρ`
directions lie on one circle, and the crude bound above turns its radius into a
multiple of `δ`. -/
theorem norm_model_root_pow {c₀ c₁ u : ℂ} {ρ : ℕ}
    (hroot : c₁ * u ^ ρ + c₀ = 0) : ‖u‖ ^ ρ * ‖c₁‖ = ‖c₀‖ := by
  have h : c₁ * u ^ ρ = -c₀ := by linear_combination hroot
  have hn := congrArg norm h
  rw [norm_mul, norm_pow, norm_neg, mul_comm] at hn
  exact hn

/-- **Every cluster direction carries a pencil root, for all small `δ`.**  With
the `z`-rate supplied as a limit `z(δ)/δ^ρ → z_0 ≠ 0`, there is an `ε` below
which each root `u` of the model `q(x_1)w^ρ + z_0x_1^rδ^ρ` has a root of the
pencil within `κ‖u‖` of `x_1 + u`.

`4κρ ≤ 1` is what keeps the `ρ` disks inside the separation of the model's own
roots, so the roots produced here are distinct — this is the existence half of
the cluster's member count, with the counting done on the model side by
`exists_root_of_dominated`. -/
theorem exists_ftDen_root_near_model_root_eventually {x₁ : ℝ} (hx : 0 < x₁)
    {ρ r : ℕ} (hρ : 1 ≤ ρ) {Q q : ℂ[X]}
    (hQ : Q = (X - C ((x₁ : ℝ) : ℂ)) ^ ρ * q)
    (hqx : q.eval ((x₁ : ℝ) : ℂ) ≠ 0)
    {z : ℝ → ℂ} {z₀ : ℂ} (hz₀ : z₀ ≠ 0)
    (hzrate : Filter.Tendsto (fun δ : ℝ => z δ / (δ : ℂ) ^ ρ)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds z₀))
    {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ * (4 * ρ) ≤ 1) :
    ∃ ε > 0, ∀ δ : ℝ, 0 < δ → δ < ε → ∀ u : ℂ,
      q.eval ((x₁ : ℝ) : ℂ) * u ^ ρ + z₀ * ((x₁ : ℝ) : ℂ) ^ r * (δ : ℂ) ^ ρ = 0 →
      ∃ t : ℂ, ‖t - (((x₁ : ℝ) : ℂ) + u)‖ < κ * ‖u‖ ∧ (ftDen Q r (z δ)).eval t = 0 := by
  set xc : ℂ := ((x₁ : ℝ) : ℂ) with hxc
  have hxcn : ‖xc‖ = x₁ := by
    rw [hxc, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx]
  have hxc0 : xc ≠ 0 := by
    rw [hxc]
    exact Complex.ofReal_ne_zero.mpr hx.ne'
  have hc₁ : (0 : ℝ) < ‖q.eval xc‖ := norm_pos_iff.mpr hqx
  have hz₀n : (0 : ℝ) < ‖z₀‖ := norm_pos_iff.mpr hz₀
  set K : ℝ := ‖z₀‖ * x₁ ^ r / ‖q.eval xc‖ with hK
  have hK0 : 0 < K := div_pos (mul_pos hz₀n (pow_pos hx r)) hc₁
  set B : ℝ := max K 1 with hB
  have hB1 : (1 : ℝ) ≤ B := le_max_right _ _
  have hB0 : (0 : ℝ) < B := lt_of_lt_of_le one_pos hB1
  set D : ℝ := (1 + κ) * B with hD
  have hD0 : 0 < D := mul_pos (by linarith only [hκ]) hB0
  set M : ℝ := x₁ + D with hM
  have hM0 : 0 < M := by rw [hM]; linarith only [hx, hD0]
  set L : ℝ := ∑ k ∈ Finset.range (q.natDegree + 1), ‖q.coeff k‖ * ((k : ℝ) * M ^ (k - 1))
    with hL
  have hL0 : 0 ≤ L := by
    rw [hL]
    exact Finset.sum_nonneg fun k _ =>
      mul_nonneg (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg k) (pow_nonneg hM0.le _))
  have hρR : (0 : ℝ) < (ρ : ℝ) := by exact_mod_cast hρ
  set m : ℝ := ‖q.eval xc‖ * ((ρ : ℝ) / 2 * κ * K) with hm
  have hm0 : 0 < m := by
    rw [hm]
    exact mul_pos hc₁ (mul_pos (mul_pos (by linarith only [hρR]) hκ) hK0)
  set C₁ : ℝ := L * D ^ (ρ + 1) + ‖z₀‖ * (r : ℝ) * M ^ (r - 1) * D with hC₁
  have hMr : (0 : ℝ) ≤ M ^ r := pow_nonneg hM0.le r
  have hMr1 : (0 : ℝ) ≤ M ^ (r - 1) := pow_nonneg hM0.le _
  have hC₁0 : 0 ≤ C₁ := by
    rw [hC₁]
    have h1 : 0 ≤ L * D ^ (ρ + 1) := mul_nonneg hL0 (pow_nonneg hD0.le _)
    have h2 : 0 ≤ ‖z₀‖ * (r : ℝ) * M ^ (r - 1) * D :=
      mul_nonneg (mul_nonneg (mul_nonneg (norm_nonneg _) (Nat.cast_nonneg r)) hMr1) hD0.le
    linarith only [h1, h2]
  clear_value K B D M L m C₁
  have hw : Filter.Tendsto (fun δ : ℝ => ‖z δ / (δ : ℂ) ^ ρ - z₀‖)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have h := (hzrate.sub_const z₀).norm
    simpa using h
  have hthr : (0 : ℝ) < m / (2 * (M ^ r + 1)) := div_pos hm0 (by linarith only [hMr])
  have hev : ∀ᶠ δ : ℝ in nhdsWithin 0 (Set.Ioi 0),
      ‖z δ / (δ : ℂ) ^ ρ - z₀‖ < m / (2 * (M ^ r + 1)) := hw.eventually_lt_const hthr
  rw [eventually_nhdsWithin_iff] at hev
  obtain ⟨ε₀, hε₀, hball⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨min (min (ε₀ / 2) 1) (m / (2 * (C₁ + 1))), ?_, ?_⟩
  · exact lt_min (lt_min (by linarith only [hε₀]) one_pos) (div_pos hm0 (by linarith only [hC₁0]))
  intro δ hδ hδε u hroot
  have hδ1 : δ ≤ 1 :=
    le_of_lt (lt_of_lt_of_le (lt_of_lt_of_le hδε (min_le_left _ _)) (min_le_right _ _))
  have hδd : dist δ (0 : ℝ) < ε₀ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hδ]
    have hhalf : δ < ε₀ / 2 :=
      lt_of_lt_of_le (lt_of_lt_of_le hδε (min_le_left _ _)) (min_le_left _ _)
    linarith only [hhalf, hε₀]
  have hwδ : ‖z δ / (δ : ℂ) ^ ρ - z₀‖ < m / (2 * (M ^ r + 1)) :=
    hball hδd (Set.mem_Ioi.mpr hδ)
  have hδC : C₁ * δ < m / 2 := by
    have hlt : δ < m / (2 * (C₁ + 1)) := lt_of_lt_of_le hδε (min_le_right _ _)
    have hp : (0 : ℝ) < 2 * (C₁ + 1) := by linarith only [hC₁0]
    have h2 : δ * (2 * (C₁ + 1)) < m := (lt_div_iff₀ hp).mp hlt
    nlinarith only [h2, hδ, hC₁0]
  have hupow : ‖u‖ ^ ρ = K * δ ^ ρ := by
    have hnc₀ : ‖z₀ * xc ^ r * (δ : ℂ) ^ ρ‖ = ‖z₀‖ * x₁ ^ r * δ ^ ρ := by
      rw [norm_mul, norm_mul, norm_pow, norm_pow, hxcn, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hδ]
    have h := norm_model_root_pow hroot
    rw [hnc₀] at h
    rw [hK, div_mul_eq_mul_div, eq_div_iff hc₁.ne']
    linarith only [h]
  have hunorm0 : 0 < ‖u‖ := by
    rcases (norm_nonneg u).lt_or_eq with h | h
    · exact h
    · exfalso
      rw [← h, zero_pow (by omega : ρ ≠ 0)] at hupow
      nlinarith only [hupow, pow_pos hδ ρ, hK0]
  have hule : ‖u‖ ≤ B * δ := by
    rw [hB]
    exact le_max_one_mul_of_pow_eq hρ (norm_nonneg u) hK0.le hδ.le hupow
  set R : ℝ := κ * ‖u‖ with hR
  have hR0 : 0 < R := by rw [hR]; exact mul_pos hκ hunorm0
  clear_value R
  have hRu : R * (4 * ρ) ≤ ‖u‖ := by
    rw [hR]
    have hcomm : κ * ‖u‖ * (4 * (ρ : ℝ)) = ‖u‖ * (κ * (4 * (ρ : ℝ))) := by ring
    rw [hcomm]
    calc ‖u‖ * (κ * (4 * (ρ : ℝ))) ≤ ‖u‖ * 1 :=
          mul_le_mul_of_nonneg_left hκ4 (norm_nonneg u)
      _ = ‖u‖ := mul_one _
  have hdom : ∀ t : ℂ, ‖t - (xc + u)‖ = R →
      ‖t - xc‖ ^ ρ * ‖q.eval t - q.eval xc‖
        + ‖z δ * t ^ r - z₀ * xc ^ r * (δ : ℂ) ^ ρ‖
        < ‖q.eval xc‖ * ((ρ : ℝ) / 2 * R * ‖u‖ ^ (ρ - 1)) := by
    intro t htc
    have htx : ‖t - xc‖ ≤ D * δ := by
      have h1 : t - xc = (t - (xc + u)) + u := by ring
      have h2 : ‖t - xc‖ ≤ R + ‖u‖ := by
        rw [h1]
        exact le_trans (norm_add_le _ _) (by rw [htc])
      have h3 : R + ‖u‖ = (1 + κ) * ‖u‖ := by rw [hR]; ring
      rw [h3] at h2
      calc ‖t - xc‖ ≤ (1 + κ) * ‖u‖ := h2
        _ ≤ (1 + κ) * (B * δ) := mul_le_mul_of_nonneg_left hule (by linarith only [hκ])
        _ = D * δ := by rw [hD]; ring
    have hDd : D * δ ≤ D := by nlinarith only [hD0, hδ1, hδ]
    have htM : ‖t‖ ≤ M := by
      have hsum : ‖t‖ ≤ ‖xc‖ + ‖t - xc‖ := norm_le_norm_add_norm_sub' t xc
      rw [hxcn] at hsum
      rw [hM]
      linarith only [hsum, htx, hDd]
    have hxM : ‖xc‖ ≤ M := by rw [hxcn, hM]; linarith only [hD0]
    have hincr : ‖t - xc‖ ^ ρ * ‖q.eval t - q.eval xc‖
        + ‖z δ * t ^ r - z₀ * xc ^ r * (δ : ℂ) ^ ρ‖
        ≤ (C₁ * δ + ‖z δ / (δ : ℂ) ^ ρ - z₀‖ * M ^ r) * δ ^ ρ :=
      norm_pencil_sub_model_le_of_norm_le hδ hD0.le hL hC₁ htM hxM htx
    have hRHS : ‖q.eval xc‖ * ((ρ : ℝ) / 2 * R * ‖u‖ ^ (ρ - 1)) = m * δ ^ ρ := by
      have hpw : ‖u‖ * ‖u‖ ^ (ρ - 1) = ‖u‖ ^ ρ := by
        conv_rhs => rw [show ρ = 1 + (ρ - 1) by omega]
        rw [pow_add, pow_one]
      rw [hR, hm]
      calc ‖q.eval xc‖ * ((ρ : ℝ) / 2 * (κ * ‖u‖) * ‖u‖ ^ (ρ - 1))
          = ‖q.eval xc‖ * ((ρ : ℝ) / 2 * κ * (‖u‖ * ‖u‖ ^ (ρ - 1))) := by ring
        _ = ‖q.eval xc‖ * ((ρ : ℝ) / 2 * κ * ‖u‖ ^ ρ) := by rw [hpw]
        _ = ‖q.eval xc‖ * ((ρ : ℝ) / 2 * κ * (K * δ ^ ρ)) := by rw [hupow]
        _ = ‖q.eval xc‖ * ((ρ : ℝ) / 2 * κ * K) * δ ^ ρ := by ring
    have hkey : C₁ * δ + ‖z δ / (δ : ℂ) ^ ρ - z₀‖ * M ^ r < m := by
      have h1 : ‖z δ / (δ : ℂ) ^ ρ - z₀‖ * M ^ r ≤ m / (2 * (M ^ r + 1)) * M ^ r :=
        mul_le_mul_of_nonneg_right hwδ.le hMr
      have hp : (0 : ℝ) < 2 * (M ^ r + 1) := by linarith
      have h2 : m / (2 * (M ^ r + 1)) * M ^ r < m / 2 := by
        rw [div_mul_eq_mul_div, div_lt_iff₀ hp]
        nlinarith only [hm0, hMr]
      linarith only [h1, h2, hδC]
    have hδρ : (0 : ℝ) < δ ^ ρ := pow_pos hδ ρ
    rw [hRHS]
    exact lt_of_le_of_lt hincr (mul_lt_mul_of_pos_right hkey hδρ)
  exact exists_ftDen_root_near_model_root hρ hQ hqx hxc0 hz₀ hδ hR0 hroot hRu hdom

/-- All `ρ` cluster directions have the same `ρ`-th power, because
`clusterOmega_pow` makes each `ω_j` a `ρ`-th root of `-1`.  One instance of the
model identity therefore carries all `ρ` of them. -/
theorem clusterAlpha_pow_eq {x₁ : ℝ} {ρ : ℕ} (hρ : 1 ≤ ρ) (j k : ℕ) :
    clusterAlpha x₁ ρ j ^ ρ = clusterAlpha x₁ ρ k ^ ρ := by
  simp only [clusterAlpha, div_pow, mul_pow, clusterOmega_pow hρ]

/-- **`hmodel` is satisfiable, and it *determines* `z_0`.**  The identity solves
for `z_0`, uniquely and nonzero, so it is a value for the branch's rate rather
than a restriction on the pencil: no pencil is excluded by naming it.

What is not settled here is that the branch's *own* rate is that value.  That is
a fact about `ftBranchZ`, it is what
`FTBranchZRate.exists_tendsto_ftBranchZ_div_pow` names in prose while stating
only `0 < z_0`, and `scripts/check_cluster_model_roots.py` measures it — at the
reference pencil, over a sweep, and against the branch followed numerically. -/
theorem exists_model_rate {x₁ : ℝ} (hx : 0 < x₁) {ρ : ℕ} (hρ : 2 ≤ ρ) {r : ℕ}
    {q : ℂ[X]} (hqx : q.eval ((x₁ : ℝ) : ℂ) ≠ 0) :
    ∃ z₀ : ℂ, z₀ ≠ 0 ∧
      q.eval ((x₁ : ℝ) : ℂ) * clusterAlpha x₁ ρ 1 ^ ρ
        + z₀ * ((x₁ : ℝ) : ℂ) ^ r = 0 := by
  have hxc : ((x₁ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have hα : clusterAlpha x₁ ρ 1 ≠ 0 := clusterAlpha_ne_zero hx hρ 1
  refine ⟨-(q.eval ((x₁ : ℝ) : ℂ) * clusterAlpha x₁ ρ 1 ^ ρ) / ((x₁ : ℝ) : ℂ) ^ r,
    ?_, ?_⟩
  · exact div_ne_zero (neg_ne_zero.mpr (mul_ne_zero hqx (pow_ne_zero ρ hα)))
      (pow_ne_zero r hxc)
  · field_simp
    ring

/-- **The lower cluster's members exist, one per direction.**  For all small `δ`
each of the `ρ` directions of `eq:lower-cluster-expansion` carries a root of the
pencil within `κx_1/sin(π/ρ)` of `x_1 + α_jδ`.

`hmodel` is the one scalar identity saying the cluster directions *are* the
Rouché model's own roots, `q(x_1)α_j^ρ + z_0x_1^r = 0`.  It is stated at `j = 1`
and `clusterAlpha_pow_eq` carries it to every `j`.  It is a sign question rather
than a modulus one — `q(x_1)` picks up `(-1)^ρ` from writing `∏(a_k - t)` as
`(t-x_1)^ρq(t)` and `α_j^ρ` picks up another, and the two have to cancel against
`ω_j^ρ = -1` — and it holds exactly when `z_0` takes the value
`c(x_1/sin(π/ρ))^ρ∏_{k∉ S}(a_k-x_1)/x_1^r` that
`FTBranchZRate.exists_tendsto_ftBranchZ_div_pow` names in prose.  That lemma
currently states only `0 < z_0`, so the value is the one input this composition
still has to be handed; `scripts/check_cluster_model_roots.py` measures the
identity, over a sweep, and follows the branch's own rate to it. -/
theorem exists_cluster_member_family {x₁ : ℝ} (hx : 0 < x₁) {ρ r : ℕ} (hρ : 2 ≤ ρ)
    {Q q : ℂ[X]} (hQ : Q = (X - C ((x₁ : ℝ) : ℂ)) ^ ρ * q)
    (hqx : q.eval ((x₁ : ℝ) : ℂ) ≠ 0)
    {z : ℝ → ℂ} {z₀ : ℂ} (hz₀ : z₀ ≠ 0)
    (hzrate : Filter.Tendsto (fun δ : ℝ => z δ / (δ : ℂ) ^ ρ)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds z₀))
    (hmodel : q.eval ((x₁ : ℝ) : ℂ) * clusterAlpha x₁ ρ 1 ^ ρ
      + z₀ * ((x₁ : ℝ) : ℂ) ^ r = 0)
    {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ * (4 * ρ) ≤ 1) :
    ∃ ε > 0, ∀ δ : ℝ, 0 < δ → δ < ε → ∀ j : ℕ,
      ∃ t : ℂ, ‖t - (((x₁ : ℝ) : ℂ) + clusterAlpha x₁ ρ j * (δ : ℂ))‖
          < κ * (x₁ / Real.sin (Real.pi / ρ)) * δ
        ∧ (ftDen Q r (z δ)).eval t = 0 := by
  obtain ⟨ε, hε, hmain⟩ :=
    exists_ftDen_root_near_model_root_eventually hx (by omega : 1 ≤ ρ) hQ hqx hz₀
      hzrate hκ hκ4
  refine ⟨ε, hε, ?_⟩
  intro δ hδ hδε j
  have hroot : q.eval ((x₁ : ℝ) : ℂ) * (clusterAlpha x₁ ρ j * (δ : ℂ)) ^ ρ
      + z₀ * ((x₁ : ℝ) : ℂ) ^ r * (δ : ℂ) ^ ρ = 0 := by
    rw [mul_pow, clusterAlpha_pow_eq (by omega : 1 ≤ ρ) j 1]
    calc q.eval ((x₁ : ℝ) : ℂ) * (clusterAlpha x₁ ρ 1 ^ ρ * (δ : ℂ) ^ ρ)
          + z₀ * ((x₁ : ℝ) : ℂ) ^ r * (δ : ℂ) ^ ρ
        = (q.eval ((x₁ : ℝ) : ℂ) * clusterAlpha x₁ ρ 1 ^ ρ
            + z₀ * ((x₁ : ℝ) : ℂ) ^ r) * (δ : ℂ) ^ ρ := by ring
      _ = 0 := by rw [hmodel]; ring
  obtain ⟨t, ht1, ht2⟩ := hmain δ hδ hδε (clusterAlpha x₁ ρ j * (δ : ℂ)) hroot
  refine ⟨t, ?_, ht2⟩
  have hun : ‖clusterAlpha x₁ ρ j * (δ : ℂ)‖ = x₁ / Real.sin (Real.pi / ρ) * δ := by
    rw [norm_mul, norm_clusterAlpha hx hρ j, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hδ]
  rw [hun, ← mul_assoc] at ht1
  exact ht1

/-- **`exists_cluster_ratio_close`'s `hclose`, at `e = Kδ`.**  Two roots both
within `Aδ` of `x_1` put the `z`-free ratio within `Kδ` of `1`, and the same `ε`
delivers the two nondegeneracies that lemma also wants — `q(t) ≠ 0` and
`t_p ≠ 0` — together with `Kδ ≤ 1/2`.

Nothing here is asymptotic: `norm_cluster_ratio_sub_one_le` decomposes the ratio
exactly, and both increments are `O(‖t - t_p‖)`, hence `O(δ)`.  The denominator
is bounded below by `q`'s own continuity at `x_1` and by `‖t_p‖ ≥ x_1/2`, which
is what makes the constant explicit rather than obtained by compactness. -/
theorem exists_cluster_ratio_bound {q : ℂ[X]} {x₁ : ℝ} (hx : 0 < x₁)
    (hqx : q.eval ((x₁ : ℝ) : ℂ) ≠ 0) {r : ℕ} {A : ℝ} (hA : 0 ≤ A) :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ ε > 0, ∀ δ : ℝ, 0 < δ → δ < ε → ∀ t tp : ℂ,
      ‖t - ((x₁ : ℝ) : ℂ)‖ ≤ A * δ → ‖tp - ((x₁ : ℝ) : ℂ)‖ ≤ A * δ →
      q.eval t ≠ 0 ∧ tp ≠ 0 ∧ K * δ ≤ 1 / 2 ∧
        ‖q.eval tp * t ^ r / (q.eval t * tp ^ r) - 1‖ ≤ K * δ := by
  set xc : ℂ := ((x₁ : ℝ) : ℂ) with hxc
  have hxcn : ‖xc‖ = x₁ := by
    rw [hxc, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx]
  set M : ℝ := x₁ + A with hM
  have hM0 : 0 < M := by rw [hM]; linarith only [hx, hA]
  set L : ℝ := ∑ k ∈ Finset.range (q.natDegree + 1), ‖q.coeff k‖ * ((k : ℝ) * M ^ (k - 1))
    with hL
  have hL0 : 0 ≤ L := by
    rw [hL]
    exact Finset.sum_nonneg fun k _ =>
      mul_nonneg (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg k) (pow_nonneg hM0.le _))
  set Nq : ℝ := ‖q.eval xc‖ with hNq
  have hNq0 : 0 < Nq := by rw [hNq]; exact norm_pos_iff.mpr hqx
  set Dn : ℝ := Nq / 2 * (x₁ / 2) ^ r with hDn
  have hDn0 : 0 < Dn := by
    rw [hDn]
    exact mul_pos (by linarith only [hNq0]) (pow_pos (by linarith only [hx]) r)
  set N : ℝ := 3 * Nq * (r : ℝ) * M ^ (r - 1) * A + 2 * L * A * M ^ r with hN
  have hMr1 : (0 : ℝ) ≤ M ^ (r - 1) := pow_nonneg hM0.le _
  have hMr : (0 : ℝ) ≤ M ^ r := pow_nonneg hM0.le r
  have hN0 : 0 ≤ N := by
    rw [hN]
    have h1 : 0 ≤ 3 * Nq * (r : ℝ) * M ^ (r - 1) * A :=
      mul_nonneg (mul_nonneg (mul_nonneg (by linarith only [hNq0]) (Nat.cast_nonneg r)) hMr1) hA
    have h2 : 0 ≤ 2 * L * A * M ^ r :=
      mul_nonneg (mul_nonneg (by linarith only [hL0]) hA) hMr
    linarith only [h1, h2]
  set K : ℝ := N / Dn with hK
  have hK0 : 0 ≤ K := by rw [hK]; exact div_nonneg hN0 hDn0.le
  clear_value M L Nq Dn N K
  refine ⟨K, hK0, min (min 1 (x₁ / (2 * (A + 1)))) (min (Nq / (2 * (L * A + 1)))
    (1 / (2 * (K + 1)))), ?_, ?_⟩
  · refine lt_min (lt_min one_pos (div_pos hx (by linarith only [hA])))
      (lt_min (div_pos hNq0 (by nlinarith only [hL0, hA]))
        (div_pos one_pos (by linarith only [hK0])))
  intro δ hδ hδε t tp htx htpx
  have hδ1 : δ ≤ 1 :=
    le_of_lt (lt_of_lt_of_le (lt_of_lt_of_le hδε (min_le_left _ _)) (min_le_left _ _))
  have hAδ : A * δ ≤ x₁ / 2 := by
    have h1 : δ < x₁ / (2 * (A + 1)) :=
      lt_of_lt_of_le (lt_of_lt_of_le hδε (min_le_left _ _)) (min_le_right _ _)
    have h2 : δ * (2 * (A + 1)) < x₁ := (lt_div_iff₀ (by linarith only [hA])).mp h1
    nlinarith only [h2, hδ, hA]
  have hLAδ : L * A * δ ≤ Nq / 2 := by
    have h1 : δ < Nq / (2 * (L * A + 1)) :=
      lt_of_lt_of_le (lt_of_lt_of_le hδε (min_le_right _ _)) (min_le_left _ _)
    have hp : (0 : ℝ) < 2 * (L * A + 1) := by nlinarith only [hL0, hA]
    have h2 : δ * (2 * (L * A + 1)) < Nq := (lt_div_iff₀ hp).mp h1
    nlinarith only [h2, hδ, hL0, hA]
  have hKδ : K * δ ≤ 1 / 2 := by
    have h1 : δ < 1 / (2 * (K + 1)) :=
      lt_of_lt_of_le (lt_of_lt_of_le hδε (min_le_right _ _)) (min_le_right _ _)
    have hp : (0 : ℝ) < 2 * (K + 1) := by linarith only [hK0]
    have h2 : δ * (2 * (K + 1)) < 1 := (lt_div_iff₀ hp).mp h1
    nlinarith only [h2, hδ, hK0]
  -- the two points lie in the window
  have htM : ‖t‖ ≤ M := by
    have hsum : ‖t‖ ≤ ‖xc‖ + ‖t - xc‖ := norm_le_norm_add_norm_sub' t xc
    rw [hxcn] at hsum
    rw [hM]
    nlinarith only [hsum, htx, hAδ, hx, hA, hδ, hδ1]
  have htpM : ‖tp‖ ≤ M := by
    have hsum : ‖tp‖ ≤ ‖xc‖ + ‖tp - xc‖ := norm_le_norm_add_norm_sub' tp xc
    rw [hxcn] at hsum
    rw [hM]
    nlinarith only [hsum, htpx, hAδ, hx, hA, hδ, hδ1]
  have hxM : ‖xc‖ ≤ M := by rw [hxcn, hM]; linarith only [hA]
  have htplow : x₁ / 2 ≤ ‖tp‖ := by
    have hsub : ‖xc‖ - ‖tp‖ ≤ ‖xc - tp‖ := norm_sub_norm_le _ _
    rw [norm_sub_rev, hxcn] at hsub
    linarith only [hsub, htpx, hAδ]
  have htp0 : tp ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at htplow
    linarith only [htplow, hx]
  -- `q` stays away from zero on the window, and is bounded above on it
  have hLA : (∑ k ∈ Finset.range (q.natDegree + 1), ‖q.coeff k‖ * ((k : ℝ) * M ^ (k - 1)))
      * (A * δ) ≤ ‖q.eval xc‖ / 2 := by
    rw [← hL, ← hNq, ← mul_assoc]; exact hLAδ
  have hqt : Nq / 2 ≤ ‖q.eval t‖ := by
    rw [hNq]; exact (norm_eval_mem_of_norm_sub_le htM hxM htx hLA).1
  have hqtne : q.eval t ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hqt
    linarith only [hqt, hNq0]
  have hqtp : ‖q.eval tp‖ ≤ 3 * Nq / 2 := by
    have h := (norm_eval_mem_of_norm_sub_le htpM hxM htpx hLA).2
    rw [← hNq] at h
    linarith only [h]
  refine ⟨hqtne, htp0, hKδ, ?_⟩
  -- the two increments
  have http : ‖t - tp‖ ≤ 2 * (A * δ) := by
    have hsplit : t - tp = (t - xc) - (tp - xc) := by ring
    rw [hsplit]
    exact le_trans (norm_sub_le _ _) (by linarith only [htx, htpx])
  have hpowd : ‖t ^ r - tp ^ r‖ ≤ (r : ℝ) * M ^ (r - 1) * (2 * (A * δ)) := by
    refine le_trans (norm_pow_sub_pow_le_of_norm_le (M := M) htM htpM) ?_
    exact mul_le_mul_of_nonneg_left http
      (mul_nonneg (Nat.cast_nonneg r) hMr1)
  have hqd : ‖q.eval tp - q.eval t‖ ≤ L * (2 * (A * δ)) := by
    refine le_trans (norm_eval_sub_eval_le_of_norm_le (q := q) (M := M) htpM htM) ?_
    rw [← hL]
    refine mul_le_mul_of_nonneg_left ?_ hL0
    rw [norm_sub_rev]
    exact http
  have htpr : ‖tp‖ ^ r ≤ M ^ r := pow_le_pow_left₀ (norm_nonneg tp) htpM r
  have htprlow : (x₁ / 2) ^ r ≤ ‖tp‖ ^ r :=
    pow_le_pow_left₀ (by linarith only [hx]) htplow r
  -- numerator and denominator
  have hnum : ‖q.eval tp‖ * ‖t ^ r - tp ^ r‖ + ‖q.eval tp - q.eval t‖ * ‖tp‖ ^ r
      ≤ N * δ := by
    have h1 : ‖q.eval tp‖ * ‖t ^ r - tp ^ r‖
        ≤ 3 * Nq / 2 * ((r : ℝ) * M ^ (r - 1) * (2 * (A * δ))) :=
      mul_le_mul hqtp hpowd (norm_nonneg _) (by linarith only [hNq0])
    have h2 : ‖q.eval tp - q.eval t‖ * ‖tp‖ ^ r ≤ L * (2 * (A * δ)) * M ^ r :=
      mul_le_mul hqd htpr (pow_nonneg (norm_nonneg _) r)
        (mul_nonneg hL0 (by nlinarith only [hA, hδ]))
    rw [hN]
    nlinarith only [h1, h2]
  have hden : Dn ≤ ‖q.eval t‖ * ‖tp‖ ^ r := by
    rw [hDn]
    exact mul_le_mul hqt htprlow (pow_nonneg (by linarith only [hx]) r)
      (le_trans (by linarith only [hNq0]) hqt)
  refine le_trans (norm_cluster_ratio_sub_one_le hqtne htp0) ?_
  have hstep : (‖q.eval tp‖ * ‖t ^ r - tp ^ r‖ + ‖q.eval tp - q.eval t‖ * ‖tp‖ ^ r)
      / (‖q.eval t‖ * ‖tp‖ ^ r) ≤ N * δ / Dn :=
    div_le_div₀ (by nlinarith only [hN0, hδ]) hnum hDn0 hden
  refine le_trans hstep ?_
  rw [hK, div_mul_eq_mul_div]

/-! ### The two scales, matched

The Rouché step locates a member to `O(δ)` and names its direction; the ratio
step locates it to `O(δ^2)` but at an index it produces rather than accepts.
Matching the two needs a lower bound on the gap between distinct cluster
directions, and `norm_pow_sub_one_ge_of_near_one` already supplies one in its
contrapositive: a `ρ`-th root of unity other than `1` cannot be within `1/(4ρ)`
of `1`.  No trigonometry is needed — in particular not the sharp gap
`2sin(π/ρ)`, which is what a direct argument on the roots of `-1` would have to
prove.
-/

/-- **A nontrivial `ρ`-th root of unity is at least `1/(4ρ)` from `1`.**  The
contrapositive of `norm_pow_sub_one_ge_of_near_one`: inside that radius the
bound reads `(ρ/2)‖μ-1‖ ≤ ‖μ^ρ-1‖ = 0`. -/
theorem norm_sub_one_gt_of_pow_eq_one {μ : ℂ} {ρ : ℕ} (hρ : 1 ≤ ρ) (hμ : μ ^ ρ = 1)
    (hne : μ ≠ 1) : 1 / (4 * ρ) < ‖μ - 1‖ := by
  by_contra hcon
  push Not at hcon
  have hρR : (0 : ℝ) < 4 * ρ := by
    have : (1 : ℝ) ≤ (ρ : ℝ) := by exact_mod_cast hρ
    linarith only [this]
  have hh : ‖μ - 1‖ * (4 * ρ) ≤ 1 := (le_div_iff₀ hρR).mp hcon
  have hmain := norm_pow_sub_one_ge_of_near_one (s := μ) hh
  rw [hμ, sub_self, norm_zero] at hmain
  have hρ1 : (1 : ℝ) ≤ (ρ : ℝ) := by exact_mod_cast hρ
  have hz : ‖μ - 1‖ ≤ 0 := by nlinarith only [hmain, hρ1, norm_nonneg (μ - 1)]
  have hz0 : μ - 1 = 0 := norm_eq_zero.mp (le_antisymm hz (norm_nonneg _))
  exact hne (by linear_combination hz0)

/-- **Distinct cluster directions are separated, uniformly in the index.**  Any
two of them differ by a `ρ`-th root of unity — `clusterAlpha_pow_eq` makes the
ratio's `ρ`-th power `1` — so the gap is `‖α‖` times the previous bound.

The constant is crude: the true gap is `2x_1`, since `‖α_j - α_k‖ = ‖α‖‖ω_j-ω_k‖`
and the `ω` are `ρ`-th roots of `-1`.  What is proved here is `‖α‖/(4ρ)`, which
is smaller and needs no trigonometry, and the disks it has to beat are smaller
still. -/
theorem clusterAlpha_sep {x₁ : ℝ} (hx : 0 < x₁) {ρ : ℕ} (hρ : 2 ≤ ρ) {j k : ℕ}
    (hne : clusterAlpha x₁ ρ j ≠ clusterAlpha x₁ ρ k) :
    x₁ / Real.sin (Real.pi / ρ) / (4 * ρ)
      < ‖clusterAlpha x₁ ρ j - clusterAlpha x₁ ρ k‖ := by
  have hρ1 : 1 ≤ ρ := by omega
  have hj0 : clusterAlpha x₁ ρ j ≠ 0 := clusterAlpha_ne_zero hx hρ j
  have hjn : ‖clusterAlpha x₁ ρ j‖ = x₁ / Real.sin (Real.pi / ρ) :=
    norm_clusterAlpha hx hρ j
  set μ : ℂ := clusterAlpha x₁ ρ k / clusterAlpha x₁ ρ j with hμdef
  have hμ : μ ^ ρ = 1 := by
    rw [hμdef, div_pow, clusterAlpha_pow_eq hρ1 k j,
      div_self (pow_ne_zero ρ hj0)]
  have hμ1 : μ ≠ 1 := by
    intro h
    rw [hμdef, div_eq_one_iff_eq hj0] at h
    exact hne h.symm
  have hgap := norm_sub_one_gt_of_pow_eq_one hρ1 hμ hμ1
  have hfac : clusterAlpha x₁ ρ j - clusterAlpha x₁ ρ k
      = -((μ - 1) * clusterAlpha x₁ ρ j) := by
    rw [hμdef]
    field
  rw [hfac, norm_neg, norm_mul, hjn]
  have hs : 0 < x₁ / Real.sin (Real.pi / ρ) := div_pos hx (sin_pi_div_pos hρ)
  calc x₁ / Real.sin (Real.pi / ρ) / (4 * ρ)
      = 1 / (4 * ρ) * (x₁ / Real.sin (Real.pi / ρ)) := by ring
    _ < ‖μ - 1‖ * (x₁ / Real.sin (Real.pi / ρ)) := mul_lt_mul_of_pos_right hgap hs

/-- **The two scales agree on the direction.**  A point located within
`κ‖α‖δ` of `x_1 + α_jδ` and within `Cδ^2` of `x_1 + α_ωδ` has `α_j = α_ω`, once
`κ‖α‖ + Cδ` sits below the separation of `clusterAlpha_sep`.

This is what lets the `O(δ^2)` expansion, whose index is produced by
`exists_member_expansion_of_roots`, be read at the index the Rouché step chose. -/
theorem clusterAlpha_eq_of_mixed_scale {x₁ : ℝ} (hx : 0 < x₁) {ρ : ℕ} (hρ : 2 ≤ ρ)
    {j ω : ℕ} {t : ℂ} {δ C κ : ℝ} (hδ : 0 < δ)
    (hgap : κ * (x₁ / Real.sin (Real.pi / ρ)) + C * δ
      ≤ x₁ / Real.sin (Real.pi / ρ) / (4 * ρ))
    (h1 : ‖t - (((x₁ : ℝ) : ℂ) + clusterAlpha x₁ ρ j * (δ : ℂ))‖
      < κ * (x₁ / Real.sin (Real.pi / ρ)) * δ)
    (h2 : ‖t - (((x₁ : ℝ) : ℂ) + clusterAlpha x₁ ρ ω * (δ : ℂ))‖ ≤ C * δ ^ 2) :
    clusterAlpha x₁ ρ j = clusterAlpha x₁ ρ ω := by
  by_contra hne
  have hsep := clusterAlpha_sep hx hρ hne
  have hsplit : (clusterAlpha x₁ ρ j - clusterAlpha x₁ ρ ω) * (δ : ℂ)
      = (t - (((x₁ : ℝ) : ℂ) + clusterAlpha x₁ ρ ω * (δ : ℂ)))
        - (t - (((x₁ : ℝ) : ℂ) + clusterAlpha x₁ ρ j * (δ : ℂ))) := by ring
  have hnorm : ‖(clusterAlpha x₁ ρ j - clusterAlpha x₁ ρ ω) * (δ : ℂ)‖
      = ‖clusterAlpha x₁ ρ j - clusterAlpha x₁ ρ ω‖ * δ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδ]
  have hle : ‖clusterAlpha x₁ ρ j - clusterAlpha x₁ ρ ω‖ * δ
      ≤ C * δ ^ 2 + κ * (x₁ / Real.sin (Real.pi / ρ)) * δ := by
    rw [← hnorm, hsplit]
    exact le_trans (norm_sub_le _ _) (by linarith only [h1, h2])
  nlinarith only [hle, hsep, hgap, hδ]

/-- **`Forgacs2017RationalDenominator` Prop. 3 Case 2, the member leg, closed at
the family.**  Every cluster direction carries a pencil root expanding as
`eq:lower-cluster-expansion` says, to `O(δ^2)`, *at that direction* — the index
is chosen by the Rouché step and the expansion is then read at it, rather than
being whatever `exists_member_expansion_of_roots` happens to produce.

Four pieces meet here.  `exists_cluster_member_family` puts a root within
`κ‖α‖δ` of `x_1 + α_jδ`; `exists_cluster_ratio_bound` supplies `hclose` at
`e = Kδ` together with the two nondegeneracies; `exists_member_expansion_of_roots`
sharpens `O(δ)` to `O(δ^2)` at *some* direction; and
`clusterAlpha_eq_of_mixed_scale` identifies that direction with `α_j`, which is
what `κ = 1/(8ρ)` is chosen for — it halves the separation `clusterAlpha_sep`
gives, leaving the other half for `Cδ`.

The principal branch enters as two hypotheses because it is not this module's
object: `htpr` says `t_p(δ)` is a root of the same pencil member, which is how
`ftBranchZ` is defined, and `hpexp` is its own `O(δ^2)` expansion, which is
`exists_principal_expansion_of_branch`.

**Differs from the paper's route.**  `Forgacs2017RationalDenominator` Prop. 3
Case 2 asserts the `ρ` members and their directions from the displayed
asymptotics: the expansion is written down and the `ρ` branches are read off it.
Here they are *produced* — Rouché against the model
`q(x_1)(t-x_1)^ρ + z_0x_1^rδ^ρ` puts a root in each of `ρ` disjoint disks, and
the direction is then matched to the one the ratio step names.  The match
consumes only `ω^ρ = -1`, through the crude gap `‖α‖/(4ρ)` of `clusterAlpha_sep`
rather than the sharp `2x_1`, so no trigonometry enters.  What the change buys is
that the count is a theorem rather than a reading: an asymptotic displaying `ρ`
branches does not by itself say that `ρ` roots exist at each small `δ`. -/
theorem exists_cluster_member_expansion_family {x₁ : ℝ} (hx : 0 < x₁) {ρ r : ℕ}
    (hρ : 2 ≤ ρ) {Q q : ℂ[X]} (hQ : Q = (X - C ((x₁ : ℝ) : ℂ)) ^ ρ * q)
    (hqx : q.eval ((x₁ : ℝ) : ℂ) ≠ 0)
    {z : ℝ → ℂ} {z₀ : ℂ} (hz₀ : z₀ ≠ 0)
    (hzrate : Filter.Tendsto (fun δ : ℝ => z δ / (δ : ℂ) ^ ρ)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds z₀))
    (hmodel : q.eval ((x₁ : ℝ) : ℂ) * clusterAlpha x₁ ρ 1 ^ ρ
      + z₀ * ((x₁ : ℝ) : ℂ) ^ r = 0)
    {tp : ℝ → ℂ} {jp : ℕ} {Cp ε₁ : ℝ} (hCp : 0 ≤ Cp) (hε₁ : 0 < ε₁)
    (htpr : ∀ δ : ℝ, 0 < δ → δ ≤ ε₁ → (ftDen Q r (z δ)).eval (tp δ) = 0)
    (hpexp : ∀ δ : ℝ, 0 < δ → δ ≤ ε₁ →
      ‖tp δ - (((x₁ : ℝ) : ℂ) + clusterAlpha x₁ ρ jp * (δ : ℂ))‖ ≤ Cp * δ ^ 2) :
    ∃ Cm ε : ℝ, 0 ≤ Cm ∧ 0 < ε ∧ ∀ δ : ℝ, 0 < δ → δ < ε → ∀ j : ℕ,
      ∃ t : ℂ, (ftDen Q r (z δ)).eval t = 0 ∧
        ‖t - (((x₁ : ℝ) : ℂ) + clusterAlpha x₁ ρ j * (δ : ℂ))‖ ≤ Cm * δ ^ 2 := by
  have hρ1 : 1 ≤ ρ := by omega
  have hρR : (1 : ℝ) ≤ (ρ : ℝ) := by exact_mod_cast hρ1
  have hρ0 : (0 : ℝ) < (ρ : ℝ) := by linarith only [hρR]
  have hρne : ((ρ : ℝ)) ≠ 0 := ne_of_gt hρ0
  set S : ℝ := x₁ / Real.sin (Real.pi / ρ) with hS
  have hS0 : 0 < S := by rw [hS]; exact div_pos hx (sin_pi_div_pos hρ)
  set κ : ℝ := 1 / (8 * (ρ : ℝ)) with hκdef
  have hκ : 0 < κ := by rw [hκdef]; exact div_pos one_pos (by linarith only [hρ0])
  have hκ4 : κ * (4 * (ρ : ℝ)) ≤ 1 := by
    rw [hκdef, div_mul_eq_mul_div, one_mul, div_le_one (by linarith only [hρ0])]
    linarith only [hρ0]
  obtain ⟨εf, hεf, hfam⟩ :=
    exists_cluster_member_family hx hρ hQ hqx hz₀ hzrate hmodel hκ hκ4
  set A : ℝ := (1 + κ) * S + Cp with hA
  have hA0 : 0 ≤ A := by
    rw [hA]
    have : 0 ≤ (1 + κ) * S := mul_nonneg (by linarith only [hκ]) hS0.le
    linarith only [this, hCp]
  obtain ⟨K, hK0, ε₂, hε₂, hratio⟩ := exists_cluster_ratio_bound hx hqx (r := r) hA0
  set Cm : ℝ := 5 * K * (S + Cp) + Cp with hCm
  have hCm0 : 0 ≤ Cm := by
    rw [hCm]
    have : 0 ≤ 5 * K * (S + Cp) :=
      mul_nonneg (by linarith only [hK0]) (by linarith only [hS0, hCp])
    linarith only [this, hCp]
  refine ⟨Cm, min (min εf ε₂) (min (min 1 ε₁)
      (min (S / (8 * (ρ : ℝ) * (Cm + 1))) (S / (Cp + 1)))), hCm0, ?_, ?_⟩
  · refine lt_min (lt_min hεf hε₂) (lt_min (lt_min one_pos hε₁) (lt_min ?_ ?_))
    · refine div_pos hS0 ?_
      have h := mul_pos hρ0 (show (0 : ℝ) < Cm + 1 by linarith only [hCm0])
      linarith only [h]
    · exact div_pos hS0 (by linarith only [hCp])
  intro δ hδ hδε j
  have hδ1' : δ < εf :=
    lt_of_lt_of_le (lt_of_lt_of_le hδε (min_le_left _ _)) (min_le_left _ _)
  have hδ2' : δ < ε₂ :=
    lt_of_lt_of_le (lt_of_lt_of_le hδε (min_le_left _ _)) (min_le_right _ _)
  have hδ1 : δ ≤ 1 :=
    le_of_lt (lt_of_lt_of_le (lt_of_lt_of_le hδε (min_le_right _ _))
      (le_trans (min_le_left _ _) (min_le_left _ _)))
  have hδe₁ : δ ≤ ε₁ :=
    le_of_lt (lt_of_lt_of_le (lt_of_lt_of_le hδε (min_le_right _ _))
      (le_trans (min_le_left _ _) (min_le_right _ _)))
  have hδg : δ < S / (8 * (ρ : ℝ) * (Cm + 1)) :=
    lt_of_lt_of_le (lt_of_lt_of_le hδε (min_le_right _ _))
      (le_trans (min_le_right _ _) (min_le_left _ _))
  have hδp : δ < S / (Cp + 1) :=
    lt_of_lt_of_le (lt_of_lt_of_le hδε (min_le_right _ _))
      (le_trans (min_le_right _ _) (min_le_right _ _))
  have hCmδ : Cm * δ * (8 * (ρ : ℝ)) ≤ S := by
    have hp : (0 : ℝ) < 8 * (ρ : ℝ) * (Cm + 1) := by
      have h := mul_pos hρ0 (show (0 : ℝ) < Cm + 1 by linarith only [hCm0])
      linarith only [h]
    have h2 : δ * (8 * (ρ : ℝ) * (Cm + 1)) < S := (lt_div_iff₀ hp).mp hδg
    nlinarith only [h2, hδ, hρ0, hCm0, mul_pos hρ0 hδ]
  have hCpδ : Cp * δ < S := by
    have h2 : δ * (Cp + 1) < S := (lt_div_iff₀ (by linarith only [hCp])).mp hδp
    nlinarith only [h2, hδ, hCp]
  -- the member from the Rouché step
  obtain ⟨t, ht1, ht2⟩ := hfam δ hδ hδ1' j
  rw [← hS] at ht1
  have hαj : ‖clusterAlpha x₁ ρ j * (δ : ℂ)‖ = S * δ := by
    rw [norm_mul, norm_clusterAlpha hx hρ j, ← hS, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hδ]
  have hαp : ‖clusterAlpha x₁ ρ jp * (δ : ℂ)‖ = S * δ := by
    rw [norm_mul, norm_clusterAlpha hx hρ jp, ← hS, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hδ]
  have htx : ‖t - ((x₁ : ℝ) : ℂ)‖ ≤ A * δ := by
    have hsplit : t - ((x₁ : ℝ) : ℂ)
        = (t - (((x₁ : ℝ) : ℂ) + clusterAlpha x₁ ρ j * (δ : ℂ)))
          + clusterAlpha x₁ ρ j * (δ : ℂ) := by ring
    have hle := le_trans (le_of_eq (congrArg norm hsplit)) (norm_add_le _ _)
    rw [hαj] at hle
    rw [hA]
    nlinarith only [hle, ht1, hCp, hδ]
  have htpx : ‖tp δ - ((x₁ : ℝ) : ℂ)‖ ≤ A * δ := by
    have hsplit : tp δ - ((x₁ : ℝ) : ℂ)
        = (tp δ - (((x₁ : ℝ) : ℂ) + clusterAlpha x₁ ρ jp * (δ : ℂ)))
          + clusterAlpha x₁ ρ jp * (δ : ℂ) := by ring
    have hle := le_trans (le_of_eq (congrArg norm hsplit)) (norm_add_le _ _)
    rw [hαp] at hle
    have hp := hpexp δ hδ hδe₁
    have hq1 : Cp * δ ^ 2 ≤ Cp * δ := by
      have hprod := mul_nonneg (mul_nonneg hCp hδ.le)
        (show (0 : ℝ) ≤ 1 - δ by linarith only [hδ1])
      linarith only [hprod]
    have hq2 : (0 : ℝ) ≤ κ * S * δ :=
      mul_nonneg (mul_nonneg hκ.le hS0.le) hδ.le
    rw [hA]
    linarith only [hle, hp, hq1, hq2]
  obtain ⟨hqt, htp0, hKδ, hclose⟩ := hratio δ hδ hδ2' t (tp δ) htx htpx
  -- the principal branch point is not `x_1`
  have hne : tp δ ≠ ((x₁ : ℝ) : ℂ) := by
    intro h0
    have hp := hpexp δ hδ hδe₁
    rw [h0] at hp
    have hrw : ((x₁ : ℝ) : ℂ) - (((x₁ : ℝ) : ℂ) + clusterAlpha x₁ ρ jp * (δ : ℂ))
        = -(clusterAlpha x₁ ρ jp * (δ : ℂ)) := by ring
    rw [hrw, norm_neg, hαp] at hp
    nlinarith only [hp, hCpδ, hδ]
  obtain ⟨ω, hω⟩ := exists_member_expansion_of_roots hx hρ hQ ht2 (htpr δ hδ hδe₁) hne
    hqt htp0 hδ hδ1 hK0 hCp hKδ (le_refl (K * δ)) hclose (hpexp δ hδ hδe₁)
  rw [← hS, ← hCm] at hω
  have hgapcond : κ * S + Cm * δ ≤ S / (4 * (ρ : ℝ)) := by
    have hκS : κ * S = S / (8 * (ρ : ℝ)) := by rw [hκdef]; ring
    have hhalf : S / (8 * (ρ : ℝ)) + S / (8 * (ρ : ℝ)) = S / (4 * (ρ : ℝ)) := by
      field
    have hle : Cm * δ ≤ S / (8 * (ρ : ℝ)) := by
      rw [le_div_iff₀ (by linarith only [hρ0])]
      linarith only [hCmδ]
    rw [hκS, ← hhalf]
    linarith only [hle]
  have heq := clusterAlpha_eq_of_mixed_scale hx hρ hδ hgapcond ht1 hω
  refine ⟨t, ht2, ?_⟩
  rw [heq]
  exact hω

/-- **`thm:weighted-dominance`'s `hexp₀`, at the pencil.**  The `ρ` cluster
members, normalized by the branch radius, expand as

`ζ_i(δ) = 1 + [(cos(π/ρ) - ω_{i})/sin(π/ρ)]δ + O(δ^2)`,

with the members produced rather than assumed: `g` is the family
`exists_cluster_member_expansion_family` supplies, one root per direction, and
`cluster_normalized_expansion` divides by `τ`.

The four inputs about the principal branch — that `t_p(δ)` is a root, its own
`O(δ^2)` expansion, `τ = ‖t_p‖`, and `τ ≥ x_1/2` — stay hypotheses because
`ftTau` and `ftBranchZ` are not this module's objects; the first two are
`FTGeometryAssembly.ftDen_eval_ftPrincipal_ftBranchZ` and
`exists_principal_expansion_of_branch`. -/
theorem exists_cluster_normalized_expansion_of_pencil {x₁ : ℝ} (hx : 0 < x₁)
    {ρ r : ℕ} (hρ : 2 ≤ ρ) {Q q : ℂ[X]} (hQ : Q = (X - C ((x₁ : ℝ) : ℂ)) ^ ρ * q)
    (hqx : q.eval ((x₁ : ℝ) : ℂ) ≠ 0)
    {z : ℝ → ℂ} {z₀ : ℂ} (hz₀ : z₀ ≠ 0)
    (hzrate : Filter.Tendsto (fun δ : ℝ => z δ / (δ : ℂ) ^ ρ)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds z₀))
    (hmodel : q.eval ((x₁ : ℝ) : ℂ) * clusterAlpha x₁ ρ 1 ^ ρ
      + z₀ * ((x₁ : ℝ) : ℂ) ^ r = 0)
    {tp : ℝ → ℂ} {τ : ℝ → ℝ} {jp : ℕ} {Cp ε₁ : ℝ} (hCp : 0 ≤ Cp) (hε₁ : 0 < ε₁)
    (hjp : (clusterOmega ρ jp).re = Real.cos (Real.pi / ρ))
    (htpr : ∀ δ : ℝ, 0 < δ → δ ≤ ε₁ → (ftDen Q r (z δ)).eval (tp δ) = 0)
    (hpexp : ∀ δ : ℝ, 0 < δ → δ ≤ ε₁ →
      ‖tp δ - (((x₁ : ℝ) : ℂ) + clusterAlpha x₁ ρ jp * (δ : ℂ))‖ ≤ Cp * δ ^ 2)
    (hτeq : ∀ δ : ℝ, 0 < δ → δ ≤ ε₁ → τ δ = ‖tp δ‖)
    (hwin : ∀ δ : ℝ, 0 < δ → δ ≤ ε₁ → x₁ / 2 ≤ τ δ) :
    ∃ C₀ ε : ℝ, 0 ≤ C₀ ∧ 0 < ε ∧ ∃ g : ℝ → Fin ρ → ℂ,
      (∀ i : Fin ρ, ∀ δ : ℝ, 0 < δ → δ ≤ ε → (ftDen Q r (z δ)).eval (g δ i) = 0) ∧
      (∀ i : Fin ρ, ∀ δ : ℝ, 0 < δ → δ ≤ ε →
        ‖g δ i / ((τ δ : ℝ) : ℂ)
          - (1 + ((((Real.cos (Real.pi / ρ) : ℝ) : ℂ)
              - clusterOmega ρ ((i : ℕ) + 1))
            / ((Real.sin (Real.pi / ρ) : ℝ) : ℂ)) * (δ : ℂ))‖ ≤ C₀ * δ ^ 2) := by
  obtain ⟨Cm, ε₀, hCm0, hε₀, hmain⟩ :=
    exists_cluster_member_expansion_family hx hρ hQ hqx hz₀ hzrate hmodel hCp hε₁
      htpr hpexp
  have hmain' : ∀ δ : ℝ, ∀ j : ℕ, ∃ t : ℂ, 0 < δ → δ < ε₀ →
      (ftDen Q r (z δ)).eval t = 0 ∧
        ‖t - (((x₁ : ℝ) : ℂ) + clusterAlpha x₁ ρ j * (δ : ℂ))‖ ≤ Cm * δ ^ 2 := by
    intro δ j
    by_cases h : 0 < δ ∧ δ < ε₀
    · obtain ⟨t, h1, h2⟩ := hmain δ h.1 h.2 j
      exact ⟨t, fun _ _ => ⟨h1, h2⟩⟩
    · exact ⟨0, fun hd he => absurd ⟨hd, he⟩ h⟩
  choose g hg using hmain'
  have hs := sin_pi_div_pos hρ
  set ε : ℝ := min (min (min (ε₀ / 2) 1) ε₁) (Real.sin (Real.pi / ρ) / 2) with hεdef
  have hε : 0 < ε :=
    lt_min (lt_min (lt_min (by linarith only [hε₀]) one_pos) hε₁) (by linarith only [hs])
  have hε1 : ε ≤ 1 :=
    le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_right _ _))
  have hεe₁ : ε ≤ ε₁ := le_trans (min_le_left _ _) (min_le_right _ _)
  have hεs : ε ≤ Real.sin (Real.pi / ρ) / 2 := min_le_right _ _
  have hεlt : ∀ δ : ℝ, δ ≤ ε → δ < ε₀ := by
    intro δ hδ
    have h1 : δ ≤ ε₀ / 2 :=
      le_trans hδ (le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_left _ _)))
    linarith only [h1, hε₀]
  set Cb : ℝ := max Cm Cp with hCb
  have hCb0 : 0 ≤ Cb := le_trans hCm0 (le_max_left _ _)
  have hgexp : ∀ i : Fin ρ, ∀ δ : ℝ, 0 < δ → δ ≤ ε →
      ‖(fun δ' (i' : Fin ρ) => g δ' ((i' : ℕ) + 1)) δ i
        - (((x₁ : ℝ) : ℂ) + clusterAlpha x₁ ρ ((i : ℕ) + 1) * (δ : ℂ))‖ ≤ Cb * δ ^ 2 := by
    intro i δ hδ hδε
    refine le_trans ((hg δ ((i : ℕ) + 1) hδ (hεlt δ hδε)).2) ?_
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg δ)
  have hpexp' : ∀ δ : ℝ, 0 < δ → δ ≤ ε →
      ‖tp δ - (((x₁ : ℝ) : ℂ) + clusterAlpha x₁ ρ jp * (δ : ℂ))‖ ≤ Cb * δ ^ 2 := by
    intro δ hδ hδε
    refine le_trans (hpexp δ hδ (le_trans hδε hεe₁)) ?_
    exact mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg δ)
  obtain ⟨C₀, hC₀, hnorm⟩ :=
    cluster_normalized_expansion (n₀ := ρ) (idx₀ := fun i : Fin ρ => (i : ℕ) + 1)
      (g₀ := fun δ' (i' : Fin ρ) => g δ' ((i' : ℕ) + 1)) (τ := τ) (tp := tp)
      hx hρ hCb0 hε hε1 hεs hjp
      (fun δ hδ hδε => hτeq δ hδ (le_trans hδε hεe₁))
      (fun δ hδ hδε => hwin δ hδ (le_trans hδε hεe₁))
      hgexp hpexp'
  refine ⟨C₀, ε, hC₀, hε, fun δ (i : Fin ρ) => g δ ((i : ℕ) + 1), ?_, hnorm⟩
  intro i δ hδ hδε
  exact (hg δ ((i : ℕ) + 1) hδ (hεlt δ hδε)).1

end ForgacsTran
