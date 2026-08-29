/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib
import ForgacsTran.EndpointRegularity
import ForgacsTran.ClusterDirections
import ForgacsTran.FTBranchAngle
import ForgacsTran.FTBranchFunction
import ForgacsTran.PencilIndex

/-!
# The endpoint chart

`EndpointRegularity` derives everything `lem:principal-endpoint-regularity` asserts
*from* the branch's one-sided derivative at the endpoint, which it takes as the
hypothesis `hγ : HasDerivWithinAt γ γ_e (Set.Ici 0) 0`.  Nothing in the tree
produces that hypothesis.  This module is the first step of producing it.

The manuscript's route factors `Q(t) + z_et^r = (t - t_e)^kG(t)` at the endpoint
and takes a `k`-th root of the nonvanishing factor.  `exists_endpoint_chart`
does exactly that, and the result is sharper than an expansion: in the chart
`w(t) = (t - t_e)Λ(t)` the fiber map is a **perfect `k`-th power with no
remainder**,

  `g(t) - z_e = w(t)^k`,

with `w` analytic, `w(t_e) = 0` and `w'(t_e) ≠ 0`.  Since `z` is real on the
branch, `w^k` is real there, so `w` runs along one of `k` straight rays through
the origin — which is what turns the `k` local branches into `k` real parameters.

## What is here and what is not

Proved: the analytic `k`-th root, and the chart.  Not yet: the local inverse
`t = ψ(w)` — `AnalyticAt.analyticAt_localInverse` supplies it and `w'(t_e) ≠ 0`
is its hypothesis, which is why that clause is in the conclusion above — the
passage from the ray parameter to the manuscript's angular one, and the
identification of the resulting branch with `ftTau`.

**The identification is only free at `k = 2`.**  There the two local branches are
a conjugate pair and exactly one lies in the upper half plane, so it is the
principal one with nothing to check.  From `k = 3` the cluster has `k` members of
equal modulus to leading order and the principal pair is singled out by a
second-order condition — the vanishing of the linear coefficient of `|ζ_j|` — so
that case needs an argument this module does not contain.  `k = 2` is exactly the
range `ρ ≤ 2` of the smallest zero's multiplicity.

## Containment

`exists_endpoint_chart` relates `w`, `Q`, `t_e` and `z_e`.  Since `w` is bound in
the conclusion, the question is whether a hypothesis already supplies the chart,
and none does: the hypotheses are `1 ≤ k`, `t_e ≠ 0`, `G(t_e) ≠ 0` and the
factorization `hfac`, and `hfac` mentions `Q` and `t_e` but asserts a
factorization of `ftDen` rather than a `k`-th root of anything.  The root is
built by `exists_analytic_kth_root`.  The hypotheses are jointly satisfiable —
`EndpointRegularity.exists_endpointFactor` produces `G` and `hfac` from any
nonzero pencil, and `EndpointRegularity.rootMultiplicity_pos_of_branch` gives
`1 ≤ k` at a branch through `t_e`.

## The endpoint datum, and the value it takes

`DominanceFTBranch.weighted_dominance_of_branch_any_multiplicity_at` carries the whole
endpoint group — `hte₀`, `hγe₀`, `hγ0₀`, `hγd₀`, `hk₀`, `hrootev₀` — with **no**
guard on the lower cluster, while its `hρ`, `hcB₀`, `hcQ₀`, `hBp₀` and `hEp₀` all
carry `0 < n₀ →`.  So the datum is owed at every multiplicity of the smallest
zero, `ρ = 1` included, and the two ends of that range are not alike:

| | endpoint limit `t_e` | datum `γ_e` |
|---|---|---|
| `ρ = 1` | the first positive critical point of `g`, strictly inside `(x_1, x_2)` | `i·t_e` |
| `ρ ≥ 2` | the smallest zero `x_1` itself | `clusterAlpha x_1 ρ 0` |

Both are the single formula `γ_e = t_e(i - \cot(π/k))` at the collision
multiplicity `k = max(ρ, 2)`, which is `2` in the first row and `ρ` in the
second.  `clusterAlpha` is the `ρ ≥ 2` half of it and **degenerates silently at
`ρ = 1`** — `clusterAlpha_one_eq_zero`.

## Main statements

* `exists_analytic_kth_root` — a nonvanishing analytic function has an analytic
  `k`-th root near the point, itself nonvanishing.
* `exists_endpoint_chart` — the chart, with `g - z_e = w^k` exact.
* `clusterAlpha_one_eq_zero` — the `ρ = 1` degeneracy, as a fact rather than a
  reading.
* `clusterAlpha_im` — `\Im α_0 = x_1`, which is why `hγe₀` is free once the datum
  exists.
* `ftAngle_eq_arg` — the branch angle as the argument of the chord, which is what
  makes the blow-up `τ = x_1 - sθ` a limit of `arg` rather than of a cotangent.
* `ftAngle_eq_pi_add_arctan` — the same angle for a zero the circle has not
  reached, in the one chart that stays continuous where its chord is heading.
* `arg_blowup_root` — `\arg(-x_1\cot(π/ρ) + ix_1) = π - π/ρ`, the root of the
  blown-up angle-sum equation.
* `tendsto_expI_slope`, `tendsto_blowup_chord_div` — the chord from `x_1` to the
  branch point is `θ(-s + ix_1) + o(θ)`.
* `tendsto_ftAngle_blowup_cluster`, `tendsto_ftAngle_blowup_far` — the two kinds
  of angle in the blow-up, each through the chart that stays continuous where its
  chord is heading.
* `tendsto_ftAngleSum_blowup`, `sum_ite_cluster_eq` — the whole angle sum, and its
  limit in closed form.
* `arg_neg_add_im`, `strictMono_arg_neg_add_im` — the cluster angle in closed
  form, `π/2 + \arctan(s/x_1)`, and its monotonicity in the blow-up variable.
* `tendsto_ftTau_blowup` — `(x_1 - τ(θ))/θ → x_1\cot(π/ρ)`, by an
  intermediate-value squeeze against that monotone family.
* `clusterAlpha_eq_blowup` — the blow-up limit is the tree's own `clusterAlpha` at
  the principal index.
* `exists_endpoint_local_inverse` — the chart inverted: `g(ψ(v)) - z_e = v^k`
  exactly, with `ψ` analytic, `ψ'(0) ≠ 0` and injective near `0`.
* `exists_cluster_branch` — the same at the lower endpoint of a repeated smallest
  zero, where `z_e = 0`: `ψ(v)` is a zero of the pencil at spectral parameter
  `v^ρ`.
* `cluster_member_root`, `cluster_member_ne` — the `ρ` rotates `ψ(ζv)`, `ζ^ρ = 1`,
  are zeros at that one spectral parameter and are distinct off `v = 0`.
* `clusterDir`, `clusterDir_pow`, `clusterDir_inj` — the chart directions, the
  `ρ`-th roots of **unity**, which are a different family from
  `Cluster.clusterOmega` (whose `ρ`-th power is `-1`).
* `clusterAlpha_mul_clusterDir` — the orbit identity `α_0·ζ_j = α_j`, which pins
  the enumeration index without matching an asymptotic by hand.
* `cluster_covers` — every nearby zero is one of the `ρ` members, so the cluster is
  complete rather than a sub-family.
* `pow_eq_pow_of_tendsto`, `exists_clusterDir_of_pow`, `exists_principal_index` —
  which member the principal pair is, settled by an identity on the `ρ`-th powers
  rather than by a pigeonhole on the index.
* `clusterSlope_inj`, `exists_index_of_cover`, `eventually_eq_of_cover` — the same
  by slopes: the `ρ` slopes are distinct, one of them is the covered point's, and
  the covering then forces that index eventually.

## Implementation notes

Sorry-free.

## References

* `../shields-2026-forgacs-tran-numerators.tex`, «Forgács--Tran geometry and
  endpoint separation» — `lem:principal-endpoint-regularity`,
  `eq:principal-finite-endpoint-regularity`, `eq:z-endpoint-order`.
* `Forgacs2017RationalDenominator`, Proposition 3.

## Tags

endpoint, Puiseux, analytic root, principal branch
-/

namespace ForgacsTran

open Complex Filter Topology Polynomial

/-- **An analytic `k`-th root of a nonvanishing analytic function.**  On a
neighbourhood of a point where `f` does not vanish, `f` has an analytic `k`-th
root, itself nonvanishing there. -/
theorem exists_analytic_kth_root {f : ℂ → ℂ} {t₀ : ℂ} {k : ℕ} (hk : 1 ≤ k)
    (hf : AnalyticAt ℂ f t₀) (h0 : f t₀ ≠ 0) :
    ∃ Λ : ℂ → ℂ, AnalyticAt ℂ Λ t₀ ∧ Λ t₀ ≠ 0 ∧ ∀ᶠ t in 𝓝 t₀, Λ t ^ k = f t := by
  obtain ⟨μ, hμ⟩ := IsAlgClosed.exists_pow_nat_eq (f t₀) (n := k) (by omega)
  have hμ0 : μ ≠ 0 := by
    intro h
    rw [h, zero_pow (by omega : k ≠ 0)] at hμ
    exact h0 hμ.symm
  have hk0 : ((k : ℂ)) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  set h : ℂ → ℂ := fun t => f t / f t₀ with hhdef
  have hh0 : h t₀ = 1 := by rw [hhdef]; field_simp
  have hha : AnalyticAt ℂ h t₀ := hf.div_const
  have hslit : h t₀ ∈ Complex.slitPlane := by
    rw [hh0]
    exact Complex.mem_slitPlane_iff.2 (Or.inl (by norm_num))
  refine ⟨fun t => μ * Complex.exp (((k : ℂ))⁻¹ * Complex.log (h t)), ?_, ?_, ?_⟩
  · exact analyticAt_const.mul (analyticAt_const.mul (hha.clog hslit)).cexp'
  · change μ * Complex.exp (((k : ℂ))⁻¹ * Complex.log (h t₀)) ≠ 0
    rw [hh0, Complex.log_one, mul_zero, Complex.exp_zero, mul_one]
    exact hμ0
  · filter_upwards [hha.continuousAt.eventually_ne (by rw [hh0]; exact one_ne_zero)] with t ht
    rw [mul_pow, ← Complex.exp_nat_mul, ← mul_assoc, mul_inv_cancel₀ hk0, one_mul,
      Complex.exp_log ht, hμ, hhdef]
    field_simp


/-- **The endpoint chart.**  At a finite endpoint, where `Q + z_eX^r` has a zero of
order `k` at `t_e ≠ 0`, the fiber map is a perfect `k`-th power in a chart:
`g(t) - z_e = w(t)^k` **exactly**, with `w` analytic, `w(t_e) = 0` and
`w'(t_e) ≠ 0`.

This is `EndpointRegularity.endpoint_root_identity` with the nonvanishing
cofactor absorbed into an analytic `k`-th root, which is what turns the `k`
local branches into the `k` straight rays `w^k = z - z_e` of a real parameter. -/
theorem exists_endpoint_chart {Q : Polynomial ℂ} {r k : ℕ} {ze te : ℂ} {G : Polynomial ℂ}
    (hk : 1 ≤ k) (hte : te ≠ 0) (hG : G.eval te ≠ 0)
    (hfac : ftDen Q r ze = (X - C te) ^ k * G) :
    ∃ w : ℂ → ℂ, AnalyticAt ℂ w te ∧ w te = 0 ∧ deriv w te ≠ 0 ∧
      ∀ᶠ t in 𝓝 te, w t ^ k = -(Q.eval t) / t ^ r - ze := by
  have hfa : AnalyticAt ℂ (fun t => -(G.eval t) / t ^ r) te :=
    ((analyticAt_eval G te).neg).div (analyticAt_id.pow r) (pow_ne_zero _ hte)
  have hf0 : (fun t => -(G.eval t) / t ^ r) te ≠ 0 :=
    div_ne_zero (neg_ne_zero.2 hG) (pow_ne_zero _ hte)
  obtain ⟨Λ, hΛa, hΛ0, hΛk⟩ := exists_analytic_kth_root hk hfa hf0
  refine ⟨fun t => (t - te) * Λ t, (analyticAt_id.sub analyticAt_const).mul hΛa, by simp, ?_, ?_⟩
  · have hlin : HasDerivAt (fun t : ℂ => t - te) 1 te := by
      simpa using (hasDerivAt_id te).sub_const te
    have hd : HasDerivAt (fun t : ℂ => (t - te) * Λ t)
        (1 * Λ te + (te - te) * deriv Λ te) te :=
      hlin.mul (hΛa.differentiableAt.hasDerivAt)
    rw [hd.deriv]
    simpa using hΛ0
  · filter_upwards [hΛk, eventually_ne_nhds hte] with t hΛt ht0
    have hpow : ((t - te) * Λ t) ^ k = (t - te) ^ k * (-(G.eval t) / t ^ r) := by
      rw [mul_pow, hΛt]
    have hid : Q.eval t + ze * t ^ r = (t - te) ^ k * G.eval t := by
      have h := congrArg (Polynomial.eval t) hfac
      rw [ftDen_eval] at h
      simpa using h
    have htr : t ^ r ≠ 0 := pow_ne_zero _ ht0
    have hrhs : -(Q.eval t) / t ^ r - ze = (-(Q.eval t) - ze * t ^ r) / t ^ r := by
      field_simp
    rw [hpow, hrhs, ← mul_div_assoc]
    congr 1
    linear_combination hid


/-! ### The endpoint datum, and where its closed form degenerates -/

/-! **`clusterAlpha` is zero at `ρ = 1`, and silently**
(`Cluster.clusterAlpha_one_eq_zero`).  Its definition divides by `\sin(π/ρ)`, which
is `\sin π = 0` there, so the whole expression evaluates to `0` rather than
failing.  Anything that reads the endpoint datum `γ_e` off `clusterAlpha`
uniformly in `ρ` therefore compiles at `ρ = 1` and supplies `0`, against a
consumer whose `hγe₀` asks for `γ_e ≠ 0`.

The endpoint collision has multiplicity `k = max(ρ, 2)`, not `ρ`, and it is `k`
that the datum is built from: at `ρ = 1` the two members of the principal pair
still collide, so `k = 2` and `γ_e = i·t_e`, which is nonzero.  `clusterAlpha`
agrees with that only from `ρ = 2` on. -/
/-- **`\Im α_j = x_1` at the principal index.**  This is why `hγe₀` is free once
the datum exists at `2 ≤ ρ`: the endpoint limit is a positive real, so the branch
leaves it in a direction that is never real.  `Cluster.clusterAlpha_ne_zero` is
the same conclusion through the modulus. -/
theorem clusterAlpha_im {x₁ : ℝ} {ρ : ℕ} (hρ : 2 ≤ ρ) : (clusterAlpha x₁ ρ 0).im = x₁ := by
  have hπ := Real.pi_pos
  have hρR : (2 : ℝ) ≤ (ρ : ℝ) := by exact_mod_cast hρ
  have hρ0 : (0 : ℝ) < (ρ : ℝ) := by linarith
  have hs : Real.sin (Real.pi / (ρ : ℝ)) ≠ 0 := by
    refine ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by positivity) ?_)
    rw [div_lt_iff₀ hρ0]
    nlinarith
  have hang : clusterAngle ρ 0 = -(Real.pi / (ρ : ℝ)) := by
    rw [clusterAngle]
    push_cast
    ring
  simp only [clusterAlpha, clusterOmega, hang, Complex.div_im, Complex.mul_im,
    Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, Complex.normSq_ofReal,
    Real.cos_neg, Real.sin_neg]
  field


/-! ### The branch angle as a complex argument -/

/-- **`θ_k(τ,θ) = \arg(τe^{iθ} - a)`.**  `ftAngle` is defined through `ftArccot` of
a cotangent, which is what makes its monotonicity and its endpoint limits
computable; this identifies it with the argument of the chord, which is what makes
a *blow-up* computable, since a limit of `ftAngle` along `τ = x_1 - sθ` becomes a
limit of `arg` of a converging complex number. -/
theorem ftAngle_eq_arg {a τ θ : ℝ} (hτ : 0 < τ) (hθ : θ ∈ Set.Ioo 0 Real.pi) :
    ftAngle a τ θ
      = Complex.arg (((τ : ℝ) : ℂ) * Complex.exp (((θ : ℝ) : ℂ) * Complex.I) - ((a : ℝ) : ℂ)) := by
  set w : ℂ := ((τ : ℝ) : ℂ) * Complex.exp (((θ : ℝ) : ℂ) * Complex.I) - ((a : ℝ) : ℂ) with hw
  have hre : w.re = τ * Real.cos θ - a := by
    simp [hw, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
  have him : w.im = τ * Real.sin θ := by
    simp [hw, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
  have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
  have himpos : 0 < w.im := by rw [him]; positivity
  have hw0 : w ≠ 0 := by
    intro h
    rw [h] at himpos
    simp at himpos
  have hn : 0 < ‖w‖ := norm_pos_iff.2 hw0
  have hargmem : Complex.arg w ∈ Set.Ioo 0 Real.pi := by
    have hsin : Real.sin (Complex.arg w) = w.im / ‖w‖ := Complex.sin_arg w
    have hpos : 0 < Real.sin (Complex.arg w) := by rw [hsin]; positivity
    have h1 := Complex.neg_pi_lt_arg w
    have h2 := Complex.arg_le_pi w
    refine ⟨?_, ?_⟩
    · by_contra hcon
      push Not at hcon
      have hneg : 0 ≤ Real.sin (-(Complex.arg w)) :=
        Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
      rw [Real.sin_neg] at hneg
      linarith
    · rcases lt_or_eq_of_le h2 with hlt | heq
      · exact hlt
      · rw [heq, Real.sin_pi] at hpos
        linarith
  refine (ftArccot_eq_of_cos_eq hargmem ?_).symm
  rw [Complex.cos_arg hw0, Complex.sin_arg, hre, him]
  have hτ0 : τ ≠ 0 := ne_of_gt hτ
  have hs0 : Real.sin θ ≠ 0 := ne_of_gt hs
  field_simp


/-- **The far zeros' chart.**  For a zero the branch circle has not reached,
`τ\cos θ < a`, the angle is `π + \arctan` of a quantity that vanishes with `θ`.
Unlike `ftAngle_eq_arg` this stays continuous at the limit, which is what the
non-cluster zeros need: their chords tend to the *negative* reals, where `arg`
itself is not. -/
theorem ftAngle_eq_pi_add_arctan {a τ θ : ℝ} (hτ : 0 < τ) (hθ : θ ∈ Set.Ioo 0 Real.pi)
    (hlt : τ * Real.cos θ < a) :
    ftAngle a τ θ
      = Real.pi + Real.arctan (τ * Real.sin θ / (τ * Real.cos θ - a)) := by
  have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
  have hX : Real.cos θ / Real.sin θ - a / (τ * Real.sin θ)
      = (τ * Real.cos θ - a) / (τ * Real.sin θ) := by
    field_simp
  have hXneg : (τ * Real.cos θ - a) / (τ * Real.sin θ) < 0 :=
    div_neg_of_neg_of_pos (by linarith) (by positivity)
  have hinv : ((τ * Real.cos θ - a) / (τ * Real.sin θ))⁻¹
      = τ * Real.sin θ / (τ * Real.cos θ - a) := by
    rw [inv_div]
  have hkey := Real.arctan_inv_of_neg hXneg
  rw [hinv] at hkey
  rw [ftAngle, hX, ftArccot]
  linarith

/-- **The limit equation's root.**  `\arg(-x_1\cot(π/ρ) + ix_1) = π - π/ρ`, so
`s = x_1\cot(π/ρ)` is what the blown-up angle sum
`ρ\arg(-s + ix_1) + (n-ρ)π = (n-1)π` selects. -/
theorem arg_blowup_root {x₁ : ℝ} (hx₁ : 0 < x₁) {ρ : ℕ} (hρ : 2 ≤ ρ) :
    Complex.arg (((-(x₁ * (Real.cos (Real.pi / ρ) / Real.sin (Real.pi / ρ))) : ℝ) : ℂ)
        + ((x₁ : ℝ) : ℂ) * Complex.I)
      = Real.pi - Real.pi / ρ := by
  have hπ := Real.pi_pos
  have hρR : (2 : ℝ) ≤ (ρ : ℝ) := by exact_mod_cast hρ
  have hρ0 : (0 : ℝ) < (ρ : ℝ) := by linarith
  have hpos : (0 : ℝ) < Real.pi / (ρ : ℝ) := by positivity
  have hlt : Real.pi / (ρ : ℝ) < Real.pi := by
    rw [div_lt_iff₀ hρ0]; nlinarith
  have hs : 0 < Real.sin (Real.pi / (ρ : ℝ)) :=
    Real.sin_pos_of_pos_of_lt_pi hpos hlt
  have hsne : Real.sin (Real.pi / (ρ : ℝ)) ≠ 0 := ne_of_gt hs
  have hscale : (0 : ℝ) < x₁ / Real.sin (Real.pi / (ρ : ℝ)) := by positivity
  have hpt : ((-(x₁ * (Real.cos (Real.pi / ρ) / Real.sin (Real.pi / ρ))) : ℝ) : ℂ)
      + ((x₁ : ℝ) : ℂ) * Complex.I
      = ((x₁ / Real.sin (Real.pi / (ρ : ℝ)) : ℝ) : ℂ)
        * ((Real.cos (Real.pi - Real.pi / (ρ : ℝ)) : ℂ)
            + (Real.sin (Real.pi - Real.pi / (ρ : ℝ)) : ℂ) * Complex.I) := by
    rw [Real.cos_pi_sub, Real.sin_pi_sub]
    have hsC : ((Real.sin (Real.pi / (ρ : ℝ)) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hsne
    push_cast [-Complex.ofReal_cos, -Complex.ofReal_sin]
    field_simp
  rw [hpt, Complex.arg_real_mul _ hscale, Complex.ofReal_cos, Complex.ofReal_sin]
  refine Complex.arg_cos_add_sin_mul_I ?_
  rw [Set.mem_Ioc]
  constructor <;> linarith


/-! ### The blown-up angle at a cluster zero -/

/-- `(e^{iθ} - 1)/θ → i`: the derivative of the arc at the endpoint, as a slope. -/
theorem tendsto_expI_slope :
    Filter.Tendsto (fun θ : ℝ => (Complex.exp ((θ : ℂ) * Complex.I) - 1) / (θ : ℂ))
      (𝓝[≠] (0 : ℝ)) (𝓝 Complex.I) := by
  have hlin : HasDerivAt (fun θ : ℝ => ((θ : ℝ) : ℂ) * Complex.I) Complex.I 0 := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).mul_const Complex.I
  have hexp : HasDerivAt (fun θ : ℝ => Complex.exp (((θ : ℝ) : ℂ) * Complex.I)) Complex.I 0 := by
    have h := (Complex.hasDerivAt_exp (((0 : ℝ) : ℂ) * Complex.I)).scomp 0 hlin
    simpa [Function.comp_def] using h
  refine (hasDerivAt_iff_tendsto_slope.1 hexp).congr fun x => ?_
  simp only [slope, vsub_eq_sub, sub_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero,
    Complex.real_smul, Complex.ofReal_inv]
  rw [div_eq_inv_mul]

/-- **The blown-up chord at a cluster zero.**  Along `τ = x_1 - sθ`, the chord from
`x_1` to the branch point is `θ(-s + ix_1) + o(θ)`. -/
theorem tendsto_blowup_chord_div (x₁ s : ℝ) :
    Filter.Tendsto
      (fun θ : ℝ => (((x₁ - s * θ : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)
        - ((x₁ : ℝ) : ℂ)) / (θ : ℂ))
      (𝓝[≠] (0 : ℝ)) (𝓝 (((-s : ℝ) : ℂ) + ((x₁ : ℝ) : ℂ) * Complex.I)) := by
  have hexpc : Filter.Tendsto (fun θ : ℝ => Complex.exp ((θ : ℂ) * Complex.I))
      (𝓝[≠] (0 : ℝ)) (𝓝 1) := by
    have hc : Continuous fun θ : ℝ => Complex.exp (((θ : ℝ) : ℂ) * Complex.I) :=
      Complex.continuous_exp.comp (Complex.continuous_ofReal.mul continuous_const)
    have h : Filter.Tendsto (fun θ : ℝ => Complex.exp (((θ : ℝ) : ℂ) * Complex.I))
        (𝓝[≠] (0 : ℝ)) (𝓝 (Complex.exp ((((0 : ℝ)) : ℂ) * Complex.I))) :=
      (hc.tendsto 0).mono_left nhdsWithin_le_nhds
    simpa using h
  have hmain := ((tendsto_expI_slope.const_mul ((x₁ : ℝ) : ℂ)).sub
    (hexpc.const_mul ((s : ℝ) : ℂ)))
  have hval : ((x₁ : ℝ) : ℂ) * Complex.I - ((s : ℝ) : ℂ) * 1
      = ((-s : ℝ) : ℂ) + ((x₁ : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [hval] at hmain
  refine hmain.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with θ hθ
  have hθC : ((θ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hθ
  field_simp
  push_cast
  ring


/-- **The cluster angle, blown up.**  Along `τ = x_1 - sθ` the angle subtended at
the repeated zero `x_1` tends to `\arg(-s + ix_1)` — a genuine limit rather than
a degeneracy, which is what makes the blown-up angle-sum equation regular at
`θ = 0`.  `ftAngle_eq_arg` is what puts it in reach: the cotangent the definition
uses blows up here while the argument converges. -/
theorem tendsto_ftAngle_blowup_cluster {x₁ s : ℝ} (hx₁ : 0 < x₁) :
    Filter.Tendsto (fun θ : ℝ => ftAngle x₁ (x₁ - s * θ) θ) (𝓝[>] (0 : ℝ))
      (𝓝 (Complex.arg (((-s : ℝ) : ℂ) + ((x₁ : ℝ) : ℂ) * Complex.I))) := by
  have hπ := Real.pi_pos
  have hsub : 𝓝[>] (0 : ℝ) ≤ 𝓝[≠] (0 : ℝ) := nhdsWithin_mono _ fun x hx => ne_of_gt hx
  have him : (((-s : ℝ) : ℂ) + ((x₁ : ℝ) : ℂ) * Complex.I).im = x₁ := by simp
  have hslit : (((-s : ℝ) : ℂ) + ((x₁ : ℝ) : ℂ) * Complex.I) ∈ Complex.slitPlane :=
    Complex.mem_slitPlane_iff.2 (Or.inr (by rw [him]; exact ne_of_gt hx₁))
  have hcont : ContinuousAt Complex.arg (((-s : ℝ) : ℂ) + ((x₁ : ℝ) : ℂ) * Complex.I) :=
    Complex.continuousAt_arg hslit
  have hcomp := hcont.tendsto.comp ((tendsto_blowup_chord_div x₁ s).mono_left hsub)
  refine hcomp.congr' ?_
  -- the branch radius stays positive, and the angle stays inside `(0, π)`
  have hτ : ∀ᶠ θ in 𝓝[>] (0 : ℝ), 0 < x₁ - s * θ := by
    have hc : Filter.Tendsto (fun θ : ℝ => x₁ - s * θ) (𝓝 (0 : ℝ)) (𝓝 x₁) := by
      have hcont' : Continuous fun θ : ℝ => x₁ - s * θ := by fun_prop
      simpa using hcont'.tendsto (0 : ℝ)
    exact (hc.eventually (eventually_gt_nhds hx₁)).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hτ, Ioo_mem_nhdsGT hπ] with θ hθ hτθ hθπ
  have hθ0 : (0 : ℝ) < θ := hθ
  have hθC : ((θ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hθ0
  set X : ℂ := ((x₁ - s * θ : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) - ((x₁ : ℝ) : ℂ)
    with hXdef
  have hsplit : X = ((θ : ℝ) : ℂ) * (X / ((θ : ℝ) : ℂ)) := by field_simp
  rw [Function.comp_apply, ftAngle_eq_arg hτθ ⟨hθ0, hθπ.2⟩, ← hXdef]
  conv_rhs => rw [hsplit]
  exact (Complex.arg_real_mul _ hθ0).symm


/-- **The far angle, blown up.**  A zero the branch circle never reaches
contributes a full `π` in the limit.  The chord runs into the negative reals, so
this is where `ftAngle_eq_arg` would be useless and
`ftAngle_eq_pi_add_arctan` is what carries it. -/
theorem tendsto_ftAngle_blowup_far {x₁ s a : ℝ} (hx₁ : 0 < x₁) (ha : x₁ < a) :
    Filter.Tendsto (fun θ : ℝ => ftAngle a (x₁ - s * θ) θ) (𝓝[>] (0 : ℝ)) (𝓝 Real.pi) := by
  have hπ := Real.pi_pos
  have hane : x₁ - a ≠ 0 := sub_ne_zero.2 (ne_of_lt ha)
  have hq : Filter.Tendsto (fun θ : ℝ =>
      (x₁ - s * θ) * Real.sin θ / ((x₁ - s * θ) * Real.cos θ - a)) (𝓝 (0 : ℝ)) (𝓝 0) := by
    have hc : ContinuousAt (fun θ : ℝ =>
        (x₁ - s * θ) * Real.sin θ / ((x₁ - s * θ) * Real.cos θ - a)) 0 := by
      refine ContinuousAt.div (by fun_prop) (by fun_prop) ?_
      simpa using hane
    simpa using hc.tendsto
  have harc : Filter.Tendsto (fun θ : ℝ =>
      Real.pi + Real.arctan ((x₁ - s * θ) * Real.sin θ / ((x₁ - s * θ) * Real.cos θ - a)))
      (𝓝 (0 : ℝ)) (𝓝 Real.pi) := by
    have h := (Real.continuous_arctan.tendsto (0 : ℝ)).comp hq
    rw [Real.arctan_zero] at h
    simpa [Function.comp_def] using (h.const_add Real.pi)
  refine (harc.mono_left nhdsWithin_le_nhds).congr' ?_
  -- the eventual conditions the chart needs
  have hτ : ∀ᶠ θ in 𝓝[>] (0 : ℝ), 0 < x₁ - s * θ := by
    have hc : Continuous fun θ : ℝ => x₁ - s * θ := by fun_prop
    exact (((by simpa using hc.tendsto (0 : ℝ)) :
      Filter.Tendsto (fun θ : ℝ => x₁ - s * θ) (𝓝 (0 : ℝ)) (𝓝 x₁)).eventually
      (eventually_gt_nhds hx₁)).filter_mono nhdsWithin_le_nhds
  have hcos : ∀ᶠ θ in 𝓝[>] (0 : ℝ), (x₁ - s * θ) * Real.cos θ < a := by
    have hc : Continuous fun θ : ℝ => (x₁ - s * θ) * Real.cos θ := by fun_prop
    exact (((by simpa using hc.tendsto (0 : ℝ)) :
      Filter.Tendsto (fun θ : ℝ => (x₁ - s * θ) * Real.cos θ) (𝓝 (0 : ℝ)) (𝓝 x₁)).eventually
      (eventually_lt_nhds ha)).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hτ, hcos, Ioo_mem_nhdsGT hπ] with θ hθ hτθ hcθ hθπ
  exact (ftAngle_eq_pi_add_arctan hτθ ⟨hθ, hθπ.2⟩ hcθ).symm


/-- **The blown-up angle sum.**  Along `τ = x_1 - sθ` every angle converges: the
`ρ` copies of the smallest zero to `\arg(-s + ix_1)`, every other zero to `π`.
The sum is therefore regular at `θ = 0`, which the unblown-up equation is not —
there `∑_kθ_k - rθ - (n-1)π` vanishes identically in `τ` and carries no
information. -/
theorem tendsto_ftAngleSum_blowup {n : ℕ} {a : Fin n → ℝ} {x₁ s : ℝ} (hx₁ : 0 < x₁)
    (hmin : ∀ k, x₁ ≤ a k) :
    Filter.Tendsto (fun θ : ℝ => ftAngleSum a (x₁ - s * θ) θ) (𝓝[>] (0 : ℝ))
      (𝓝 (∑ k, if a k = x₁
            then Complex.arg (((-s : ℝ) : ℂ) + ((x₁ : ℝ) : ℂ) * Complex.I)
            else Real.pi)) := by
  simp only [ftAngleSum]
  refine tendsto_finsetSum _ fun k _ => ?_
  by_cases hk : a k = x₁
  · rw [if_pos hk, hk]
    exact tendsto_ftAngle_blowup_cluster hx₁
  · rw [if_neg hk]
    exact tendsto_ftAngle_blowup_far hx₁ (lt_of_le_of_ne (hmin k) (Ne.symm hk))

/-- The limit in closed form: `ρ` copies of the cluster angle and `n - ρ` of `π`,
with `ρ` the multiplicity of the smallest zero. -/
theorem sum_ite_cluster_eq {n : ℕ} (a : Fin n → ℝ) (x₁ A : ℝ) :
    (∑ k, if a k = x₁ then A else Real.pi)
      = ((Finset.univ.filter fun k => a k = x₁).card : ℝ) * A
        + ((n : ℝ) - ((Finset.univ.filter fun k => a k = x₁).card : ℝ)) * Real.pi := by
  classical
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]
  have hsum : ((Finset.univ.filter fun k => a k = x₁).card
      + (Finset.univ.filter fun k => ¬ (a k = x₁)).card) = n := by
    simpa using Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin n))) (p := fun k => a k = x₁)
  have hcast : ((Finset.univ.filter fun k => ¬ (a k = x₁)).card : ℝ)
      = (n : ℝ) - ((Finset.univ.filter fun k => a k = x₁).card : ℝ) := by
    have h := congrArg (Nat.cast : ℕ → ℝ) hsum
    push_cast at h
    linarith
  rw [hcast]


/-! ### The blown-up equation is strictly monotone in the blow-up variable -/

/-- **The cluster angle in closed form.**  `\arg(-s + ix_1) = π/2 + \arctan(s/x_1)`
for `x_1 > 0`.  Everything the squeeze needs about the blown-up equation follows:
it is strictly increasing in `s`, and `arg_blowup_root` locates its value. -/
theorem arg_neg_add_im {x₁ : ℝ} (hx₁ : 0 < x₁) (s : ℝ) :
    Complex.arg (((-s : ℝ) : ℂ) + ((x₁ : ℝ) : ℂ) * Complex.I)
      = Real.pi / 2 + Real.arctan (s / x₁) := by
  have hπ := Real.pi_pos
  set u : ℝ := s / x₁ with hu
  have hxu : x₁ * u = s := by rw [hu]; field_simp
  set t : ℝ := Real.arctan u with ht
  have htmem : t ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := Real.arctan_mem_Ioo u
  have hroot : (0 : ℝ) < Real.sqrt (1 + u ^ 2) := Real.sqrt_pos.2 (by positivity)
  set R : ℝ := x₁ * Real.sqrt (1 + u ^ 2) with hR
  have hR0 : 0 < R := by rw [hR]; positivity
  have hcos : Real.cos (Real.pi / 2 + t) = -Real.sin t := by
    rw [Real.cos_add, Real.cos_pi_div_two, Real.sin_pi_div_two]; ring
  have hsin : Real.sin (Real.pi / 2 + t) = Real.cos t := by
    rw [Real.sin_add, Real.cos_pi_div_two, Real.sin_pi_div_two]; ring
  have hpt : ((-s : ℝ) : ℂ) + ((x₁ : ℝ) : ℂ) * Complex.I
      = ((R : ℝ) : ℂ) * ((Real.cos (Real.pi / 2 + t) : ℂ)
          + (Real.sin (Real.pi / 2 + t) : ℂ) * Complex.I) := by
    rw [hcos, hsin, ht, Real.sin_arctan, Real.cos_arctan, hR, ← hxu]
    push_cast [-Complex.ofReal_cos, -Complex.ofReal_sin]
    have hrC : ((Real.sqrt (1 + u ^ 2) : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast ne_of_gt hroot
    field_simp
  rw [hpt, Complex.arg_real_mul _ hR0, Complex.ofReal_cos, Complex.ofReal_sin]
  exact Complex.arg_cos_add_sin_mul_I ⟨by linarith [htmem.1], by linarith [htmem.2]⟩

/-- The blown-up cluster angle is strictly increasing in `s`. -/
theorem strictMono_arg_neg_add_im {x₁ : ℝ} (hx₁ : 0 < x₁) :
    StrictMono fun s : ℝ => Complex.arg (((-s : ℝ) : ℂ) + ((x₁ : ℝ) : ℂ) * Complex.I) := by
  intro s₁ s₂ h
  dsimp only
  rw [arg_neg_add_im hx₁, arg_neg_add_im hx₁]
  have hdiv : s₁ / x₁ < s₂ / x₁ := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_lt_mul_of_pos_right h (inv_pos.2 hx₁)
  linarith [Real.arctan_strictMono hdiv]


/-! ### The branch radius in the blow-up -/

/-- **The blown-up branch radius converges.**  `(x_1 - τ(θ))/θ → x_1\cot(π/ρ)`.

**Differs from the paper's route.**  The manuscript reads the endpoint expansion
off `Forgacs2017RationalDenominator` Prop. 3's cluster expansion, which is an
asymptotic statement about the `ρ` roots.  Here nothing is expanded: the blow-up
`τ = x_1 - sθ` makes the angle-sum equation regular at `θ = 0`, its limit is
strictly increasing in `s` by `strictMono_arg_neg_add_im`, and the value is
pinned by `arg_blowup_root`.  The convergence is then an intermediate-value
squeeze against a monotone family — no implicit function theorem, and no
expansion whose remainder has to be controlled. -/
theorem tendsto_ftTau_blowup {n r ρ : ℕ} {a : Fin n → ℝ} {x₁ : ℝ}
    (hn : 0 < n) (ha : ∀ k, 0 < a k) (hr : 1 ≤ r) (hnr : 2 ≤ n ∨ 2 ≤ r)
    (hx₁ : 0 < x₁) (hmin : ∀ k, x₁ ≤ a k)
    (hcard : (Finset.univ.filter fun k => a k = x₁).card = ρ) (hρ : 2 ≤ ρ) :
    Filter.Tendsto (fun θ : ℝ => (x₁ - ftTau a r (n - 1) θ) / θ) (𝓝[>] (0 : ℝ))
      (𝓝 (x₁ * (Real.cos (Real.pi / ρ) / Real.sin (Real.pi / ρ)))) := by
  classical
  have hπ := Real.pi_pos
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hρR : (2 : ℝ) ≤ (ρ : ℝ) := by exact_mod_cast hρ
  set A : ℝ → ℝ := fun σ => Complex.arg (((-σ : ℝ) : ℂ) + ((x₁ : ℝ) : ℂ) * Complex.I) with hAdef
  have hAmono : StrictMono A := strictMono_arg_neg_add_im hx₁
  set s₀ : ℝ := x₁ * (Real.cos (Real.pi / ρ) / Real.sin (Real.pi / ρ)) with hs₀
  have hA0 : A s₀ = Real.pi - Real.pi / ρ := arg_blowup_root hx₁ hρ
  have hncast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := cast_pred_eq_sub_one (by omega)
  -- the branch equation, on the arc
  have hbeq : ∀ᶠ θ in 𝓝[>] (0 : ℝ),
      ftAngleSum a (ftTau a r (n - 1) θ) θ = r * θ + ((n : ℝ) - 1) * Real.pi
        ∧ 0 < ftTau a r (n - 1) θ ∧ θ ∈ Set.Ioo (0 : ℝ) Real.pi := by
    filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < Real.pi / r by positivity)] with θ hθ
    have hb := ftBranchAt_of_arc_principal hn ha hr hnr hθ
    refine ⟨?_, ftTau_pos hb, ftArc_subset hr hθ⟩
    rw [ftAngleSum_ftTau hb, hncast]
  -- the blown-up equation, at a fixed `σ`
  have hlim : ∀ σ : ℝ, Filter.Tendsto
      (fun θ : ℝ => ftAngleSum a (x₁ - σ * θ) θ - (r * θ + ((n : ℝ) - 1) * Real.pi))
      (𝓝[>] (0 : ℝ))
      (𝓝 ((ρ : ℝ) * A σ + ((n : ℝ) - ρ) * Real.pi - ((n : ℝ) - 1) * Real.pi)) := by
    intro σ
    have h1 := tendsto_ftAngleSum_blowup (s := σ) hx₁ hmin
    rw [sum_ite_cluster_eq a x₁ (A σ), hcard] at h1
    have h2 : Filter.Tendsto (fun θ : ℝ => (r : ℝ) * θ + ((n : ℝ) - 1) * Real.pi)
        (𝓝[>] (0 : ℝ)) (𝓝 (((n : ℝ) - 1) * Real.pi)) := by
      have hc : Continuous fun θ : ℝ => (r : ℝ) * θ + ((n : ℝ) - 1) * Real.pi := by fun_prop
      exact ((by simpa using hc.tendsto (0 : ℝ)) :
        Filter.Tendsto (fun θ : ℝ => (r : ℝ) * θ + ((n : ℝ) - 1) * Real.pi)
          (𝓝 (0 : ℝ)) (𝓝 (((n : ℝ) - 1) * Real.pi))).mono_left nhdsWithin_le_nhds
    exact h1.sub h2
  -- the limit value is zero exactly at `s₀`
  have hzero : (ρ : ℝ) * A s₀ + ((n : ℝ) - ρ) * Real.pi - ((n : ℝ) - 1) * Real.pi = 0 := by
    rw [hA0]
    field
  refine tendsto_order.2 ⟨fun b hb => ?_, fun c hc => ?_⟩
  · -- `b < s₀`: the blown-up equation is negative at `b`, so the branch sits above it
    have hneg : (ρ : ℝ) * A b + ((n : ℝ) - ρ) * Real.pi - ((n : ℝ) - 1) * Real.pi < 0 := by
      have := hAmono hb
      nlinarith
    filter_upwards [hbeq, (hlim b).eventually (eventually_lt_nhds hneg),
      self_mem_nhdsWithin,
      (((by simpa using (by fun_prop : Continuous fun θ : ℝ => x₁ - b * θ).tendsto (0:ℝ)) :
        Filter.Tendsto (fun θ : ℝ => x₁ - b * θ) (𝓝 (0:ℝ)) (𝓝 x₁)).eventually
        (eventually_gt_nhds hx₁)).filter_mono nhdsWithin_le_nhds]
      with θ ⟨heq, hTpos, hθπ⟩ hlt hθ0 hbpos
    have hθ : (0 : ℝ) < θ := hθ0
    have hcmp : ftAngleSum a (x₁ - b * θ) θ < ftAngleSum a (ftTau a r (n - 1) θ) θ := by
      rw [heq]; linarith
    have hTlt : ftTau a r (n - 1) θ < x₁ - b * θ := by
      by_contra hcon
      push Not at hcon
      exact absurd (ftAngleSum_le_of_le hn ha hθπ hbpos hcon) (not_le.2 hcmp)
    rw [lt_div_iff₀ hθ]
    linarith
  · -- `s₀ < c`: symmetric
    have hposv : 0 < (ρ : ℝ) * A c + ((n : ℝ) - ρ) * Real.pi - ((n : ℝ) - 1) * Real.pi := by
      have := hAmono hc
      nlinarith
    filter_upwards [hbeq, (hlim c).eventually (eventually_gt_nhds hposv),
      self_mem_nhdsWithin,
      (((by simpa using (by fun_prop : Continuous fun θ : ℝ => x₁ - c * θ).tendsto (0:ℝ)) :
        Filter.Tendsto (fun θ : ℝ => x₁ - c * θ) (𝓝 (0:ℝ)) (𝓝 x₁)).eventually
        (eventually_gt_nhds hx₁)).filter_mono nhdsWithin_le_nhds]
      with θ ⟨heq, hTpos, hθπ⟩ hgt hθ0 hcpos
    have hθ : (0 : ℝ) < θ := hθ0
    have hcmp : ftAngleSum a (ftTau a r (n - 1) θ) θ < ftAngleSum a (x₁ - c * θ) θ := by
      rw [heq]; linarith
    have hTgt : x₁ - c * θ < ftTau a r (n - 1) θ := by
      by_contra hcon
      push Not at hcon
      exact absurd (ftAngleSum_le_of_le hn ha hθπ hTpos hcon) (not_le.2 hcmp)
    rw [div_lt_iff₀ hθ]
    linarith


/-! ### The endpoint datum -/

/-- `α_0 = -x_1\cot(π/ρ) + ix_1`: the cluster direction at the principal index is
exactly the blow-up limit, real part the radius' slope and imaginary part `x_1`. -/
theorem clusterAlpha_eq_blowup {x₁ : ℝ} {ρ : ℕ} (hρ : 2 ≤ ρ) :
    clusterAlpha x₁ ρ 0
      = ((-(x₁ * (Real.cos (Real.pi / ρ) / Real.sin (Real.pi / ρ))) : ℝ) : ℂ)
        + ((x₁ : ℝ) : ℂ) * Complex.I := by
  have hπ := Real.pi_pos
  have hρR : (2 : ℝ) ≤ (ρ : ℝ) := by exact_mod_cast hρ
  have hρ0 : (0 : ℝ) < (ρ : ℝ) := by linarith
  have hpos : (0 : ℝ) < Real.pi / (ρ : ℝ) := by positivity
  have hlt : Real.pi / (ρ : ℝ) < Real.pi := by rw [div_lt_iff₀ hρ0]; nlinarith
  have hs : Real.sin (Real.pi / (ρ : ℝ)) ≠ 0 :=
    ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hpos hlt)
  have hsC : ((Real.sin (Real.pi / (ρ : ℝ)) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs
  have hang : clusterAngle ρ 0 = -(Real.pi / (ρ : ℝ)) := by
    rw [clusterAngle]; push_cast; ring
  have homega : clusterOmega ρ 0
      = ((Real.cos (Real.pi / (ρ : ℝ)) : ℝ) : ℂ)
        - ((Real.sin (Real.pi / (ρ : ℝ)) : ℝ) : ℂ) * Complex.I := by
    rw [clusterOmega, hang]
    refine Complex.ext ?_ ?_
    · rw [Complex.exp_ofReal_mul_I_re, Real.cos_neg]
      simp [-Complex.ofReal_cos, -Complex.ofReal_sin]
    · rw [Complex.exp_ofReal_mul_I_im, Real.sin_neg]
      simp [-Complex.ofReal_cos, -Complex.ofReal_sin]
  rw [clusterAlpha, homega]
  push_cast [-Complex.ofReal_cos, -Complex.ofReal_sin]
  field


/-! ### The chart inverted -/

/-- **The endpoint cluster, parameterized.**  Inverting `exists_endpoint_chart`
gives an analytic `ψ` with `ψ(0) = t_e`, `ψ'(0) ≠ 0` and

  `g(ψ(v)) - z_e = v^k`   **exactly**

on a neighbourhood of `0`.  So the `k` denominator zeros at a spectral parameter
`z` near `z_e` are `ψ(ω v)` over the `k`-th roots `ω` of unity, `v^k = z - z_e`,
and each is analytic in `v` with nonzero derivative.  This is the object the
lower-endpoint cluster and the `ρ = 1` endpoint datum both run on: the first takes
`k = ρ` and the `k` directions, the second takes `k = 2` and the ray. -/
theorem exists_endpoint_local_inverse {Q : Polynomial ℂ} {r k : ℕ} {ze te : ℂ}
    {G : Polynomial ℂ} (hk : 1 ≤ k) (hte : te ≠ 0) (hG : G.eval te ≠ 0)
    (hfac : ftDen Q r ze = (X - C te) ^ k * G) :
    ∃ (ψ w : ℂ → ℂ) (γe : ℂ), AnalyticAt ℂ ψ 0 ∧ ψ 0 = te ∧ γe ≠ 0
      ∧ HasDerivAt ψ γe 0
      ∧ (∃ U ∈ 𝓝 (0 : ℂ), Set.InjOn ψ U)
      ∧ (∀ᶠ t in 𝓝 te, ψ (w t) = t)
      ∧ (∀ᶠ t in 𝓝 te, w t ^ k = -(Q.eval t) / t ^ r - ze)
      ∧ (∀ᶠ v in 𝓝 (0 : ℂ), -(Q.eval (ψ v)) / (ψ v) ^ r - ze = v ^ k) := by
  obtain ⟨w, hwa, hw0, hwd, hwk⟩ := exists_endpoint_chart hk hte hG hfac
  have hsd : HasStrictDerivAt w (deriv w te) te := hwa.hasStrictDerivAt
  set ψ : ℂ → ℂ := hsd.localInverse w (deriv w te) te hwd with hψdef
  have hleft : ∀ᶠ t in 𝓝 te, ψ (w t) = t := hsd.eventually_left_inverse hwd
  have hright : ∀ᶠ v in 𝓝 (w te), w (ψ v) = v := hsd.eventually_right_inverse hwd
  have hψ0 : ψ 0 = te := by
    have h := hleft.self_of_nhds
    rwa [hw0] at h
  have hψsd : HasStrictDerivAt ψ (deriv w te)⁻¹ (w te) := hsd.to_localInverse hwd
  rw [hw0] at hψsd hright
  refine ⟨ψ, w, (deriv w te)⁻¹, ?_, hψ0, inv_ne_zero hwd, hψsd.hasDerivAt, ?_,
    hleft, hwk, ?_⟩
  · have h := hwa.analyticAt_localInverse hwd
    rwa [hw0] at h
  · obtain ⟨U, hU, hUsub⟩ := Filter.eventually_iff_exists_mem.1 hright
    exact ⟨U, hU, fun v₁ h₁ v₂ h₂ hv => by rw [← hUsub v₁ h₁, ← hUsub v₂ h₂, hv]⟩
  · have hcont : Filter.Tendsto ψ (𝓝 (0 : ℂ)) (𝓝 te) := by
      have h : Filter.Tendsto ψ (𝓝 (0 : ℂ)) (𝓝 (ψ 0)) := hψsd.hasDerivAt.continuousAt
      rwa [hψ0] at h
    filter_upwards [hcont.eventually hwk, hright] with v hv hwv
    rw [← hv, hwv]


/-! ### The lower cluster as branches of the pencil -/

/-- **The cluster branch.**  At the lower endpoint of a repeated smallest zero the
spectral parameter's endpoint value is `z_e = 0`, because `x_1` is a zero of `Q`.
The chart then says: `ψ(v)` is a zero of the pencil at spectral parameter `v^ρ`,
analytically in `v`, with `ψ(0) = x_1` and `ψ'(0) ≠ 0`.

The `ρ` cluster members at one spectral parameter are `ψ(ω v)` over the `ρ`-th
roots of unity `ω`, all at the same `z = v^ρ`; `hinj` is what makes them distinct,
and it is the local inverse's own injectivity rather than a separate count. -/
theorem exists_cluster_branch {Q : Polynomial ℂ} {r ρ : ℕ} {te : ℂ} {G : Polynomial ℂ}
    (hρ : 1 ≤ ρ) (hte : te ≠ 0) (hG : G.eval te ≠ 0)
    (hfac : ftDen Q r 0 = (X - C te) ^ ρ * G) :
    ∃ (ψ : ℂ → ℂ) (γe : ℂ), AnalyticAt ℂ ψ 0 ∧ ψ 0 = te ∧ γe ≠ 0
      ∧ HasDerivAt ψ γe 0
      ∧ (∃ U ∈ 𝓝 (0 : ℂ), Set.InjOn ψ U)
      ∧ (∀ᶠ v in 𝓝 (0 : ℂ), (ftDen Q r (v ^ ρ)).eval (ψ v) = 0) := by
  obtain ⟨ψ, w, γe, hψa, hψ0, hγe, hψd, hinj, -, -, hchart⟩ :=
    exists_endpoint_local_inverse hρ hte hG hfac
  refine ⟨ψ, γe, hψa, hψ0, hγe, hψd, hinj, ?_⟩
  have hcont : Filter.Tendsto ψ (𝓝 (0 : ℂ)) (𝓝 te) := by
    have h : Filter.Tendsto ψ (𝓝 (0 : ℂ)) (𝓝 (ψ 0)) := hψd.continuousAt
    rwa [hψ0] at h
  filter_upwards [hchart, hcont.eventually (eventually_ne_nhds hte)] with v hv hne
  have hpow : (ψ v) ^ r ≠ 0 := pow_ne_zero _ hne
  rw [ftDen_eval]
  rw [sub_zero] at hv
  field_simp at hv
  linear_combination -hv


/-- **Every rotate of the cluster branch is a zero at the same spectral
parameter.**  `(ωv)^ρ = v^ρ` when `ω^ρ = 1`, so the `ρ` rotates sit on one fibre. -/
theorem cluster_member_root {Q : Polynomial ℂ} {r ρ : ℕ} {ψ : ℂ → ℂ}
    (hroot : ∀ᶠ v in 𝓝 (0 : ℂ), (ftDen Q r (v ^ ρ)).eval (ψ v) = 0)
    {ω : ℂ} (hω : ω ^ ρ = 1) :
    ∀ᶠ v in 𝓝 (0 : ℂ), (ftDen Q r (v ^ ρ)).eval (ψ (ω * v)) = 0 := by
  have hmul : Filter.Tendsto (fun v : ℂ => ω * v) (𝓝 (0 : ℂ)) (𝓝 (0 : ℂ)) := by
    have hc : Continuous fun v : ℂ => ω * v := by fun_prop
    simpa using hc.tendsto (0 : ℂ)
  filter_upwards [hmul.eventually hroot] with v hv
  rwa [mul_pow, hω, one_mul] at hv

/-- **The rotates are distinct.**  Off `v = 0` the `ρ` points `ωv` are distinct, and
the local inverse is injective, so the cluster really has `ρ` members rather than
fewer.  This is `hginj₀`'s content, and it is the chart's injectivity rather than a
root count. -/
theorem cluster_member_ne {ψ : ℂ → ℂ} {U : Set ℂ} (hinj : Set.InjOn ψ U)
    {ω₁ ω₂ v : ℂ} (h₁ : ω₁ * v ∈ U) (h₂ : ω₂ * v ∈ U) (hv : v ≠ 0) (hω : ω₁ ≠ ω₂) :
    ψ (ω₁ * v) ≠ ψ (ω₂ * v) := by
  intro h
  exact hω (mul_right_cancel₀ hv (hinj h₁ h₂ h))


/-- **The chart covers every nearby zero.**  A zero of the pencil close to `t_e`
at spectral parameter `z_e + v^k` is one of the `k` members `ψ(ζ_j v)` — not merely
*some* zero of the pencil is, but *every* nearby one.  This is what makes the
cluster complete rather than a sub-family, and it is what `huniq₀` will consume:
the chart's `w` sends the zero to a `k`-th root of `v^k`, and the left inverse
sends it back. -/
theorem cluster_covers {ψ w : ℂ → ℂ} {Q : Polynomial ℂ} {r k : ℕ} {ze t v : ℂ}
    (hk : k ≠ 0) (hleft : ψ (w t) = t)
    (hwk : w t ^ k = -(Q.eval t) / t ^ r - ze) (hv : v ≠ 0)
    (hz : -(Q.eval t) / t ^ r - ze = v ^ k) :
    ∃ j < k, t = ψ (clusterDir k j * v) := by
  haveI : NeZero k := ⟨hk⟩
  have hpow : (w t / v) ^ k = 1 := by
    rw [div_pow, hwk, hz, div_self (pow_ne_zero _ hv)]
  obtain ⟨j, hj, hje⟩ :=
    (Complex.isPrimitiveRoot_exp k hk).eq_pow_of_pow_eq_one hpow
  refine ⟨j, hj, ?_⟩
  have hwv : w t = clusterDir k j * v := by
    rw [clusterDir, hje]
    field_simp
  rw [← hwv, hleft]


/-! ### Identifying the principal index

Which of the `ρ` members is the principal pair's is settled by an identity, not by
a pigeonhole on the index and not by matching an asymptotic.  Writing `u(δ)` for
the chart coordinate of the principal point, `cluster_covers` gives
`(u(δ)/v(δ))^ρ = 1`, so `(u(δ)/δ)^ρ = (v(δ)/δ)^ρ` for every `δ`; passing to the
limit turns that into `(γ_e/(chart slope))^ρ = L^ρ`, and the quotient is then a
`ρ`-th root of unity by `exists_clusterDir_of_pow`. -/

/-- Two functions whose `ρ`-th powers agree along a filter have limits whose
`ρ`-th powers agree. -/
theorem pow_eq_pow_of_tendsto {ρ : ℕ} {f g : ℝ → ℂ} {A B : ℂ} {l : Filter ℝ} [l.NeBot]
    (hf : Filter.Tendsto f l (𝓝 A)) (hg : Filter.Tendsto g l (𝓝 B))
    (h : ∀ᶠ x in l, (f x) ^ ρ = (g x) ^ ρ) : A ^ ρ = B ^ ρ := by
  refine tendsto_nhds_unique ((hf.pow ρ).congr' h) (hg.pow ρ)

/-- A `ρ`-th root of unity is one of the `ρ` chart directions. -/
theorem exists_clusterDir_of_pow {ρ : ℕ} (hρ : ρ ≠ 0) {κ : ℂ} (h : κ ^ ρ = 1) :
    ∃ j < ρ, clusterDir ρ j = κ := by
  haveI : NeZero ρ := ⟨hρ⟩
  exact (Complex.isPrimitiveRoot_exp ρ hρ).eq_pow_of_pow_eq_one h

/-- **The principal index.**  Given that the principal slope `A` and the chart data
`γ_e`, `L` satisfy `(A/(γ_eL))^ρ = 1`, the principal member is the one at chart
direction `ζ_{j_p}`, and every member's slope is then `A` times a chart direction —
which `clusterAlpha_mul_clusterDir` turns into `clusterAlpha` at a shifted index. -/
theorem exists_principal_index {ρ : ℕ} (hρ : ρ ≠ 0) {γe A : ℂ} {L : ℝ}
    (hγe : γe ≠ 0) (hL : (L : ℂ) ≠ 0) (hpow : (A / (γe * (L : ℂ))) ^ ρ = 1) :
    ∃ j < ρ, γe * (clusterDir ρ j * (L : ℂ)) = A := by
  obtain ⟨j, hj, hje⟩ := exists_clusterDir_of_pow hρ hpow
  refine ⟨j, hj, ?_⟩
  rw [hje]
  field_simp


/-- The `ρ` cluster slopes are distinct, which is what makes the index the point's
slope determines unique. -/
theorem clusterSlope_inj {ρ : ℕ} (hρ : ρ ≠ 0) {γe : ℂ} {L : ℝ} (hγe : γe ≠ 0)
    (hL : ((L : ℝ) : ℂ) ≠ 0) {i j : ℕ} (hi : i < ρ) (hj : j < ρ) (hij : i ≠ j) :
    γe * (clusterDir ρ i * ((L : ℝ) : ℂ)) ≠ γe * (clusterDir ρ j * ((L : ℝ) : ℂ)) := by
  intro h
  exact hij (clusterDir_inj hρ hi hj
    (mul_right_cancel₀ hL (mul_left_cancel₀ hγe h)))

/-- **Some chart direction carries the distinguished point.**  If a point is
covered by the `ρ` members at every small angle, and each member has its own slope
limit, then one of those limits is the point's own.  This is the cheap half of a
pigeonhole: if *no* index matched, each would be excluded eventually, and finitely
many eventuallys intersect to contradict the covering.  The index itself never has
to be shown eventually constant for this. -/
theorem exists_index_of_cover {ψ : ℂ → ℂ} {ρ : ℕ} {te A : ℂ} {S : ℕ → ℂ} {P V : ℝ → ℂ}
    (hcover : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∃ j ∈ Finset.range ρ, P δ = ψ (clusterDir ρ j * V δ))
    (hP : Filter.Tendsto (fun δ : ℝ => (P δ - te) / ((δ : ℝ) : ℂ)) (𝓝[>] (0 : ℝ)) (𝓝 A))
    (hmem : ∀ j : ℕ, Filter.Tendsto
      (fun δ : ℝ => (ψ (clusterDir ρ j * V δ) - te) / ((δ : ℝ) : ℂ))
      (𝓝[>] (0 : ℝ)) (𝓝 (S j))) :
    ∃ j ∈ Finset.range ρ, S j = A := by
  by_contra hcon
  push Not at hcon
  have hne : ∀ j ∈ Finset.range ρ,
      ∀ᶠ δ in 𝓝[>] (0 : ℝ), P δ ≠ ψ (clusterDir ρ j * V δ) := by
    intro j hj
    have hAS : A - S j ≠ 0 := sub_ne_zero.2 fun h => hcon j hj h.symm
    have hd := (hP.sub (hmem j)).eventually_ne hAS
    filter_upwards [hd] with δ hδ h
    exact hδ (by rw [h]; ring)
  have hall := (Filter.eventually_all_finset _).2 hne
  have hfalse : ∀ᶠ δ in 𝓝[>] (0 : ℝ), False := by
    filter_upwards [hcover, hall] with δ hc hn
    obtain ⟨j, hj, hje⟩ := hc
    exact hn j hj hje
  exact (Filter.neBot_iff.1 inferInstance) (Filter.eventually_false_iff_eq_bot.1 hfalse)

/-- **And then the index is eventually constant.**  Once one direction's slope is
the point's own, the others' are not — the slopes are distinct — so every other
index is excluded eventually and the covering forces that one. -/
theorem eventually_eq_of_cover {ψ : ℂ → ℂ} {ρ : ℕ} {te A : ℂ} {S : ℕ → ℂ} {P V : ℝ → ℂ}
    {jp : ℕ} (hjp : jp ∈ Finset.range ρ) (hSjp : S jp = A)
    (hinjS : ∀ i ∈ Finset.range ρ, ∀ j ∈ Finset.range ρ, i ≠ j → S i ≠ S j)
    (hcover : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∃ j ∈ Finset.range ρ, P δ = ψ (clusterDir ρ j * V δ))
    (hP : Filter.Tendsto (fun δ : ℝ => (P δ - te) / ((δ : ℝ) : ℂ)) (𝓝[>] (0 : ℝ)) (𝓝 A))
    (hmem : ∀ j : ℕ, Filter.Tendsto
      (fun δ : ℝ => (ψ (clusterDir ρ j * V δ) - te) / ((δ : ℝ) : ℂ))
      (𝓝[>] (0 : ℝ)) (𝓝 (S j))) :
    ∀ᶠ δ in 𝓝[>] (0 : ℝ), P δ = ψ (clusterDir ρ jp * V δ) := by
  have hne : ∀ j ∈ Finset.range ρ,
      ∀ᶠ δ in 𝓝[>] (0 : ℝ), j ≠ jp → P δ ≠ ψ (clusterDir ρ j * V δ) := by
    intro j hj
    by_cases hjjp : j = jp
    · exact Filter.Eventually.of_forall fun δ h => absurd hjjp h
    · have hAS : A - S j ≠ 0 := by
        rw [← hSjp]
        exact sub_ne_zero.2 (hinjS jp hjp j hj (Ne.symm hjjp))
      have hd := (hP.sub (hmem j)).eventually_ne hAS
      filter_upwards [hd] with δ hδ _ h
      exact hδ (by rw [h]; ring)
  have hall := (Filter.eventually_all_finset _).2 hne
  filter_upwards [hcover, hall] with δ hc hn
  obtain ⟨j, hj, hje⟩ := hc
  by_cases hjjp : j = jp
  · rwa [hjjp] at hje
  · exact absurd hje (hn j hj hjjp)

/-- **The index of a distinguished point, and the identity that follows.**  A point
covered by the `ρ` members and carrying its own slope has exactly one member's
slope, and from then on it *is* that member.  `exists_index_of_cover` supplies the
index and `eventually_eq_of_cover` the identity; the distinctness that makes the
index unique is `clusterSlope_inj`.

Stated against abstract `P` and `A` because both the principal branch and its arc
point are consumed through it, with `A` the slope of each. -/
theorem exists_cluster_index_of_cover {ρ : ℕ} {ψ : ℂ → ℂ} {γe A : ℂ} {L : ℝ} {te : ℂ}
    {V : ℝ → ℂ} {P : ℝ → ℂ}
    (hρ : ρ ≠ 0) (hγe : γe ≠ 0) (hL : ((L : ℝ) : ℂ) ≠ 0)
    (hslope : ∀ j : ℕ, Filter.Tendsto
      (fun δ : ℝ => (ψ (clusterDir ρ j * V δ) - te) / ((δ : ℝ) : ℂ))
      (𝓝[>] (0 : ℝ)) (𝓝 (γe * (clusterDir ρ j * ((L : ℝ) : ℂ)))))
    (hP : Filter.Tendsto (fun δ : ℝ => (P δ - te) / ((δ : ℝ) : ℂ)) (𝓝[>] (0 : ℝ)) (𝓝 A))
    (hcover : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∃ j ∈ Finset.range ρ, P δ = ψ (clusterDir ρ j * V δ)) :
    ∃ jp < ρ, γe * (clusterDir ρ jp * ((L : ℝ) : ℂ)) = A
      ∧ ∀ᶠ δ in 𝓝[>] (0 : ℝ), P δ = ψ (clusterDir ρ jp * V δ) := by
  obtain ⟨jp, hjp, hSjp⟩ := exists_index_of_cover (te := te) (A := A)
    (S := fun j => γe * (clusterDir ρ j * ((L : ℝ) : ℂ))) hcover hP hslope
  refine ⟨jp, Finset.mem_range.1 hjp, hSjp, ?_⟩
  exact eventually_eq_of_cover hjp hSjp
    (fun i hi j hj hij => clusterSlope_inj hρ hγe hL (Finset.mem_range.1 hi)
      (Finset.mem_range.1 hj) hij) hcover hP hslope

end ForgacsTran
