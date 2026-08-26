/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib
import ForgacsTran.BoundAssembly
import ForgacsTran.PhaseDerivativeBound
import ForgacsTran.BranchAmplitude
import ForgacsTran.ViewingAngle

/-!
# The cofactor bound `eq:phase-derivative-bound` needs at an endpoint

`PhaseDerivativeBound.phase_deriv_bound_uniform_in_collar_of_bound` reduces
`eq:phase-derivative-bound` on the collar to a single estimate: a **bound** on
`|Im(V'/V)|` over the punctured collar, where `V` is the nonvanishing cofactor of
`eq:W-endpoint-form`.  It takes that estimate as a hypothesis and says nothing
about where it comes from.  This module produces it.

**A bound, not a limit, and that is the whole point.**  Writing
`γ - t_e = δ·u(δ)`, the surviving term of `Im(W'/W)` is `-m·Im(u'/u)`, and

  `u'(δ) = (γ'(δ)·δ - (γ(δ) - t_e)) / δ²`.

The *limit* of `u'` at the endpoint is not determined by `γ'(0)` and the pencil:
it is second order in `γ`, so naming it means naming `γ''(0)`.  A *bound* does
not.  It follows from `γ'` satisfying a one-sided Lipschitz estimate against its
endpoint value alone, because that makes the numerator above `O(δ²)` against the
`δ²` already in the denominator — and a Lipschitz estimate is a first-order
statement, reachable from a second-derivative bound on the punctured collar with
nothing asked at the endpoint itself.

## Main statements

* `hasDerivAt_endpointCofactor` — `u` is differentiable off the endpoint, with
  the quotient-rule derivative.
* `norm_endpointCofactor_sub_le` — `‖u(δ) - γ'(0)‖ ≤ Lδ/2`, so `u` is off zero
  on a collar whose length the estimate itself names.
* `norm_endpointCofactorDeriv_le` — `‖u'‖ ≤ 3L/2`, the estimate above.
* `exists_bound_im_endpointCofactor_logDeriv` — the two combined:
  `|Im(u'/u)| ≤ 3L/‖γ'(0)‖` on `(0, b']`, which is
  `phase_deriv_bound_uniform_in_collar_of_bound`'s `hbd` at the endpoint.
* `exists_endpoint_phase_deriv_bound_zpow` — that composed, giving
  `eq:phase-derivative-bound` on the collar for `W = δ^p·u(δ)` with `p ≠ 0`.
* `norm_deriv_sub_le_of_norm_deriv2_le` — the Lipschitz binder traded for a
  bound on `γ''` **off** the endpoint plus continuity of `γ'` at it, which is
  what the branch modules carry.
* `exists_endpoint_phase_deriv_bound_of_deriv2` — the two composed, so the
  collar bound owes nothing at the endpoint but a one-sided first derivative.
* `exists_bound_of_continuousOn_of_tendsto` — a bound off the endpoint from a
  one-sided limit at it, and
* `exists_endpoint_phase_deriv_bound_of_deriv2_limit` — the collar bound with
  that folded in, so what is owed carries no constant at all.
* `eventuallyEq_endpointCofactor_of_quotient` — the raw quotient against the
  continuous extension `Amplitude` uses, related on `𝓝[>] 0` and nowhere else.
* `exists_bound_im_logDeriv_endpointCofactor` — the module's own bound restated
  through Mathlib's `logDeriv`, so it composes with the split literally.
* `im_logDeriv_endpoint_factorization`, `abs_im_logDeriv_endpoint_factorization_le`
  — `eq:W-endpoint-form`'s cofactor split into branch, divided difference and
  nonvanishing factor, with only the middle one delicate.
* `polarModulus_eq_norm` — the branch's modulus is `‖W‖`, which is what
  `ftPrincipalAmp` is.
* `exists_threshold_of_bound`, `exists_phase_branch_of_bound` — the bound turned
  into `FTPhaseSupply`'s three clauses about one block, the `|dψ| < M+1` one as a
  threshold on `M`.
* `tendsto_ftGammaDeriv2_of_tendsto` — the one complex hypothesis that remains,
  reduced to the convergence of `τ`, `τ'` and `τ''` at the endpoint, and
* `exists_ft_endpoint_phase_deriv_bound_of_tau_limits` — the collar bound with
  that folded in.
* `exists_tendsto_of_tendsto_deriv`, `exists_tau_limits_of_tendsto_ftTauDeriv2`,
  `exists_ft_endpoint_phase_deriv_bound_of_tau2` — a convergent derivative forces
  its function to converge, so the three limits collapse to `τ''` alone.  That is
  as far as this module reduces the chain.
* `ftAngleDeriv2AngleTau_eq_ftAngleDeriv2TauAngle` — the angle's mixed second
  partials, written two ways in `BranchCurvature`, are one function.
* `exists_endpoint_phase_deriv_bound_of_contDiffOn` — the collar bound from
  one-sided `C²` on the collar alone, which is the landing pad for the analytic
  endpoint chart, and
* `exists_endpoint_phase_deriv_bound_of_comp` — that through the chart's own
  shape, `γ = F ∘ v`, and
* `exists_contDiffAt_local_inverse` — the `v` that shape wants, from a `C²`
  angle map with nonvanishing derivative, and
* `exists_endpoint_phase_deriv_bound_of_chart` — the three composed, so the
  collar bound follows from the endpoint chart alone.
* `contDiffAt_chart_ray` — the chart's own `F`, its real restriction along the
  ray, shifted so the endpoint sits at the origin, and
* `contDiffAt_polarAngle` — the chart's own `Θ`, through `ViewingAngle`'s
  cut-free branch rather than `Complex.arg`.
* `exists_ft_endpoint_phase_deriv_bound` — that at the Forgács–Tran branch, with
  every punctured-collar hypothesis discharged from the tree's own lemmas, so
  what remains is four facts at the endpoint and one of them is new.

## Implementation notes

**Nothing in the tree consumes this module yet, and that is a stage rather than a
defect.**  Every theorem here is a proved input to the first of the three things
`AngularDiscrepancyFT.FTPhaseSupply`'s branch hypothesis still wants — a bound on
`Im(W'/W)` over every zero-free block of the arc — and that hypothesis is
discharged nowhere, so there is no consumer to have.  The reason is uniform
across the module, which is why it is said once here rather than repeated on
each declaration.  A zero reference count is not a verdict (`CLAUDE.md`, dead
code), and these are not helpers: they state paper steps.

What would make them consumed is named in
`exists_endpoint_phase_deriv_bound_of_chart`, and the assembly of the three
regions into one `κ` is `abs_le_of_cover_three`.

**`τ''` does not come from the angle sums by algebra of limits, and a theorem
saying it did was withdrawn from here.**  `τ' = -(S_a - r)/S_t` with
`S_t = ftAngleSumDerivTau`, and at the lower endpoint that quotient is never a
quotient of limits.  Two regimes, both failing: where the branch's limit sits
strictly inside the first gap no `a_k` equals `τ`, every angle runs to `0` or
`π`, and `S_t → 0` linearly, so the quotient is `0/0`; at a repeated minimum the
collision members have `a_k = τ` **exactly**, sit at `θ_k → π/2` with
`sin²θ_k → 1`, and `S_t` **diverges** like `-ρ/θ`.  So a hypothesis asking that
`S_t` converge to a nonzero limit is unsatisfiable in both — vacuous, green, and
invisible to every gate here.  `../scripts/check_angle_partial_tau_vanishes.py`
measures it.  The route to `τ''` is not this one.

**The binders are one-sided at the endpoint and two-sided off it**, which is what
`EndpointRegularity` requires: `δ` is a distance, so a two-sided `HasDerivAt` at
`0` asks for the negation of the phenomenon it describes.  The proof needs no
more — Mathlib's `image_norm_le_of_norm_deriv_right_le_deriv_boundary` runs on
right derivatives on `Ico`, which is exactly the available side.

**The Lipschitz hypothesis is taken in the weakest form the proof consumes**: a
bound on `‖γ'(δ) - γ'(0)‖` against `Lδ`, not `LipschitzOnWith` on the collar.
`norm_deriv_sub_le_of_lipschitzOnWith` supplies it from the stronger form for a
caller that has one.

**Two constants, and neither is guessed.**  `‖u(δ) - γ'(0)‖ ≤ Lδ/2` is sharp and
attained.  `‖u'‖ ≤ 3L/2` is not: splitting the numerator as
`δ(γ'(δ) - γ'(0)) - (γ(δ) - δγ'(0))` costs a factor of three against the sharp
`L/2`, and buys not having to run the boundary lemma a second time against a
moving base point.

**The collar is `min b (‖γ'(0)‖/(L+1))`, and the `+1` is load-bearing.**  At
`L = 0` the branch is affine and every bound here holds on all of `[0,b]`, but
`‖γ'(0)‖/L` is `x / 0 = 0` in Lean's arithmetic, which would hand back an empty
collar — a quantity with no pole where the mathematics has none.

**`p ≠ 0` in the composed form.**  At `p = 0` there is no real factor, `δ^p ≠ 0`
holds *at* the endpoint, and the composition would ask for `u` to be
differentiable there, which is what the whole module exists to avoid needing.
That case is `exists_phase_deriv_bound_of_bound` applied to the same `hbd`
directly.

Sorry-free.

## References

Formalizes `../shields-2026-forgacs-tran-numerators.tex`, «Spectral geometry,
residues, and the principal amplitude» (`sec:geometry`, `lem:amplitude-divisor`,
`eq:W-endpoint-form`, `eq:phase-derivative-bound`,
`lem:principal-endpoint-regularity`, `eq:z-endpoint-order`), in the form
«Angular discrepancy and proof of the main theorem» (`subsec:proof`,
`eq:retained-range`) consumes it.

## Tags

endpoint cofactor, phase derivative, divided difference, collar, uniformity
-/

namespace ForgacsTran

open Set Complex

/-- **The cofactor of `eq:W-endpoint-form`, as a divided difference.**  With the
endpoint value subtracted off, `γ - t_e = δ·u(δ)` reads `u(δ) = (γ - t_e)/δ`;
callers pass the shifted branch, so `γ 0 = 0` throughout this module. -/
noncomputable def endpointCofactor (γ : ℝ → ℂ) (θ : ℝ) : ℂ := γ θ / (θ : ℂ)

/-- The derivative of `endpointCofactor`, by the quotient rule.  It is a
definition rather than a `deriv` so that the numerator — the quantity the whole
estimate is about — is visible in every statement below. -/
noncomputable def endpointCofactorDeriv (γ dγ : ℝ → ℂ) (θ : ℝ) : ℂ :=
  (dγ θ * (θ : ℂ) - γ θ) / (θ : ℂ) ^ 2

/-- `s ↦ (s : ℂ)` has derivative `1`, as a real-variable complex-valued map. -/
private theorem hasDerivAt_ofReal (θ : ℝ) : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 θ := by
  simpa using (hasDerivAt_id θ).ofReal_comp

/-- **`u` is differentiable off the endpoint.**  The quotient rule; nothing here
reaches `θ = 0`, where `u` need not even be defined by the formula. -/
theorem hasDerivAt_endpointCofactor {γ dγ : ℝ → ℂ} {θ : ℝ}
    (hd : HasDerivAt γ (dγ θ) θ) (hθ : θ ≠ 0) :
    HasDerivAt (endpointCofactor γ) (endpointCofactorDeriv γ dγ θ) θ := by
  have hne : (θ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hθ
  have h := hd.div (hasDerivAt_ofReal θ) hne
  rw [mul_one] at h
  exact h

/-- **The Lipschitz hypothesis, from the usual form.**  The proofs below consume
only a bound against the endpoint value; a caller holding `LipschitzOnWith` on
the collar gets that here. -/
theorem norm_deriv_sub_le_of_lipschitzOnWith {dγ : ℝ → ℂ} {b : ℝ} {L : NNReal}
    (h : LipschitzOnWith L dγ (Icc (0 : ℝ) b)) (hb : 0 ≤ b) :
    ∀ θ ∈ Icc (0 : ℝ) b, ‖dγ θ - dγ 0‖ ≤ (L : ℝ) * θ := by
  intro θ hθ
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) b := ⟨le_rfl, hb⟩
  have := h.dist_le_mul θ hθ 0 h0
  rwa [Complex.dist_eq, Real.dist_eq, sub_zero, abs_of_nonneg hθ.1] at this

section Taylor

variable {γ dγ : ℝ → ℂ} {b L : ℝ}

/-- **The first-order Taylor bound at the endpoint.**  `γ(δ) - δγ'(0)` vanishes
at `0` and has derivative `γ'(δ) - γ'(0)`, bounded by `Lδ`; Mathlib's
`image_norm_le_of_norm_deriv_right_le_deriv_boundary` against the boundary
`Lδ²/2` gives the bound.  The constant is sharp — `γ(δ) = δ + Lδ²/2` attains it
identically. -/
theorem norm_sub_smul_deriv_le (hγ0 : γ 0 = 0)
    (hd0 : HasDerivWithinAt γ (dγ 0) (Ici (0 : ℝ)) 0)
    (hd : ∀ θ ∈ Ioc (0 : ℝ) b, HasDerivAt γ (dγ θ) θ)
    (hlip : ∀ θ ∈ Icc (0 : ℝ) b, ‖dγ θ - dγ 0‖ ≤ L * θ) :
    ∀ θ ∈ Icc (0 : ℝ) b, ‖γ θ - (θ : ℂ) * dγ 0‖ ≤ L * θ ^ 2 / 2 := by
  have hlin : ∀ x : ℝ, HasDerivAt (fun s : ℝ => (s : ℂ) * dγ 0) (dγ 0) x := fun x => by
    simpa using (hasDerivAt_ofReal x).mul_const (dγ 0)
  -- the right derivative of `γ` at every point of `[0, b)`
  have hright : ∀ x ∈ Ico (0 : ℝ) b, HasDerivWithinAt γ (dγ x) (Ici x) x := by
    intro x hx
    rcases eq_or_lt_of_le hx.1 with hx0 | hx0
    · rw [← hx0]
      exact hd0
    · exact (hd x ⟨hx0, hx.2.le⟩).hasDerivWithinAt
  -- hence continuity on the closed collar
  have hcont : ContinuousOn γ (Icc (0 : ℝ) b) := by
    intro x hx
    rcases eq_or_lt_of_le hx.1 with hx0 | hx0
    · rw [← hx0]
      exact hd0.continuousWithinAt.mono fun y hy => hy.1
    · exact ((hd x ⟨hx0, hx.2⟩).continuousAt).continuousWithinAt
  have hcontf : ContinuousOn (fun s : ℝ => γ s - (s : ℂ) * dγ 0) (Icc (0 : ℝ) b) :=
    hcont.sub (fun x _ => (hlin x).continuousAt.continuousWithinAt)
  have hB : ∀ x : ℝ, HasDerivAt (fun s : ℝ => L * s ^ 2 / 2) (L * x) x := by
    intro x
    have h : HasDerivAt (fun s : ℝ => L * s ^ 2 / 2) (L * (2 * x ^ 1) / 2) x :=
      ((hasDerivAt_pow 2 x).const_mul L).div_const 2
    convert h using 1
    ring
  have hmain := image_norm_le_of_norm_deriv_right_le_deriv_boundary
    (f := fun s : ℝ => γ s - (s : ℂ) * dγ 0)
    (f' := fun s : ℝ => dγ s - dγ 0) (a := 0) (b := b) hcontf
    (fun x hx => (hright x hx).sub (hlin x).hasDerivWithinAt)
    (B := fun s : ℝ => L * s ^ 2 / 2) (B' := fun s : ℝ => L * s)
    (by simp [hγ0]) hB
    (fun x hx => hlip x ⟨hx.1, hx.2.le⟩)
  exact fun θ hθ => hmain hθ

/-- **The cofactor is near its endpoint value.**  Dividing the Taylor bound by
`δ`: `‖u(δ) - γ'(0)‖ ≤ Lδ/2`.  This is what puts `u` off zero on a collar, and
the collar's length is read off this inequality rather than assumed. -/
theorem norm_endpointCofactor_sub_le (hγ0 : γ 0 = 0)
    (hd0 : HasDerivWithinAt γ (dγ 0) (Ici (0 : ℝ)) 0)
    (hd : ∀ θ ∈ Ioc (0 : ℝ) b, HasDerivAt γ (dγ θ) θ)
    (hlip : ∀ θ ∈ Icc (0 : ℝ) b, ‖dγ θ - dγ 0‖ ≤ L * θ) :
    ∀ θ ∈ Ioc (0 : ℝ) b, ‖endpointCofactor γ θ - dγ 0‖ ≤ L * θ / 2 := by
  intro θ hθ
  have hne : (θ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hθ.1.ne'
  have hsplit : endpointCofactor γ θ - dγ 0 = (γ θ - (θ : ℂ) * dγ 0) / (θ : ℂ) := by
    change γ θ / (θ : ℂ) - dγ 0 = (γ θ - (θ : ℂ) * dγ 0) / (θ : ℂ)
    field_simp
  have htay := norm_sub_smul_deriv_le hγ0 hd0 hd hlip θ ⟨hθ.1.le, hθ.2⟩
  rw [hsplit, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hθ.1]
  rw [div_le_iff₀ hθ.1]
  calc ‖γ θ - (θ : ℂ) * dγ 0‖ ≤ L * θ ^ 2 / 2 := htay
    _ = L * θ / 2 * θ := by ring

/-- **The estimate the whole module exists for.**  `‖u'‖ ≤ 3L/2` on the punctured
collar.  The numerator of `u'` is split as `δ(γ'(δ) - γ'(0)) - (γ(δ) - δγ'(0))`,
bounded by `Lδ²` and `Lδ²/2`; the `δ²` cancels the one in the denominator and
what is left is a constant. -/
theorem norm_endpointCofactorDeriv_le (hγ0 : γ 0 = 0)
    (hd0 : HasDerivWithinAt γ (dγ 0) (Ici (0 : ℝ)) 0)
    (hd : ∀ θ ∈ Ioc (0 : ℝ) b, HasDerivAt γ (dγ θ) θ)
    (hlip : ∀ θ ∈ Icc (0 : ℝ) b, ‖dγ θ - dγ 0‖ ≤ L * θ) :
    ∀ θ ∈ Ioc (0 : ℝ) b, ‖endpointCofactorDeriv γ dγ θ‖ ≤ 3 * L / 2 := by
  intro θ hθ
  have hθ0 : (0 : ℝ) < θ := hθ.1
  have hne : (θ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hθ0.ne'
  have htay := norm_sub_smul_deriv_le hγ0 hd0 hd hlip θ ⟨hθ0.le, hθ.2⟩
  have hlp := hlip θ ⟨hθ0.le, hθ.2⟩
  -- the two-term split of the numerator
  have hsplit : dγ θ * (θ : ℂ) - γ θ
      = (θ : ℂ) * (dγ θ - dγ 0) - (γ θ - (θ : ℂ) * dγ 0) := by ring
  have hnum : ‖dγ θ * (θ : ℂ) - γ θ‖ ≤ 3 * L / 2 * θ ^ 2 := by
    rw [hsplit]
    refine le_trans (norm_sub_le _ _) ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hθ0]
    have h1 : θ * ‖dγ θ - dγ 0‖ ≤ θ * (L * θ) := by
      exact mul_le_mul_of_nonneg_left hlp hθ0.le
    nlinarith [htay, h1]
  have hden : ‖((θ : ℂ)) ^ 2‖ = θ ^ 2 := by
    rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hθ0]
  rw [endpointCofactorDeriv, norm_div, hden, div_le_iff₀ (by positivity)]
  exact hnum

end Taylor

/-- **The Lipschitz binder, from a second-derivative bound off the endpoint.**
`hlip` is a statement *at* the endpoint, and the endpoint is exactly where the
branch's second derivative is not available.  This trades it for two facts that
are: a bound on `γ''` on the **punctured** collar, where the closed forms of
`BranchCurvature` live, and continuity of `γ'` at the endpoint, which is the
one-sided derivative the branch already carries.

The mean value inequality gives `‖γ'(θ) - γ'(ε)‖ ≤ L(θ - ε)` on `[ε, θ]` for
every `ε > 0`; letting `ε → 0⁺` and using continuity transfers it to the
endpoint.  Nothing is asked of `γ''` at `0`, where it need not exist. -/
theorem norm_deriv_sub_le_of_norm_deriv2_le {dγ d2γ : ℝ → ℂ} {b L : ℝ}
    (hc : ContinuousWithinAt dγ (Ici (0 : ℝ)) 0)
    (hd2 : ∀ θ ∈ Ioc (0 : ℝ) b, HasDerivAt dγ (d2γ θ) θ)
    (hb2 : ∀ θ ∈ Ioc (0 : ℝ) b, ‖d2γ θ‖ ≤ L) :
    ∀ θ ∈ Icc (0 : ℝ) b, ‖dγ θ - dγ 0‖ ≤ L * θ := by
  intro θ hθ
  rcases eq_or_lt_of_le hθ.1 with hθ0 | hθ0
  · simp [← hθ0]
  -- the limit the endpoint value is reached through
  have hlim : Filter.Tendsto (fun ε : ℝ => L * (θ - ε) + ‖dγ ε - dγ 0‖)
      (nhdsWithin 0 (Ioi (0 : ℝ))) (nhds (L * θ)) := by
    have h1 : Filter.Tendsto (fun ε : ℝ => L * (θ - ε))
        (nhdsWithin 0 (Ioi (0 : ℝ))) (nhds (L * θ)) := by
      have hcont : Continuous fun ε : ℝ => L * (θ - ε) :=
        continuous_const.mul (continuous_const.sub continuous_id)
      simpa using (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
    have h2 : Filter.Tendsto (fun ε : ℝ => ‖dγ ε - dγ 0‖)
        (nhdsWithin 0 (Ioi (0 : ℝ))) (nhds 0) := by
      have hd : Filter.Tendsto dγ (nhdsWithin 0 (Ioi (0 : ℝ))) (nhds (dγ 0)) :=
        hc.mono_left (nhdsWithin_mono _ Ioi_subset_Ici_self)
      have hconst : Filter.Tendsto (fun _ : ℝ => dγ 0)
          (nhdsWithin 0 (Ioi (0 : ℝ))) (nhds (dγ 0)) := tendsto_const_nhds
      simpa using (hd.sub hconst).norm
    simpa using h1.add h2
  refine ge_of_tendsto hlim ?_
  filter_upwards [Ioo_mem_nhdsGT hθ0] with ε hε
  -- the mean value inequality on `[ε, θ]`, which misses the endpoint entirely
  have hsub : Icc ε θ ⊆ Ioc (0 : ℝ) b := fun x hx =>
    ⟨lt_of_lt_of_le hε.1 hx.1, le_trans hx.2 hθ.2⟩
  have hmvt : ‖dγ θ - dγ ε‖ ≤ L * (θ - ε) := by
    have h := (convex_Icc ε θ).norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := dγ) (f' := d2γ) (C := L)
      (fun x hx => (hd2 x (hsub hx)).hasDerivWithinAt)
      (fun x hx => hb2 x (hsub hx))
      (left_mem_Icc.2 hε.2.le) (right_mem_Icc.2 hε.2.le)
    rwa [Real.norm_eq_abs, abs_of_nonneg (sub_pos.2 hε.2).le] at h
  have htri : ‖dγ θ - dγ 0‖ ≤ ‖dγ θ - dγ ε‖ + ‖dγ ε - dγ 0‖ := by
    have hsplit : dγ θ - dγ 0 = (dγ θ - dγ ε) + (dγ ε - dγ 0) := by ring
    rw [hsplit]
    exact norm_add_le _ _
  linarith [hmvt, htri]

/-- **`hbd` at the endpoint.**  `|Im(u'/u)| ≤ 3L/‖γ'(0)‖` on `(0, b']`, with
`b' = min b (‖γ'(0)‖/(L+1))`: the numerator is bounded by
`norm_endpointCofactorDeriv_le` and the denominator is off zero by
`norm_endpointCofactor_sub_le`, and the collar is exactly where the second
inequality bites.

This is the hypothesis `PhaseDerivativeBound.phase_deriv_bound_uniform_in_collar_of_bound`
takes, in the form it takes it, together with the two side facts that lemma also
asks for — that `u` is differentiable and nonvanishing where it is used. -/
theorem exists_bound_im_endpointCofactor_logDeriv {γ dγ : ℝ → ℂ} {b L : ℝ}
    (hb : 0 < b) (hL : 0 ≤ L) (hγ0 : γ 0 = 0)
    (hd0 : HasDerivWithinAt γ (dγ 0) (Ici (0 : ℝ)) 0)
    (hd : ∀ θ ∈ Ioc (0 : ℝ) b, HasDerivAt γ (dγ θ) θ)
    (hlip : ∀ θ ∈ Icc (0 : ℝ) b, ‖dγ θ - dγ 0‖ ≤ L * θ)
    (h0 : dγ 0 ≠ 0) :
    ∃ b' : ℝ, 0 < b' ∧ b' ≤ b ∧
      (∀ θ ∈ Icc (0 : ℝ) b', θ ≠ 0 → endpointCofactor γ θ ≠ 0) ∧
      (∀ θ ∈ Icc (0 : ℝ) b', θ ≠ 0 →
        HasDerivAt (endpointCofactor γ) (endpointCofactorDeriv γ dγ θ) θ) ∧
      (∀ θ ∈ Icc (0 : ℝ) b', θ ≠ 0 →
        |(endpointCofactorDeriv γ dγ θ / endpointCofactor γ θ).im|
          ≤ 3 * L / ‖dγ 0‖) := by
  have hg0 : 0 < ‖dγ 0‖ := norm_pos_iff.mpr h0
  set b' : ℝ := min b (‖dγ 0‖ / (L + 1)) with hb'def
  have hL1 : (0 : ℝ) < L + 1 := by linarith
  have hb'0 : 0 < b' := lt_min hb (by positivity)
  have hb'b : b' ≤ b := min_le_left _ _
  -- on the collar the cofactor is at least half its endpoint value
  have hlower : ∀ θ ∈ Ioc (0 : ℝ) b', ‖dγ 0‖ / 2 ≤ ‖endpointCofactor γ θ‖ := by
    intro θ hθ
    have hθb : θ ≤ b := le_trans hθ.2 hb'b
    have hnear := norm_endpointCofactor_sub_le hγ0 hd0 hd hlip θ ⟨hθ.1, hθb⟩
    have hsmall : L * θ / 2 ≤ ‖dγ 0‖ / 2 := by
      have hθL : θ ≤ ‖dγ 0‖ / (L + 1) := le_trans hθ.2 (min_le_right _ _)
      have : L * θ ≤ L * (‖dγ 0‖ / (L + 1)) := mul_le_mul_of_nonneg_left hθL hL
      have hfrac : L * (‖dγ 0‖ / (L + 1)) ≤ ‖dγ 0‖ := by
        rw [mul_div_assoc'] at *
        rw [div_le_iff₀ hL1]
        nlinarith [hg0]
      linarith
    have hrev : ‖dγ 0‖ - ‖endpointCofactor γ θ‖ ≤ ‖endpointCofactor γ θ - dγ 0‖ := by
      rw [← norm_neg (endpointCofactor γ θ - dγ 0)]
      simpa using norm_sub_norm_le (dγ 0) (endpointCofactor γ θ)
    linarith
  refine ⟨b', hb'0, hb'b, ?_, ?_, ?_⟩
  · intro θ hθ hθ0
    have hpos : (0 : ℝ) < θ := lt_of_le_of_ne hθ.1 (Ne.symm hθ0)
    have := hlower θ ⟨hpos, hθ.2⟩
    exact norm_pos_iff.mp (lt_of_lt_of_le (by positivity) this)
  · intro θ hθ hθ0
    have hpos : (0 : ℝ) < θ := lt_of_le_of_ne hθ.1 (Ne.symm hθ0)
    exact hasDerivAt_endpointCofactor (hd θ ⟨hpos, le_trans hθ.2 hb'b⟩) hθ0
  · intro θ hθ hθ0
    have hpos : (0 : ℝ) < θ := lt_of_le_of_ne hθ.1 (Ne.symm hθ0)
    have hθb : θ ≤ b := le_trans hθ.2 hb'b
    have hnum := norm_endpointCofactorDeriv_le hγ0 hd0 hd hlip θ ⟨hpos, hθb⟩
    have hden := hlower θ ⟨hpos, hθ.2⟩
    have hden0 : (0 : ℝ) < ‖endpointCofactor γ θ‖ := lt_of_lt_of_le (by positivity) hden
    calc |(endpointCofactorDeriv γ dγ θ / endpointCofactor γ θ).im|
        ≤ ‖endpointCofactorDeriv γ dγ θ / endpointCofactor γ θ‖ :=
          Complex.abs_im_le_norm _
      _ = ‖endpointCofactorDeriv γ dγ θ‖ / ‖endpointCofactor γ θ‖ := norm_div _ _
      _ ≤ 3 * L / ‖dγ 0‖ := by
          rw [div_le_div_iff₀ hden0 hg0]
          nlinarith [mul_le_mul_of_nonneg_right hnum hg0.le,
            mul_le_mul_of_nonneg_left hden (by positivity : (0 : ℝ) ≤ 3 * L)]

/-- **`eq:phase-derivative-bound` on the collar, at an endpoint of
`eq:W-endpoint-form`.**  `W = δ^p·u(δ)` with `p ≠ 0`: the real factor drops out
of the phase by `PhaseDerivativeBound.im_logDeriv_real_factor`, and what is left
is the cofactor bound above.  One `κ`, chosen once, serves every `M` — which is
the clause `AngularDiscrepancyFT.FTPhaseSupply` states as a threshold on `M`
rather than as a growth claim about a `κ_M`.

Every hypothesis is one-sided at the endpoint and two-sided off it, and none of
them is a limit. -/
theorem exists_endpoint_phase_deriv_bound_zpow {γ dγ : ℝ → ℂ} {b L h : ℝ} {p : ℤ}
    (hb : 0 < b) (hL : 0 ≤ L) (hh : 0 ≤ h) (hp : p ≠ 0) (hγ0 : γ 0 = 0)
    (hd0 : HasDerivWithinAt γ (dγ 0) (Ici (0 : ℝ)) 0)
    (hd : ∀ θ ∈ Ioc (0 : ℝ) b, HasDerivAt γ (dγ θ) θ)
    (hlip : ∀ θ ∈ Icc (0 : ℝ) b, ‖dγ θ - dγ 0‖ ≤ L * θ)
    (h0 : dγ 0 ≠ 0) :
    ∃ b' κ : ℝ, 0 < b' ∧ b' ≤ b ∧ 0 ≤ κ ∧
      ∀ M : ℕ, ∀ θ ∈ Icc (h / M) b', θ ≠ 0 →
        |(deriv (fun s : ℝ => ((s ^ p : ℝ) : ℂ) * endpointCofactor γ s) θ
            / (((θ ^ p : ℝ) : ℂ) * endpointCofactor γ θ)).im| ≤ κ := by
  obtain ⟨b', hb'0, hb'b, hne, hderiv, hbd⟩ :=
    exists_bound_im_endpointCofactor_logDeriv hb hL hγ0 hd0 hd hlip h0
  -- `θ ^ p ≠ 0` and `θ ≠ 0` agree because `p ≠ 0`
  have hzero : ∀ θ : ℝ, θ ^ p ≠ 0 → θ ≠ 0 := by
    intro θ hθ hθ0
    exact hθ (by rw [hθ0]; exact zero_zpow p hp)
  obtain ⟨κ, hκ0, hκ⟩ := phase_deriv_bound_uniform_in_collar_of_bound
    (ρ := fun s : ℝ => s ^ p) (dρ := fun s : ℝ => (p : ℝ) * s ^ (p - 1))
    (U := endpointCofactor γ) (dU := endpointCofactorDeriv γ dγ)
    (b := b') (h := h) (κ₀ := 3 * L / ‖dγ 0‖) hh
    (fun θ _ hρ0 => by
      rcases lt_or_ge p 0 with hlt | hge
      · exact hasDerivAt_zpow p θ
          (Or.inl fun hz => hρ0 (by rw [hz]; exact zero_zpow p (ne_of_lt hlt)))
      · exact hasDerivAt_zpow p θ (Or.inr hge))
    (fun θ hθ hρ0 => hderiv θ hθ (hzero θ hρ0))
    (fun θ hθ hρ0 => hbd θ hθ (hzero θ hρ0))
    (fun θ hθ hρ0 => hne θ hθ (hzero θ hρ0))
  exact ⟨b', κ, hb'0, hb'b, hκ0, fun M θ hθ hθ0 => hκ M θ hθ (zpow_ne_zero _ hθ0)⟩

/-- **`eq:phase-derivative-bound` on the collar, owing only punctured-collar
data.**  `exists_endpoint_phase_deriv_bound_zpow` with its Lipschitz binder
discharged by `norm_deriv_sub_le_of_norm_deriv2_le`.

What is left owed is a list with nothing *at* the endpoint on it beyond a
one-sided first derivative: `γ''` bounded on `(0,b]`, `γ'` continuous at `0`, and
`γ'(0) ≠ 0`.  Those are the closed forms `BranchCurvature` computes and the
endpoint value `EndpointRegularity` carries, and none of them is a limit of a
second-order quantity.

Stated as a composition rather than as a remark that the two shapes agree,
because a producer whose conclusion is one clause off its consumer's hypothesis
type-checks on each side alone and fails only where the two are put together. -/
theorem exists_endpoint_phase_deriv_bound_of_deriv2 {γ dγ d2γ : ℝ → ℂ} {b L h : ℝ}
    {p : ℤ} (hb : 0 < b) (hL : 0 ≤ L) (hh : 0 ≤ h) (hp : p ≠ 0) (hγ0 : γ 0 = 0)
    (hd0 : HasDerivWithinAt γ (dγ 0) (Ici (0 : ℝ)) 0)
    (hd : ∀ θ ∈ Ioc (0 : ℝ) b, HasDerivAt γ (dγ θ) θ)
    (hc : ContinuousWithinAt dγ (Ici (0 : ℝ)) 0)
    (hd2 : ∀ θ ∈ Ioc (0 : ℝ) b, HasDerivAt dγ (d2γ θ) θ)
    (hb2 : ∀ θ ∈ Ioc (0 : ℝ) b, ‖d2γ θ‖ ≤ L)
    (h0 : dγ 0 ≠ 0) :
    ∃ b' κ : ℝ, 0 < b' ∧ b' ≤ b ∧ 0 ≤ κ ∧
      ∀ M : ℕ, ∀ θ ∈ Icc (h / M) b', θ ≠ 0 →
        |(deriv (fun s : ℝ => ((s ^ p : ℝ) : ℂ) * endpointCofactor γ s) θ
            / (((θ ^ p : ℝ) : ℂ) * endpointCofactor γ θ)).im| ≤ κ :=
  exists_endpoint_phase_deriv_bound_zpow hb hL hh hp hγ0 hd0 hd
    (norm_deriv_sub_le_of_norm_deriv2_le hc hd2 hb2) h0

/-- **A bound off the endpoint, from a one-sided limit at it.**  `γ''` is not
bounded on `(0,b]` for any reason visible on `(0,b]` alone — continuity there
says nothing as `δ → 0⁺`.  What makes it bounded is that it *extends*, and this
is that argument: the limit controls a punctured neighborhood of the endpoint,
compactness controls what is left, and the two are glued.

Stated for `ℂ` because the branch is complex-valued, but nothing here is about
`γ` — it is the general fact, and it is what turns the remaining hypothesis of
`exists_endpoint_phase_deriv_bound_of_deriv2` from an estimate into a limit. -/
theorem exists_bound_of_continuousOn_of_tendsto {f : ℝ → ℂ} {b : ℝ} {A : ℂ}
    (hc : ContinuousOn f (Ioc (0 : ℝ) b))
    (hlim : Filter.Tendsto f (nhdsWithin 0 (Ioi (0 : ℝ))) (nhds A)) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ θ ∈ Ioc (0 : ℝ) b, ‖f θ‖ ≤ L := by
  -- the limit controls a punctured neighborhood of the endpoint
  have hnear : ∀ᶠ θ in nhdsWithin 0 (Ioi (0 : ℝ)), ‖f θ‖ ≤ ‖A‖ + 1 := by
    have hconst : Filter.Tendsto (fun _ : ℝ => A)
        (nhdsWithin 0 (Ioi (0 : ℝ))) (nhds A) := tendsto_const_nhds
    have h0 : Filter.Tendsto (fun θ => ‖f θ - A‖)
        (nhdsWithin 0 (Ioi (0 : ℝ))) (nhds 0) := by
      simpa using (hlim.sub hconst).norm
    filter_upwards [h0.eventually (eventually_lt_nhds one_pos)] with θ hθ
    have := norm_add_le (f θ - A) A
    simp only [sub_add_cancel] at this
    linarith
  obtain ⟨δ, hδ0, hδ⟩ := (nhdsGT_basis (0 : ℝ)).eventually_iff.1 hnear
  rcases le_or_gt b 0 with hb | hb
  · exact ⟨0, le_rfl, fun θ hθ => absurd (hθ.2.trans hb) (not_le.2 hθ.1)⟩
  -- and compactness controls the rest
  set c : ℝ := min (δ / 2) b with hcdef
  have hc0 : 0 < c := lt_min (by linarith) hb
  have hsub : Icc c b ⊆ Ioc (0 : ℝ) b := fun x hx => ⟨lt_of_lt_of_le hc0 hx.1, hx.2⟩
  obtain ⟨L₂, hL₂⟩ := isCompact_Icc.exists_bound_of_continuousOn (hc.mono hsub)
  refine ⟨max (‖A‖ + 1) (max L₂ 0),
    le_trans (le_max_right L₂ 0) (le_max_right _ _), fun θ hθ => ?_⟩
  rcases lt_or_ge θ c with hlt | hge
  · have hθδ : θ ∈ Ioo (0 : ℝ) δ := by
      refine ⟨hθ.1, ?_⟩
      have := min_le_left (δ / 2) b
      have : θ < δ / 2 := lt_of_lt_of_le hlt this
      linarith
    exact le_trans (hδ hθδ) (le_max_left _ _)
  · exact le_trans (hL₂ θ ⟨hge, hθ.2⟩) (le_trans (le_max_left _ _) (le_max_right _ _))

/-- **`eq:phase-derivative-bound` on the collar, owing a limit rather than an
estimate.**  `exists_endpoint_phase_deriv_bound_of_deriv2` with its one
constant-bearing hypothesis discharged by `exists_bound_of_continuousOn_of_tendsto`.

What is owed is now a list with no constant on it at all: `γ''` continuous off
the endpoint, `γ''` convergent at it, `γ'` continuous at it, `γ'(0) ≠ 0`.  The
constant is produced rather than supplied, which matters because the constant is
the part a caller cannot read off the pencil — the limit it *can*.

The value of the limit is not a hypothesis and does not appear in the
conclusion; only its existence is used. -/
theorem exists_endpoint_phase_deriv_bound_of_deriv2_limit {γ dγ d2γ : ℝ → ℂ}
    {b h : ℝ} {A : ℂ} {p : ℤ} (hb : 0 < b) (hh : 0 ≤ h) (hp : p ≠ 0) (hγ0 : γ 0 = 0)
    (hd0 : HasDerivWithinAt γ (dγ 0) (Ici (0 : ℝ)) 0)
    (hd : ∀ θ ∈ Ioc (0 : ℝ) b, HasDerivAt γ (dγ θ) θ)
    (hc : ContinuousWithinAt dγ (Ici (0 : ℝ)) 0)
    (hd2 : ∀ θ ∈ Ioc (0 : ℝ) b, HasDerivAt dγ (d2γ θ) θ)
    (hc2 : ContinuousOn d2γ (Ioc (0 : ℝ) b))
    (hlim2 : Filter.Tendsto d2γ (nhdsWithin 0 (Ioi (0 : ℝ))) (nhds A))
    (h0 : dγ 0 ≠ 0) :
    ∃ b' κ : ℝ, 0 < b' ∧ b' ≤ b ∧ 0 ≤ κ ∧
      ∀ M : ℕ, ∀ θ ∈ Icc (h / M) b', θ ≠ 0 →
        |(deriv (fun s : ℝ => ((s ^ p : ℝ) : ℂ) * endpointCofactor γ s) θ
            / (((θ ^ p : ℝ) : ℂ) * endpointCofactor γ θ)).im| ≤ κ := by
  obtain ⟨L, hL, hb2⟩ := exists_bound_of_continuousOn_of_tendsto hc2 hlim2
  exact exists_endpoint_phase_deriv_bound_of_deriv2 hb hL hh hp hγ0 hd0 hd hc hd2 hb2 h0

/-! ### The amplitude's cofactor, split -/

/-- **The two divided differences agree where either is used.**
`Amplitude.amplitude_endpoint_form` builds its cofactor out of
`fun δ => if δ = 0 then γ_e else (γ δ - t_e)/δ` — the *continuous extension*,
which it needs because its conclusion speaks at the endpoint.  `endpointCofactor`
is the raw quotient, so it takes the value `0` there: `γ(0) - t_e = 0` and
`0 / 0 = 0` in Lean.

The two therefore differ at exactly one point, and it is the endpoint.  They are
related here on `𝓝[>] 0`, where both are the same quotient, and **never by
unfolding either** — unfolding the extension at `0` reads `γ_e`, unfolding
`endpointCofactor` there reads `0`, and each is correct for its own definition,
so an argument that mixes them produces a plausible structure rather than a
visibly wrong number. -/
theorem eventuallyEq_endpointCofactor_of_quotient {γ : ℝ → ℂ} {te : ℂ} {u : ℝ → ℂ}
    (hu : ∀ δ : ℝ, δ ≠ 0 → u δ = (γ δ - te) / (δ : ℂ)) :
    u =ᶠ[nhdsWithin 0 (Ioi (0 : ℝ))] endpointCofactor (fun s => γ s - te) :=
  Filter.eventuallyEq_of_mem self_mem_nhdsWithin fun δ hδ => hu δ (ne_of_gt hδ)

/-- `|Im(logDeriv f)| ≤ ‖f'‖/‖f‖`, which is what bounds the two outer terms of
the split below: each is a factor that neither vanishes nor blows up at the
endpoint, so its logarithmic derivative is controlled with no cancellation
argument at all. -/
theorem abs_im_logDeriv_le (f : ℝ → ℂ) (δ : ℝ) :
    |(logDeriv f δ).im| ≤ ‖deriv f δ‖ / ‖f δ‖ := by
  rw [logDeriv_apply]
  calc |(deriv f δ / f δ).im| ≤ ‖deriv f δ / f δ‖ := Complex.abs_im_le_norm _
    _ = ‖deriv f δ‖ / ‖f δ‖ := norm_div _ _

/-- **`eq:W-endpoint-form`'s cofactor, split into three.**  The cofactor
`Amplitude.amplitude_endpoint_form` produces has the shape
`c·γ(δ)·u(δ)^p·A(δ)` — a constant, the branch, a power of the divided
difference, and a factor analytic and nonvanishing at the endpoint.  The
imaginary part of a logarithmic derivative is additive over that, so

  `Im(V'/V) = Im(γ'/γ) + p·Im(u'/u) + Im(A'/A)`,

and the constant drops out entirely.  **Only the middle term is delicate**: it is
the one whose factor degenerates at the endpoint, and it is exactly what
`exists_bound_im_endpointCofactor_logDeriv` bounds.  The other two are factors
that neither vanish nor blow up there. -/
theorem im_logDeriv_endpoint_factorization {γ u A : ℝ → ℂ} {c : ℂ} {δ : ℝ} {p : ℤ}
    (hc : c ≠ 0)
    (hγd : DifferentiableAt ℝ γ δ) (hγ0 : γ δ ≠ 0)
    (hud : DifferentiableAt ℝ u δ) (hu0 : u δ ≠ 0)
    (hAd : DifferentiableAt ℝ A δ) (hA0 : A δ ≠ 0) :
    (logDeriv (fun s : ℝ => c * γ s * (u s) ^ p * A s) δ).im
      = (logDeriv γ δ).im + (p : ℝ) * (logDeriv u δ).im + (logDeriv A δ).im := by
  -- `u : ℝ → ℂ` crosses fields, so the `ℂ`-differentiability of `z ↦ z^p` is
  -- restricted to `ℝ` before composing; `DifferentiableAt.zpow` is stated for a
  -- map of one field to itself and does not reach this.
  have hzp : DifferentiableAt ℝ (fun s : ℝ => (u s) ^ p) δ := by
    have h1 : DifferentiableAt ℂ (fun z : ℂ => z ^ p) (u δ) :=
      differentiableAt_zpow.2 (Or.inl hu0)
    exact (h1.restrictScalars ℝ).comp δ hud
  have hzp0 : (u δ) ^ p ≠ 0 := zpow_ne_zero _ hu0
  have hcγd : DifferentiableAt ℝ (fun s : ℝ => c * γ s) δ := hγd.const_mul c
  have hcγ0 : c * γ δ ≠ 0 := mul_ne_zero hc hγ0
  -- `f` and `g` are named at each step: left as metavariables for `rw` to
  -- unify, the products elaborate against the wrong factorization.
  have e1 : logDeriv (fun s : ℝ => (c * γ s * (u s) ^ p) * A s) δ
      = logDeriv (fun s : ℝ => c * γ s * (u s) ^ p) δ + logDeriv A δ :=
    logDeriv_mul (f := fun s : ℝ => c * γ s * (u s) ^ p) (g := A) δ
      (mul_ne_zero hcγ0 hzp0) hA0 (hcγd.mul hzp) hAd
  have e2 : logDeriv (fun s : ℝ => (c * γ s) * (u s) ^ p) δ
      = logDeriv (fun s : ℝ => c * γ s) δ + logDeriv (fun s : ℝ => (u s) ^ p) δ :=
    logDeriv_mul (f := fun s : ℝ => c * γ s) (g := fun s : ℝ => (u s) ^ p) δ
      hcγ0 hzp0 hcγd hzp
  have e3 : logDeriv (fun s : ℝ => c * γ s) δ = logDeriv γ δ :=
    logDeriv_const_mul δ c hc
  have e4 : logDeriv (fun s : ℝ => (u s) ^ p) δ = (p : ℂ) * logDeriv u δ :=
    logDeriv_fun_zpow hud p
  rw [e1, e2, e3, e4]
  simp [Complex.add_im, Complex.mul_im]

/-- **The split, as a bound.**  With the middle term supplied — by
`exists_bound_im_endpointCofactor_logDeriv`, which is what this module produces —
the whole of `|Im(V'/V)|` is controlled by three quantities none of which
requires anything at the endpoint. -/
theorem abs_im_logDeriv_endpoint_factorization_le {γ u A : ℝ → ℂ} {c : ℂ} {δ κ : ℝ}
    {p : ℤ} (hc : c ≠ 0)
    (hγd : DifferentiableAt ℝ γ δ) (hγ0 : γ δ ≠ 0)
    (hud : DifferentiableAt ℝ u δ) (hu0 : u δ ≠ 0)
    (hAd : DifferentiableAt ℝ A δ) (hA0 : A δ ≠ 0)
    (hmid : |(logDeriv u δ).im| ≤ κ) :
    |(logDeriv (fun s : ℝ => c * γ s * (u s) ^ p * A s) δ).im|
      ≤ ‖deriv γ δ‖ / ‖γ δ‖ + |(p : ℝ)| * κ + ‖deriv A δ‖ / ‖A δ‖ := by
  rw [im_logDeriv_endpoint_factorization hc hγd hγ0 hud hu0 hAd hA0]
  have h1 : |(logDeriv γ δ).im| ≤ ‖deriv γ δ‖ / ‖γ δ‖ := abs_im_logDeriv_le γ δ
  have h3 : |(logDeriv A δ).im| ≤ ‖deriv A δ‖ / ‖A δ‖ := abs_im_logDeriv_le A δ
  have h2 : |(p : ℝ) * (logDeriv u δ).im| ≤ |(p : ℝ)| * κ := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hmid (abs_nonneg _)
  calc |(logDeriv γ δ).im + (p : ℝ) * (logDeriv u δ).im + (logDeriv A δ).im|
      ≤ |(logDeriv γ δ).im + (p : ℝ) * (logDeriv u δ).im| + |(logDeriv A δ).im| :=
        abs_add_le _ _
    _ ≤ (|(logDeriv γ δ).im| + |(p : ℝ) * (logDeriv u δ).im|) + |(logDeriv A δ).im| := by
        gcongr
        exact abs_add_le _ _
    _ ≤ ‖deriv γ δ‖ / ‖γ δ‖ + |(p : ℝ)| * κ + ‖deriv A δ‖ / ‖A δ‖ := by
        gcongr

/-- **The same bound in `logDeriv` form**, which is the form the split above
consumes.  `exists_bound_im_endpointCofactor_logDeriv` states it with the
explicit `endpointCofactorDeriv`, because that is what the estimate is about;
`im_logDeriv_endpoint_factorization` states its middle term with Mathlib's
`logDeriv`, because that is what the product rule is about.  The two agree
wherever `u` is differentiable, and they are joined here rather than left to
agree by inspection — a producer one clause off its consumer type-checks on each
side alone. -/
theorem exists_bound_im_logDeriv_endpointCofactor {γ dγ : ℝ → ℂ} {b L : ℝ}
    (hb : 0 < b) (hL : 0 ≤ L) (hγ0 : γ 0 = 0)
    (hd0 : HasDerivWithinAt γ (dγ 0) (Ici (0 : ℝ)) 0)
    (hd : ∀ θ ∈ Ioc (0 : ℝ) b, HasDerivAt γ (dγ θ) θ)
    (hlip : ∀ θ ∈ Icc (0 : ℝ) b, ‖dγ θ - dγ 0‖ ≤ L * θ)
    (h0 : dγ 0 ≠ 0) :
    ∃ b' : ℝ, 0 < b' ∧ b' ≤ b ∧
      (∀ θ ∈ Icc (0 : ℝ) b', θ ≠ 0 → endpointCofactor γ θ ≠ 0) ∧
      (∀ θ ∈ Icc (0 : ℝ) b', θ ≠ 0 → DifferentiableAt ℝ (endpointCofactor γ) θ) ∧
      (∀ θ ∈ Icc (0 : ℝ) b', θ ≠ 0 →
        |(logDeriv (endpointCofactor γ) θ).im| ≤ 3 * L / ‖dγ 0‖) := by
  obtain ⟨b', hb'0, hb'b, hne, hderiv, hbd⟩ :=
    exists_bound_im_endpointCofactor_logDeriv hb hL hγ0 hd0 hd hlip h0
  refine ⟨b', hb'0, hb'b, hne, fun θ hθ hθ0 => (hderiv θ hθ hθ0).differentiableAt,
    fun θ hθ hθ0 => ?_⟩
  rw [logDeriv_apply, (hderiv θ hθ hθ0).deriv]
  exact hbd θ hθ hθ0

/-- **`hlim2` is three real limits.**  `γ'' = e^{iθ}(τ'' + 2iτ' - τ)`, and
`e^{iθ} → 1` at the endpoint, so the one complex hypothesis
`exists_ft_endpoint_phase_deriv_bound` still owes is exactly the convergence of
`τ`, `τ'` and `τ''` there — nothing about the branch's direction enters.

This is the reduction and not the limits: `τ`'s is `FTBranchLimitPoint`'s, and
`τ'`, `τ''` are what remain.  Stating it separately is what makes "what is
missing" a list of three real statements rather than one complex one. -/
theorem tendsto_ftGammaDeriv2_of_tendsto {n r l : ℕ} {a : Fin n → ℝ} {T D D2 : ℝ}
    (hτ : Filter.Tendsto (ftTau a r l) (nhdsWithin 0 (Ioi (0 : ℝ))) (nhds T))
    (hτ1 : Filter.Tendsto (ftTauDeriv a r l) (nhdsWithin 0 (Ioi (0 : ℝ))) (nhds D))
    (hτ2 : Filter.Tendsto (ftTauDeriv2 a r l) (nhdsWithin 0 (Ioi (0 : ℝ))) (nhds D2)) :
    Filter.Tendsto (ftGammaDeriv2 a r l) (nhdsWithin 0 (Ioi (0 : ℝ)))
      (nhds ((D2 : ℂ) + 2 * (D : ℂ) * Complex.I - (T : ℂ))) := by
  have hexp : Filter.Tendsto (fun θ : ℝ => Complex.exp ((θ : ℂ) * Complex.I))
      (nhdsWithin 0 (Ioi (0 : ℝ))) (nhds 1) := by
    have hcont : Continuous fun θ : ℝ => Complex.exp ((θ : ℂ) * Complex.I) :=
      Complex.continuous_exp.comp (Complex.continuous_ofReal.mul continuous_const)
    have h := (hcont.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    simpa using h
  have hbr : Filter.Tendsto
      (fun θ : ℝ => ((ftTauDeriv2 a r l θ : ℝ) : ℂ)
        + 2 * ((ftTauDeriv a r l θ : ℝ) : ℂ) * Complex.I
        - ((ftTau a r l θ : ℝ) : ℂ))
      (nhdsWithin 0 (Ioi (0 : ℝ)))
      (nhds ((D2 : ℂ) + 2 * (D : ℂ) * Complex.I - (T : ℂ))) := by
    have h2 := (Complex.continuous_ofReal.tendsto D2).comp hτ2
    have h1 := (Complex.continuous_ofReal.tendsto D).comp hτ1
    have h0 := (Complex.continuous_ofReal.tendsto T).comp hτ
    exact ((h2.add ((tendsto_const_nhds.mul h1).mul tendsto_const_nhds)).sub h0)
  have heq : ftGammaDeriv2 a r l = fun θ : ℝ => Complex.exp ((θ : ℂ) * Complex.I)
      * (((ftTauDeriv2 a r l θ : ℝ) : ℂ)
        + 2 * ((ftTauDeriv a r l θ : ℝ) : ℂ) * Complex.I
        - ((ftTau a r l θ : ℝ) : ℂ)) := rfl
  rw [heq]
  simpa using hexp.mul hbr

/-! ### The threshold, and the clause's own shape -/

/-- **A bound chosen once is a threshold on `M`.**  This is the step that makes
`AngularDiscrepancyFT.FTPhaseSupply`'s `|dψ| < M+1` clause a condition on `M`
rather than a growth claim about a `κ_M`.  It is available only because `κ` does
not move with the collar — that is
`PhaseDerivativeBound.phase_deriv_bound_uniform_in_collar_of_bound`, and it is
what the whole module is for.

No sign hypothesis on `κ`: at `κ < 0` the ceiling is `0` and `Nat.le_ceil` still
carries the inequality, so the statement holds vacuously rather than needing to
be guarded. -/
theorem exists_threshold_of_bound {κ : ℝ} :
    ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M → ∀ x : ℝ, |x| ≤ κ → |x| < (M : ℝ) + 1 := by
  refine ⟨⌈κ⌉₊, fun M hM x hx => ?_⟩
  have h1 : κ ≤ (M : ℝ) := le_trans (Nat.le_ceil κ) (by exact_mod_cast hM)
  linarith

/-- `polarModulus` at `β = 0` **is** the norm.  `FTPhaseSupply` states its
decomposition against `ftPrincipalAmp`, which is `‖ftAmp‖`, so the branch built
by `ViewingAngle` matches the clause only once this is said. -/
theorem polarModulus_eq_norm {W dW : ℝ → ℂ} {U : Set ℝ} {a b : ℝ}
    (hab : a ≤ b) (hU : IsOpen U) (hsub : Icc a b ⊆ U)
    (hd : ∀ s ∈ U, HasDerivAt W (dW s) s) (hc : ContinuousOn dW U)
    (hne : ∀ s ∈ Icc a b, W s ≠ 0) {s : ℝ} (hs : s ∈ Icc a b) :
    polarModulus W dW 0 a s = ‖W s‖ := by
  have h := polar_decomposition (β := (0 : ℂ)) hab hU hsub hd hc hne hs
  rw [sub_zero] at h
  rw [h, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (polarModulus_pos W dW 0 a s)]

/-- **`eq:phase-derivative-bound` in the shape `FTPhaseSupply` states it.**  The
supply asks for three things about one block: that the amplitude factor as
`modulus · e^{iψ}`, that `ψ` be differentiable, and that `|ψ'| < M+1`.  All three
come from `ViewingAngle` at `β = 0` together with a bound on `Im(W'/W)`, and the
third is the threshold above.

`hne` is why the blocks never reach the endpoint: an argument branch cannot be
built through a zero of `W`, and `W` vanishes at an endpoint whenever `p > 0`.
That is not a limitation of this lemma — it is the reason the supply's blocks are
`[h/M, π/r - h/M]` and the reason a **uniform** `κ` over all of them is the right
object rather than one `κ` per block. -/
theorem exists_phase_branch_of_bound {W dW : ℝ → ℂ} {U : Set ℝ} {a b κ : ℝ}
    (hab : a ≤ b) (hU : IsOpen U) (hsub : Icc a b ⊆ U)
    (hd : ∀ s ∈ U, HasDerivAt W (dW s) s) (hc : ContinuousOn dW U)
    (hne : ∀ s ∈ Icc a b, W s ≠ 0)
    (hbd : ∀ s ∈ Icc a b, |(dW s / W s).im| ≤ κ) :
    ∃ (M₀ : ℕ) (ψ dψ : ℝ → ℝ),
      (∀ s ∈ Icc a b, W s
        = ((‖W s‖ : ℝ) : ℂ) * Complex.exp ((ψ s : ℂ) * Complex.I)) ∧
      (∀ s ∈ Icc a b, HasDerivAt ψ (dψ s) s) ∧
      (∀ M : ℕ, M₀ ≤ M → ∀ s ∈ Icc a b, |dψ s| < (M : ℝ) + 1) := by
  obtain ⟨M₀, hM₀⟩ := exists_threshold_of_bound (κ := κ)
  refine ⟨M₀, polarAngle W dW 0 a, fun s => (dW s / W s).im, ?_, ?_,
    fun M hM s hs => hM₀ M hM _ (hbd s hs)⟩
  · intro s hs
    have h := polar_decomposition (β := (0 : ℂ)) hab hU hsub hd hc hne hs
    rw [sub_zero] at h
    rwa [polarModulus_eq_norm hab hU hsub hd hc hne hs] at h
  · intro s hs
    have h := hasDerivAt_polarAngle (β := (0 : ℂ)) hU hsub hd hc hne hs
    simpa using h

/-- **A function whose derivative converges at an endpoint converges there too.**
A convergent derivative is bounded near the endpoint, so the function is
Lipschitz there; a real-valued Lipschitz function on a set extends Lipschitz to
the line (McShane, `LipschitzOnWith.extend_real`), and the extension is
continuous at the endpoint.  Nothing is asked *at* the endpoint, where `f` need
not be defined by the same formula.

The value of the limit is not named, because the derivative's limit does not
determine it — only its existence transfers.

**Do not reach for `FTBranchLimitPoint.tendsto_ftTau_slope_nhdsGT_zero` here.**
It gives `(τ - t_a)/θ → -t_a·cot(π/ρ)`, a limit of **difference quotients**, and
that is strictly weaker than `ftTauDeriv` converging: `x²sin(1/x)` is
differentiable at `0` and its derivative does not converge there.  Using it as
the `τ'` limit is a false step that **compiles**, and it is what a search for a
`τ`-limit finds first.  The route to `τ'` runs through `τ''` and this lemma,
never through the slope. -/
theorem exists_tendsto_of_tendsto_deriv {f f' : ℝ → ℝ} {b L : ℝ} (hb : 0 < b)
    (hd : ∀ x ∈ Ioo (0 : ℝ) b, HasDerivAt f (f' x) x)
    (hlim : Filter.Tendsto f' (nhdsWithin 0 (Ioi (0 : ℝ))) (nhds L)) :
    ∃ A : ℝ, Filter.Tendsto f (nhdsWithin 0 (Ioi (0 : ℝ))) (nhds A) := by
  classical
  -- a convergent derivative is bounded near the endpoint
  have hbd : ∀ᶠ x in nhdsWithin 0 (Ioi (0 : ℝ)), |f' x| ≤ |L| + 1 := by
    have h0 : Filter.Tendsto (fun x => |f' x - L|)
        (nhdsWithin 0 (Ioi (0 : ℝ))) (nhds 0) := by
      have hconst : Filter.Tendsto (fun _ : ℝ => L)
          (nhdsWithin 0 (Ioi (0 : ℝ))) (nhds L) := tendsto_const_nhds
      simpa using (hlim.sub hconst).abs
    filter_upwards [h0.eventually (eventually_lt_nhds one_pos)] with x hx
    have h := abs_sub_abs_le_abs_sub (f' x) L
    linarith
  obtain ⟨δ, hδ0, hδ⟩ := (nhdsGT_basis (0 : ℝ)).eventually_iff.1 hbd
  set c : ℝ := min δ b with hcdef
  have hc0 : (0 : ℝ) < c := lt_min hδ0 hb
  set K : NNReal := ⟨|L| + 1, by positivity⟩ with hK
  have hKc : ((K : NNReal) : ℝ) = |L| + 1 := rfl
  -- hence Lipschitz on `(0, c)`
  have hlip : LipschitzOnWith K f (Ioo (0 : ℝ) c) := by
    refine Convex.lipschitzOnWith_of_nnnorm_hasDerivWithin_le (f := f) (f' := f')
      (convex_Ioo (0 : ℝ) c)
      (fun x hx => (hd x ⟨hx.1, lt_of_lt_of_le hx.2 (min_le_right _ _)⟩).hasDerivWithinAt)
      (fun x hx => ?_)
    rw [← NNReal.coe_le_coe, coe_nnnorm, hKc]
    simpa [Real.norm_eq_abs] using
      hδ ⟨hx.1, lt_of_lt_of_le hx.2 (min_le_left _ _)⟩
  -- and a real-valued Lipschitz function extends
  obtain ⟨g, hgL, hgeq⟩ := hlip.extend_real
  refine ⟨g 0, ?_⟩
  have hcont : Filter.Tendsto g (nhdsWithin 0 (Ioi (0 : ℝ))) (nhds (g 0)) :=
    (hgL.continuous.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  refine hcont.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT hc0] with x hx
  exact (hgeq hx).symm

/-- **`τ''` alone.**  `exists_tendsto_of_tendsto_deriv` applied twice down the
chain `τ'' → τ' → τ`: a convergent `τ''` forces `τ'` to converge, and a
convergent `τ'` forces `τ`.  So the three real limits
`exists_ft_endpoint_phase_deriv_bound_of_tau_limits` takes are **one**.

The values are not named and are not needed — `tendsto_ftGammaDeriv2_of_tendsto`
quantifies over them, and the collar bound's conclusion mentions none of them. -/
theorem exists_tau_limits_of_tendsto_ftTauDeriv2 {n r l : ℕ} {a : Fin n → ℝ}
    (hn : 0 < n) (ha : ∀ k, 0 < a k) (hr : 1 ≤ r)
    (hbranch : ∀ θ ∈ Ioo (0 : ℝ) (Real.pi / r), FTBranchAt a r l θ)
    {D2 : ℝ} (hπr : (0 : ℝ) < Real.pi / r)
    (hτ2 : Filter.Tendsto (ftTauDeriv2 a r l) (nhdsWithin 0 (Ioi (0 : ℝ))) (nhds D2)) :
    ∃ T D : ℝ,
      Filter.Tendsto (ftTau a r l) (nhdsWithin 0 (Ioi (0 : ℝ))) (nhds T) ∧
      Filter.Tendsto (ftTauDeriv a r l) (nhdsWithin 0 (Ioi (0 : ℝ))) (nhds D) := by
  obtain ⟨D, hD⟩ := exists_tendsto_of_tendsto_deriv (b := Real.pi / r) hπr
    (fun x hx => hasDerivAt_ftTauDeriv hn ha hr hx hbranch) hτ2
  obtain ⟨T, hT⟩ := exists_tendsto_of_tendsto_deriv (b := Real.pi / r) hπr
    (fun x hx => hasDerivAt_ftTau hn ha hr hx hbranch) hD
  exact ⟨T, D, hT, hD⟩

/-- **The mixed second partials of the angle agree.**  `∂²θ_k/∂θ∂τ` and
`∂²θ_k/∂τ∂θ` are written differently in `BranchCurvature` — one carries
`cos(2θ_k - θ)` explicitly, the other a `2sinθ_k cosθ_k cos(θ_k - θ)` product —
and they are the same function.  The bridge is the sum-to-product identity
`cos(2θ_k - θ) + cos θ = 2cos θ_k cos(θ_k - θ)`, which is exactly the difference
between the two spellings.

`ftTauDeriv2` uses both, so the identity collapses two of its four second-order
sums into one.  It holds unconditionally, `sin θ = 0` included, where both sides
are `0` through Lean's division — the one place in this module where `x / 0 = 0`
is load-bearing in the *helpful* direction, and it is checked rather than
assumed. -/
theorem ftAngleDeriv2AngleTau_eq_ftAngleDeriv2TauAngle (a τ s : ℝ) :
    ftAngleDeriv2AngleTau a τ s = ftAngleDeriv2TauAngle a τ s := by
  rcases eq_or_ne (Real.sin s) 0 with hs | hs
  · simp [ftAngleDeriv2AngleTau, ftAngleDeriv2TauAngle, hs]
  · have hkey : Real.cos (2 * ftAngle a τ s - s)
        = 2 * Real.cos (ftAngle a τ s) * Real.cos (ftAngle a τ s - s) - Real.cos s := by
      have h := Real.cos_add_cos (2 * ftAngle a τ s - s) s
      have h1 : (2 * ftAngle a τ s - s + s) / 2 = ftAngle a τ s := by ring
      have h2 : (2 * ftAngle a τ s - s - s) / 2 = ftAngle a τ s - s := by ring
      rw [h1, h2] at h
      linarith
    rw [ftAngleDeriv2AngleTau, ftAngleDeriv2TauAngle, hkey]
    field_simp

/-- **`hbranch`'s first three clauses, for an arbitrary family, from one `κ`.**
`AngularDiscrepancyFT.FTPhaseSupply` is consumed through
`PhaseSupplyProducer.exists_ftPhaseSupply_of_dominance`, whose branch hypothesis
quantifies over an ordered family of blocks positioned anywhere in the arc and
asks three things of each: the polar decomposition, differentiability of the
phase, and `|dψ| < M+1`.  This produces all three from a single bound on
`Im(W'/W)` over the whole arc.

**The threshold is what one `κ` buys.**  `M₀ = ⌈κ⌉` is chosen before the family
is seen, so it does not move with the blocks, with their number, or with `M` —
which is why the clause is a condition on `M` rather than a growth claim.  A
per-block constant would reassemble only through a max over the family, and that
max grows with the family; this one does not exist.

**No choice is needed for `ψ`.**  The branch on block `i` is
`polarAngle W dW 0 (Lb i)` — a definable function of the index, base point
included — so the family is exhibited rather than chosen. Its derivative is
`Im(W'/W)`, which does not depend on `i` at all: the blocks share a derivative
and differ only in the additive constant their base point fixes.

`hne` is per block rather than global because `W` genuinely vanishes on the arc,
at the amplitude divisor; the blocks the caller supplies are those the divisor
misses. -/
theorem exists_phase_family_of_bound {W dW : ℝ → ℂ} {U : Set ℝ} {L κ : ℝ}
    (hU : IsOpen U) (hsub : Icc (0 : ℝ) L ⊆ U)
    (hd : ∀ s ∈ U, HasDerivAt W (dW s) s) (hc : ContinuousOn dW U)
    (hbd : ∀ s ∈ Icc (0 : ℝ) L, W s ≠ 0 → |(dW s / W s).im| ≤ κ) :
    ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M → ∀ (k : ℕ) (Lb Rb : Fin k → ℝ),
      (∀ i, Lb i ∈ Icc (0 : ℝ) L) → (∀ i, Rb i ∈ Icc (0 : ℝ) L) →
      (∀ i, Lb i < Rb i → ∀ θ ∈ Icc (Lb i) (Rb i), W θ ≠ 0) →
      ∃ ψ dψ : Fin k → ℝ → ℝ,
        (∀ i, Lb i < Rb i → ∀ θ ∈ Icc (Lb i) (Rb i),
          W θ = ((‖W θ‖ : ℝ) : ℂ) * Complex.exp ((ψ i θ : ℂ) * Complex.I)) ∧
        (∀ i, Lb i < Rb i → ∀ θ ∈ Icc (Lb i) (Rb i), HasDerivAt (ψ i) (dψ i θ) θ) ∧
        (∀ i, Lb i < Rb i → ∀ θ ∈ Icc (Lb i) (Rb i), |dψ i θ| < (M : ℝ) + 1) := by
  obtain ⟨M₀, hM₀⟩ := exists_threshold_of_bound (κ := κ)
  refine ⟨M₀, fun M hM k Lb Rb hL hR hne => ?_⟩
  refine ⟨fun i => polarAngle W dW 0 (Lb i), fun _ θ => (dW θ / W θ).im, ?_, ?_, ?_⟩
  all_goals
    intro i hi θ hθ
  -- every block sits inside the arc, hence inside the open set
  all_goals
    have hblk : Icc (Lb i) (Rb i) ⊆ Icc (0 : ℝ) L := fun x hx =>
      ⟨le_trans (hL i).1 hx.1, le_trans hx.2 (hR i).2⟩
  · have h := polar_decomposition (β := (0 : ℂ)) hi.le hU (hblk.trans hsub) hd hc
      (fun x hx => hne i hi x hx) hθ
    rw [sub_zero] at h
    rwa [polarModulus_eq_norm hi.le hU (hblk.trans hsub) hd hc
      (fun x hx => hne i hi x hx) hθ] at h
  · have h := hasDerivAt_polarAngle (β := (0 : ℂ)) hU (hblk.trans hsub) hd hc
      (fun x hx => hne i hi x hx) hθ
    simpa using h
  · exact hM₀ M hM _ (hbd θ (hblk hθ) (hne i hi θ hθ))

/-! ### The Forgács–Tran branch -/

/-- The principal branch of `thm:FT-geometry`, shifted so the endpoint sits at
the origin.  `endpointCofactor` divides by `δ`, so it wants `γ(0) = 0`; the
branch itself runs into `t_e`. -/
noncomputable def ftShiftedBranch {n : ℕ} (a : Fin n → ℝ) (r l : ℕ) (te : ℝ) (θ : ℝ) : ℂ :=
  ((ftTau a r l θ : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) - (te : ℂ)

/-- **`eq:phase-derivative-bound` on the collar, at the Forgács–Tran branch.**
Everything on the punctured collar is discharged from the tree's own lemmas —
`BranchCurvature.hasDerivAt_ftBranchGamma` and `hasDerivAt_ftGammaDeriv` for the
two derivatives, `BranchAmplitude.continuousAt_ftGammaDeriv2` for the continuity
— because all three hold on `Ioo 0 (π/r)` and the collar is taken inside it.

What is left is four facts *at* the endpoint and nothing else.  Three of them are
`Forgacs2017RationalDenominator` Prop. 3 in the shape `EndpointRegularity` and
`Amplitude` already carry it — the endpoint value, the one-sided derivative, and
its nonvanishing.  The fourth, `hlim2`, is the one genuinely new statement this
route needs: **`γ''` converges at the endpoint.**  Its value is not used, only
its existence.

`b < π/r` rather than `b ≤ π/r`: the branch lemmas hold on the open arc, and the
upper endpoint is a different degeneracy with its own exponent. -/
theorem exists_ft_endpoint_phase_deriv_bound {n r l : ℕ} {a : Fin n → ℝ}
    (hn : 0 < n) (ha : ∀ k, 0 < a k) (hr : 1 ≤ r)
    (hbranch : ∀ θ ∈ Ioo (0 : ℝ) (Real.pi / r), FTBranchAt a r l θ)
    {te b h : ℝ} {A : ℂ} {p : ℤ}
    (hb0 : 0 < b) (hblt : b < Real.pi / r) (hh : 0 ≤ h) (hp : p ≠ 0)
    (hγ0 : ftShiftedBranch a r l te 0 = 0)
    (hd0 : HasDerivWithinAt (ftShiftedBranch a r l te)
      (ftGammaDeriv a r l 0) (Ici (0 : ℝ)) 0)
    (hc : ContinuousWithinAt (ftGammaDeriv a r l) (Ici (0 : ℝ)) 0)
    (hlim2 : Filter.Tendsto (ftGammaDeriv2 a r l)
      (nhdsWithin 0 (Ioi (0 : ℝ))) (nhds A))
    (h0 : ftGammaDeriv a r l 0 ≠ 0) :
    ∃ b' κ : ℝ, 0 < b' ∧ b' ≤ b ∧ 0 ≤ κ ∧
      ∀ M : ℕ, ∀ θ ∈ Icc (h / M) b', θ ≠ 0 →
        |(deriv (fun s : ℝ => ((s ^ p : ℝ) : ℂ)
            * endpointCofactor (ftShiftedBranch a r l te) s) θ
            / (((θ ^ p : ℝ) : ℂ)
              * endpointCofactor (ftShiftedBranch a r l te) θ)).im| ≤ κ := by
  have harc : Ioc (0 : ℝ) b ⊆ Ioo (0 : ℝ) (Real.pi / r) :=
    fun θ hθ => ⟨hθ.1, lt_of_le_of_lt hθ.2 hblt⟩
  refine exists_endpoint_phase_deriv_bound_of_deriv2_limit
    (γ := ftShiftedBranch a r l te) (dγ := ftGammaDeriv a r l)
    (d2γ := ftGammaDeriv2 a r l) hb0 hh hp hγ0 hd0 ?_ hc ?_ ?_ hlim2 h0
  · exact fun θ hθ =>
      (hasDerivAt_ftBranchGamma hn ha hr (harc hθ) hbranch).sub_const _
  · exact fun θ hθ => hasDerivAt_ftGammaDeriv hn ha hr (harc hθ) hbranch
  · exact fun θ hθ =>
      (continuousAt_ftGammaDeriv2 hn ha hr (harc hθ) hbranch).continuousWithinAt

/-- **The collar bound at the Forgács–Tran branch, owing three real limits.**
`exists_ft_endpoint_phase_deriv_bound` with its one complex hypothesis
discharged by `tendsto_ftGammaDeriv2_of_tendsto`.

This is the end of what this module can reduce.  What the whole chain — from
`eq:phase-derivative-bound` on the collar back to the pencil — still rests on is
four facts at the endpoint: three are `Forgacs2017RationalDenominator` Prop. 3 in
the shape the tree already carries it, and the fourth is that `τ`, `τ'` and `τ''`
converge at `0⁺`.  No constant, no limit of a complex quantity, and nothing about
the branch's direction. -/
theorem exists_ft_endpoint_phase_deriv_bound_of_tau_limits {n r l : ℕ} {a : Fin n → ℝ}
    (hn : 0 < n) (ha : ∀ k, 0 < a k) (hr : 1 ≤ r)
    (hbranch : ∀ θ ∈ Ioo (0 : ℝ) (Real.pi / r), FTBranchAt a r l θ)
    {te b h T D D2 : ℝ} {p : ℤ}
    (hb0 : 0 < b) (hblt : b < Real.pi / r) (hh : 0 ≤ h) (hp : p ≠ 0)
    (hγ0 : ftShiftedBranch a r l te 0 = 0)
    (hd0 : HasDerivWithinAt (ftShiftedBranch a r l te)
      (ftGammaDeriv a r l 0) (Ici (0 : ℝ)) 0)
    (hc : ContinuousWithinAt (ftGammaDeriv a r l) (Ici (0 : ℝ)) 0)
    (hτ : Filter.Tendsto (ftTau a r l) (nhdsWithin 0 (Ioi (0 : ℝ))) (nhds T))
    (hτ1 : Filter.Tendsto (ftTauDeriv a r l) (nhdsWithin 0 (Ioi (0 : ℝ))) (nhds D))
    (hτ2 : Filter.Tendsto (ftTauDeriv2 a r l) (nhdsWithin 0 (Ioi (0 : ℝ))) (nhds D2))
    (h0 : ftGammaDeriv a r l 0 ≠ 0) :
    ∃ b' κ : ℝ, 0 < b' ∧ b' ≤ b ∧ 0 ≤ κ ∧
      ∀ M : ℕ, ∀ θ ∈ Icc (h / M) b', θ ≠ 0 →
        |(deriv (fun s : ℝ => ((s ^ p : ℝ) : ℂ)
            * endpointCofactor (ftShiftedBranch a r l te) s) θ
            / (((θ ^ p : ℝ) : ℂ)
              * endpointCofactor (ftShiftedBranch a r l te) θ)).im| ≤ κ :=
  exists_ft_endpoint_phase_deriv_bound hn ha hr hbranch hb0 hblt hh hp hγ0 hd0 hc
    (tendsto_ftGammaDeriv2_of_tendsto hτ hτ1 hτ2) h0

/-- **The collar bound at the Forgács–Tran branch, owing one real limit.**
`eq:phase-derivative-bound` on the collar, from the endpoint data
`Forgacs2017RationalDenominator` Prop. 3 supplies plus the single statement that
**`τ''` converges at `0⁺`**.

`hπr` is not a hypothesis: `0 < b < π/r` already gives it.

This is the end of the reduction.  Everything the chain rests on that the tree
does not already carry is one real limit, and its value is neither assumed nor
used. -/
theorem exists_ft_endpoint_phase_deriv_bound_of_tau2 {n r l : ℕ} {a : Fin n → ℝ}
    (hn : 0 < n) (ha : ∀ k, 0 < a k) (hr : 1 ≤ r)
    (hbranch : ∀ θ ∈ Ioo (0 : ℝ) (Real.pi / r), FTBranchAt a r l θ)
    {te b h D2 : ℝ} {p : ℤ}
    (hb0 : 0 < b) (hblt : b < Real.pi / r) (hh : 0 ≤ h) (hp : p ≠ 0)
    (hγ0 : ftShiftedBranch a r l te 0 = 0)
    (hd0 : HasDerivWithinAt (ftShiftedBranch a r l te)
      (ftGammaDeriv a r l 0) (Ici (0 : ℝ)) 0)
    (hc : ContinuousWithinAt (ftGammaDeriv a r l) (Ici (0 : ℝ)) 0)
    (hτ2 : Filter.Tendsto (ftTauDeriv2 a r l) (nhdsWithin 0 (Ioi (0 : ℝ))) (nhds D2))
    (h0 : ftGammaDeriv a r l 0 ≠ 0) :
    ∃ b' κ : ℝ, 0 < b' ∧ b' ≤ b ∧ 0 ≤ κ ∧
      ∀ M : ℕ, ∀ θ ∈ Icc (h / M) b', θ ≠ 0 →
        |(deriv (fun s : ℝ => ((s ^ p : ℝ) : ℂ)
            * endpointCofactor (ftShiftedBranch a r l te) s) θ
            / (((θ ^ p : ℝ) : ℂ)
              * endpointCofactor (ftShiftedBranch a r l te) θ)).im| ≤ κ := by
  obtain ⟨T, D, hT, hD⟩ := exists_tau_limits_of_tendsto_ftTauDeriv2 hn ha hr hbranch
    (lt_trans hb0 hblt) hτ2
  exact exists_ft_endpoint_phase_deriv_bound_of_tau_limits hn ha hr hbranch
    hb0 hblt hh hp hγ0 hd0 hc hT hD hτ2 h0

/-- **The collar bound from one-sided `C²` on the collar.**  The landing pad for
the analytic endpoint chart: `EndpointBranch.exists_endpoint_local_inverse` gives
an analytic `ψ` with `ψ'(0) ≠ 0`, so a branch written through that chart is `C²`
on the closed collar, and this turns that into `eq:phase-derivative-bound` with
no further endpoint analysis.

**One-sided, and `derivWithin` rather than `deriv`, because the branch has a
corner at the endpoint.**  `τ` is even in the angle, so the two one-sided
difference quotients at `δ = 0` are exact negatives; `deriv γ 0` does not exist
and a hypothesis naming it would be unmeetable.  `ContDiffOn ℝ 2 γ (Icc 0 B)`
asks only for the one-sided object, and every derivative below is taken within
that set — which agrees with `deriv` on the interior and is the only thing
defined at the endpoint.

**This shape is load-bearing, not a convenience form.**  Do not "strengthen" the
hypothesis to `ContDiffAt ℝ 2 γ 0`, and do not restate the conclusion's
`derivWithin` as `deriv`: for the branch itself those objects do not exist, so
the strengthened theorem would be about nothing — green, guardable, and empty at
the one point the corner needs.  It is the same unmeetable-hypothesis failure as
a limit that does not exist, and it is invisible in exactly the same way.  The
symmetry is the tell: an even dependence forces the two one-sided quotients to
disagree, so read the symmetry first and then ask which of the two objects the
boundary admits.

A chart may of course supply more than this asks — an analytic continuation in
the uniformizer is two-sided in *its* parameter — and a stronger input still
discharges the hypothesis.  What must not happen is the hypothesis itself being
raised to match it.

`b < B` so that the collar sits in the interior, where the within-derivatives are
genuine two-sided ones. -/
theorem exists_endpoint_phase_deriv_bound_of_contDiffOn {γ : ℝ → ℂ} {B b h : ℝ}
    {p : ℤ} (hB : 0 < B) (hb0 : 0 < b) (hbB : b < B) (hh : 0 ≤ h) (hp : p ≠ 0)
    (hγ0 : γ 0 = 0) (hγ2 : ContDiffOn ℝ 2 γ (Icc (0 : ℝ) B))
    (h0 : derivWithin γ (Icc (0 : ℝ) B) 0 ≠ 0) :
    ∃ b' κ : ℝ, 0 < b' ∧ b' ≤ b ∧ 0 ≤ κ ∧
      ∀ M : ℕ, ∀ θ ∈ Icc (h / M) b', θ ≠ 0 →
        |(deriv (fun s : ℝ => ((s ^ p : ℝ) : ℂ) * endpointCofactor γ s) θ
            / (((θ ^ p : ℝ) : ℂ) * endpointCofactor γ θ)).im| ≤ κ := by
  have hu : UniqueDiffOn ℝ (Icc (0 : ℝ) B) := uniqueDiffOn_Icc hB
  have hd1 : ContDiffOn ℝ 1 (derivWithin γ (Icc (0 : ℝ) B)) (Icc (0 : ℝ) B) :=
    hγ2.derivWithin hu (by norm_num)
  have hcont2 : ContinuousOn
      (derivWithin (derivWithin γ (Icc (0 : ℝ) B)) (Icc (0 : ℝ) B)) (Icc (0 : ℝ) B) :=
    hd1.continuousOn_derivWithin hu le_rfl
  have hzero : (0 : ℝ) ∈ Icc (0 : ℝ) B := ⟨le_rfl, hB.le⟩
  -- the collar sits in the interior, where `derivWithin` is `deriv`
  have hmem : ∀ θ ∈ Ioc (0 : ℝ) b, Icc (0 : ℝ) B ∈ nhds θ := fun θ hθ =>
    Icc_mem_nhds hθ.1 (lt_of_le_of_lt hθ.2 hbB)
  have hsub : ∀ θ ∈ Ioc (0 : ℝ) b, θ ∈ Icc (0 : ℝ) B := fun θ hθ =>
    ⟨hθ.1.le, le_of_lt (lt_of_le_of_lt hθ.2 hbB)⟩
  -- `Icc 0 B` is a neighbourhood of the endpoint within each one-sided filter
  have hIci : Icc (0 : ℝ) B ∈ nhdsWithin 0 (Ici (0 : ℝ)) := by
    refine mem_nhdsWithin.2 ⟨Iio B, isOpen_Iio, hB, ?_⟩
    rintro x ⟨hxB, hx0⟩
    exact ⟨hx0, le_of_lt hxB⟩
  have hIoi : Icc (0 : ℝ) B ∈ nhdsWithin 0 (Ioi (0 : ℝ)) :=
    Filter.mem_of_superset (Ioo_mem_nhdsGT hB) Ioo_subset_Icc_self
  refine exists_endpoint_phase_deriv_bound_of_deriv2_limit
    (γ := γ) (dγ := derivWithin γ (Icc (0 : ℝ) B))
    (d2γ := derivWithin (derivWithin γ (Icc (0 : ℝ) B)) (Icc (0 : ℝ) B))
    (b := b) (A := derivWithin (derivWithin γ (Icc (0 : ℝ) B)) (Icc (0 : ℝ) B) 0)
    hb0 hh hp hγ0 ?_ ?_ ?_ ?_ ?_ ?_ h0
  · exact ((hγ2.differentiableOn (by norm_num) 0 hzero).hasDerivWithinAt).mono_of_mem_nhdsWithin
      hIci
  · intro θ hθ
    have hdiff : DifferentiableAt ℝ γ θ :=
      (hγ2.differentiableOn (by norm_num) θ (hsub θ hθ)).differentiableAt (hmem θ hθ)
    rw [derivWithin_of_mem_nhds (hmem θ hθ)]
    exact hdiff.hasDerivAt
  · exact (hd1.continuousOn 0 hzero).mono_of_mem_nhdsWithin hIci
  · intro θ hθ
    have hdiff : DifferentiableAt ℝ (derivWithin γ (Icc (0 : ℝ) B)) θ :=
      (hd1.differentiableOn (by norm_num) θ (hsub θ hθ)).differentiableAt (hmem θ hθ)
    rw [derivWithin_of_mem_nhds (hmem θ hθ)]
    exact hdiff.hasDerivAt
  · exact hcont2.mono (fun x hx => hsub x hx)
  · exact (hcont2 0 hzero).mono_of_mem_nhdsWithin
      (Filter.mem_of_superset hIoi (fun _ hx => hx))

/-- **The collar bound through a chart, `γ = F ∘ v`.**  The endpoint chart writes
the branch as an analytic function of a uniformizer, so what a caller holds is
not `γ`'s regularity directly but a composition: `F` twice differentiable at the
chart point and `v` twice differentiable at the endpoint.  This composes them and
lands on `exists_endpoint_phase_deriv_bound_of_contDiffOn`.

The collar is shrunk to fit the chart's own neighbourhood, which is why `b'` is
existential and only `b' ≤ b` is promised — a chart valid on a small disc cannot
certify a collar larger than itself, and silently keeping the caller's `b` would
be the error. -/
theorem exists_endpoint_phase_deriv_bound_of_comp {F : ℝ → ℂ} {v : ℝ → ℝ} {b h : ℝ}
    {p : ℤ} (hb0 : 0 < b) (hh : 0 ≤ h) (hp : p ≠ 0) (hγ0 : F (v 0) = 0)
    (hF : ContDiffAt ℝ 2 F (v 0)) (hv : ContDiffAt ℝ 2 v 0)
    (h0 : deriv (fun θ => F (v θ)) 0 ≠ 0) :
    ∃ b' κ : ℝ, 0 < b' ∧ b' ≤ b ∧ 0 ≤ κ ∧
      ∀ M : ℕ, ∀ θ ∈ Icc (h / M) b', θ ≠ 0 →
        |(deriv (fun s : ℝ => ((s ^ p : ℝ) : ℂ)
            * endpointCofactor (fun t => F (v t)) s) θ
            / (((θ ^ p : ℝ) : ℂ)
              * endpointCofactor (fun t => F (v t)) θ)).im| ≤ κ := by
  have hcomp : ContDiffAt ℝ 2 (fun θ => F (v θ)) 0 := hF.comp 0 hv
  obtain ⟨u, hu, hcon⟩ := hcomp.contDiffOn (le_refl 2) (by simp)
  obtain ⟨ε, hε, hεu⟩ := Metric.mem_nhds_iff.1 hu
  have hB : (0 : ℝ) < ε / 2 := by positivity
  have hsubB : Icc (0 : ℝ) (ε / 2) ⊆ u := by
    intro x hx
    refine hεu ?_
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg hx.1]
    exact lt_of_le_of_lt hx.2 (by linarith)
  have hγ2 : ContDiffOn ℝ 2 (fun θ => F (v θ)) (Icc (0 : ℝ) (ε / 2)) := hcon.mono hsubB
  -- the collar is the smaller of the caller's and the chart's
  have hb₂0 : (0 : ℝ) < min b (ε / 4) := lt_min hb0 (by positivity)
  have hb₂B : min b (ε / 4) < ε / 2 :=
    lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hdw : derivWithin (fun θ => F (v θ)) (Icc (0 : ℝ) (ε / 2)) 0
      = deriv (fun θ => F (v θ)) 0 :=
    (hcomp.differentiableAt (by norm_num)).derivWithin
      (uniqueDiffOn_Icc hB 0 ⟨le_rfl, hB.le⟩)
  obtain ⟨b', κ, hb'0, hb'b, hκ0, hκ⟩ :=
    exists_endpoint_phase_deriv_bound_of_contDiffOn (γ := fun θ => F (v θ))
      (B := ε / 2) (b := min b (ε / 4)) (h := h) (p := p)
      hB hb₂0 hb₂B hh hp hγ0 hγ2 (by rw [hdw]; exact h0)
  exact ⟨b', κ, hb'0, le_trans hb'b (min_le_left _ _), hκ0, hκ⟩

/-- **A `C²` angle map with nonvanishing derivative inverts, `C²`.**  This is the
step the endpoint chart needs: the chart is analytic in its own uniformizer `v`,
and the arc is parameterized by the angle, so passing between them is an
inversion of `Θ : v ↦ θ`.

Transversality — `Θ'(0) ≠ 0` — is the whole hypothesis, and at the endpoint it is
structural rather than measured: `Θ'(0) = ‖ψ'(0)‖·sin(π/k)/t_e`, nonzero for
every collision order `k ≥ 2` because `sin(π/k) ≠ 0` on `0 < π/k ≤ π/2`.

**Two things about picking the root, both of which have been got wrong.**  The
`k` roots of unity give `k` chart branches, and the physical one sits at argument
`π - π/k`; the branches that fail to invert are exactly those at argument `0` or
`π`, the real ones, where `Θ'(0) = 0`.  At `k = 3` one of the three *is* real, so
a root chosen for convenience gives a plausible nonzero `Θ'(0)` while naming the
wrong branch — at exactly the collision order the tree's own witness sits at.
And `γ'(0⁺) = i·t_e` is the `k = 2` **special case**, not the law: in general
`γ'(0)/t_e = -cot(π/k) + i`, and using the special case to pick the root fails
outright at `k = 3`, where no cube root of unity puts `ω ψ'(0)` on the imaginary
axis at all. -/
theorem exists_contDiffAt_local_inverse {Θ : ℝ → ℝ} {c : ℝ}
    (hΘ : ContDiffAt ℝ 2 Θ 0) (hd : HasDerivAt Θ c 0) (hc : c ≠ 0) :
    ∃ v : ℝ → ℝ, ContDiffAt ℝ 2 v (Θ 0) ∧ v (Θ 0) = 0 ∧
      HasDerivAt v c⁻¹ (Θ 0) ∧ (∀ᶠ x in nhds (0 : ℝ), v (Θ x) = x) := by
  have hfd : HasFDerivAt Θ
      ((ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 c hc) : ℝ →L[ℝ] ℝ)) 0 :=
    hd.hasFDerivAt_equiv hc
  have hn : (2 : WithTop ℕ∞) ≠ 0 := by norm_num
  have hstrict := hΘ.hasStrictFDerivAt' hfd hn
  have hleft : ∀ᶠ x in nhds (0 : ℝ),
      hΘ.localInverse hfd hn (Θ x) = x := hstrict.eventually_left_inverse
  have hsd : HasStrictDerivAt Θ c 0 := hΘ.hasStrictFDerivAt' hd.hasFDerivAt hn
  exact ⟨hΘ.localInverse hfd hn, hΘ.to_localInverse hfd hn,
    hΘ.localInverse_apply_image hfd hn,
    (hsd.to_local_left_inverse hc hleft).hasDerivAt, hleft⟩

/-- **`eq:phase-derivative-bound` on the collar, from the endpoint chart alone.**
The chart supplies an analytic `F` in its uniformizer and an angle map `Θ` with
`Θ'(0) ≠ 0`; this inverts `Θ`, reparameterizes the branch by the angle, and
lands the collar bound on it.  No limit, no rate, no cancellation, and nothing
measured — the transversality that makes it run is `sin(π/k) ≠ 0`.

The branch is returned as `F ∘ v` together with `v`'s defining property
`v ∘ Θ = id` near `0`, rather than being taken as a hypothesis, because the
reparameterization is what the theorem produces: a caller identifies its own
branch with `F ∘ v` through that property.

**`ContDiffAt` is legitimate for `v` and `F` here and would not be for the arc's
own `γ`.**  The chart is two-sided in *its* parameter — an analytic continuation
in the uniformizer, not the physical branch reflected — so nothing here asks the
arc for a two-sided derivative at the endpoint, which it does not have.  The
collar bound this lands on still takes only the one-sided hypothesis. -/
theorem exists_endpoint_phase_deriv_bound_of_chart {F : ℝ → ℂ} {Θ : ℝ → ℝ}
    {c b h : ℝ} {p : ℤ} (hb0 : 0 < b) (hh : 0 ≤ h) (hp : p ≠ 0)
    (hΘ0 : Θ 0 = 0) (hΘ : ContDiffAt ℝ 2 Θ 0) (hd : HasDerivAt Θ c 0) (hc : c ≠ 0)
    (hF : ContDiffAt ℝ 2 F 0) (hF0 : F 0 = 0) (hFd : deriv F 0 ≠ 0) :
    ∃ (v : ℝ → ℝ) (b' κ : ℝ), ContDiffAt ℝ 2 v 0 ∧ v 0 = 0 ∧
      (∀ᶠ x in nhds (0 : ℝ), v (Θ x) = x) ∧
      0 < b' ∧ b' ≤ b ∧ 0 ≤ κ ∧
      ∀ M : ℕ, ∀ θ ∈ Icc (h / M) b', θ ≠ 0 →
        |(deriv (fun s : ℝ => ((s ^ p : ℝ) : ℂ)
            * endpointCofactor (fun t => F (v t)) s) θ
            / (((θ ^ p : ℝ) : ℂ)
              * endpointCofactor (fun t => F (v t)) θ)).im| ≤ κ := by
  obtain ⟨v, hv2, hv0, hvd, hvleft⟩ := exists_contDiffAt_local_inverse hΘ hd hc
  rw [hΘ0] at hv2 hv0 hvd
  have hFdd : HasDerivAt F (deriv F 0) 0 := (hF.differentiableAt (by norm_num)).hasDerivAt
  have hv00 : v 0 = 0 := hv0
  -- the outer map lands in `ℂ` while the inner is real, so this is the scalar
  -- chain rule and the derivative comes out as a smul rather than a product
  have hchain : HasDerivAt (fun θ => F (v θ)) (c⁻¹ • deriv F 0) 0 :=
    HasDerivAt.scomp (x := 0) (by rw [hv00]; exact hFdd) hvd
  have h0 : deriv (fun θ => F (v θ)) 0 ≠ 0 := by
    rw [hchain.deriv]
    exact smul_ne_zero (inv_ne_zero hc) hFd
  obtain ⟨b', κ, hb'0, hb'b, hκ0, hκ⟩ :=
    exists_endpoint_phase_deriv_bound_of_comp (F := F) (v := v) (b := b) (h := h)
      (p := p) hb0 hh hp (by rw [hv00]; exact hF0) (by rw [hv00]; exact hF) hv2 h0
  exact ⟨v, b', κ, hv2, hv00, hvleft, hb'0, hb'b, hκ0, hκ⟩

/-- **The chart, restricted to a real ray, is `C²`.**  `EndpointBranch` produces
`ψ` analytic on a complex neighbourhood of `0`; the arc runs along `ω·x` for real
`x` and one `k`-th root of unity `ω`, so what
`exists_endpoint_phase_deriv_bound_of_chart` wants is the real restriction.
Analyticity gives `C^∞` over `ℂ`, restriction of scalars gives it over `ℝ`, and
the ray is `ℝ`-linear.

The shift by `ψ 0` is what makes `F 0 = 0`, which `endpointCofactor` needs
because it divides by the parameter. -/
theorem contDiffAt_chart_ray {ψ : ℂ → ℂ} (ω : ℂ) (h : AnalyticAt ℂ ψ 0) :
    ContDiffAt ℝ 2 (fun x : ℝ => ψ (ω * (x : ℂ)) - ψ 0) 0 := by
  have hray : ContDiff ℝ 2 (fun x : ℝ => ω * (x : ℂ)) :=
    contDiff_const.mul Complex.ofRealCLM.contDiff
  have hψ : ContDiffAt ℝ 2 ψ (ω * ((0 : ℝ) : ℂ)) := by
    have h0 : ω * ((0 : ℝ) : ℂ) = 0 := by simp
    rw [h0]
    exact (h.contDiffAt.restrict_scalars ℝ).of_le le_top
  have hcomp : ContDiffAt ℝ 2 (fun x : ℝ => ψ (ω * (x : ℂ))) 0 :=
    ContDiffAt.comp 0 hψ hray.contDiffAt
  exact hcomp.sub contDiffAt_const

/-- **The angle map is `C²`.**  `exists_endpoint_phase_deriv_bound_of_chart` wants
`Θ : v ↦ θ` twice differentiable, and along the chart the angle is a branch of
`arg` of a nonvanishing `C¹` curve.

**The branch is `ViewingAngle.polarAngle`, not `Complex.arg`.**  Mathlib carries
no smoothness for `Complex.arg` — it has a cut, and the statement would be false
across it — whereas `polarAngle` is built by integration and
`hasDerivAt_polarAngle` gives its derivative as `Im(G'/G)` with no cut anywhere.
That derivative is `C¹` wherever `G` is `C¹` and nonvanishing, so `Θ` is `C²`;
the chart supplies both, since `ψ` is analytic and `ψ(0) = t_e ≠ 0`. -/
theorem contDiffAt_polarAngle {G dG : ℝ → ℂ} {r : ℝ} (hr : 0 < r)
    (hd : ∀ s ∈ Ioo (-r) r, HasDerivAt G (dG s) s)
    (hc : ContinuousOn dG (Ioo (-r) r))
    (hne : ∀ s ∈ Ioo (-r) r, G s ≠ 0)
    (hG1 : ContDiffAt ℝ 1 G 0) (hdG : ContDiffAt ℝ 1 dG 0) :
    ContDiffAt ℝ 2 (polarAngle G dG 0 (-(r / 2))) 0 := by
  have h0mem : (0 : ℝ) ∈ Ioo (-r) r := ⟨by linarith, hr⟩
  have hG0 : G 0 ≠ 0 := hne 0 h0mem
  have hsub : Icc (-(r / 2)) (r / 2) ⊆ Ioo (-r) r := fun x hx =>
    ⟨by linarith [hx.1], by linarith [hx.2]⟩
  -- the derivative `Im(G'/G)` is `C¹`
  have hq : ContDiffAt ℝ 1 (fun s => (dG s / G s).im) 0 := by
    have hquot : ContDiffAt ℝ 1 (fun s => dG s * (G s)⁻¹) 0 := hdG.mul (hG1.inv hG0)
    have heq : (fun s : ℝ => (dG s / G s).im)
        = (⇑Complex.imCLM ∘ fun s : ℝ => dG s * (G s)⁻¹) := by
      funext s
      simp [Function.comp, Complex.imCLM_apply, div_eq_mul_inv]
    rw [heq]
    exact Complex.imCLM.contDiff.comp_contDiffAt (0 : ℝ) hquot
  have hf' : ContDiffAt ℝ 1
      (fun s => (ContinuousLinearMap.smulRightL ℝ ℝ ℝ 1) ((dG s / G s).im)) 0 :=
    (ContinuousLinearMap.smulRightL ℝ ℝ ℝ 1).contDiff.comp_contDiffAt 0 hq
  rw [show (2 : WithTop ℕ∞) = ((1 : ℕ) : WithTop ℕ∞) + 1 by norm_num,
    contDiffAt_succ_iff_hasFDerivAt]
  refine ⟨fun s => (ContinuousLinearMap.smulRightL ℝ ℝ ℝ 1) ((dG s / G s).im),
    ⟨Ioo (-(r / 2)) (r / 2),
      Ioo_mem_nhds (by linarith) (by linarith), fun s hs => ?_⟩, hf'⟩
  -- the two spellings of "multiply by a scalar" as a map `ℝ →L[ℝ] ℝ`
  have hEq : (ContinuousLinearMap.smulRightL ℝ ℝ ℝ 1) ((dG s / G s).im)
      = ContinuousLinearMap.toSpanSingleton ℝ ((dG s / (G s - 0)).im) := by
    rw [sub_zero]
    ext
    simp [ContinuousLinearMap.smulRightL, ContinuousLinearMap.toSpanSingleton, mul_comm]
  change HasFDerivAt _ ((ContinuousLinearMap.smulRightL ℝ ℝ ℝ 1) ((dG s / G s).im)) s
  rw [hEq]
  exact (hasDerivAt_polarAngle (β := (0 : ℂ)) isOpen_Ioo hsub hd hc
    (fun x hx => hne x (hsub hx)) ⟨hs.1.le, hs.2.le⟩).hasFDerivAt

/-! ### The same divided difference at an interior center -/

/-- The divided difference of the branch about an interior parameter.  This is
`endpointCofactor` translated: `eq:W-local-zero`'s cofactor is built from it at
`θ₀` exactly as `eq:W-endpoint-form`'s is built from `endpointCofactor` at the
endpoint. -/
noncomputable def centeredCofactor (γ : ℝ → ℂ) (θ₀ θ : ℝ) : ℂ :=
  (γ θ - γ θ₀) / ((θ : ℂ) - (θ₀ : ℂ))

/-- Its derivative, by the quotient rule, off the center. -/
noncomputable def centeredCofactorDeriv (γ dγ : ℝ → ℂ) (θ₀ θ : ℝ) : ℂ :=
  (dγ θ * ((θ : ℂ) - (θ₀ : ℂ)) - (γ θ - γ θ₀)) / ((θ : ℂ) - (θ₀ : ℂ)) ^ 2

private theorem centeredCofactor_translate (γ : ℝ → ℂ) (θ₀ s : ℝ) :
    centeredCofactor γ θ₀ (s + θ₀)
      = endpointCofactor (fun t : ℝ => γ (t + θ₀) - γ θ₀) s := by
  simp [centeredCofactor, endpointCofactor]

/-- **`eq:W-local-zero`'s cofactor bound, at an interior center.**  The interior's
`hloc` needs `|Im(W'/W)|` **bounded** near each amplitude zero, not continuous
there — so the divided difference needs a bounded logarithmic derivative off the
center and nothing at it.

That is the endpoint statement translated, and it is worth saying why the
translation is the whole proof: the estimate never used where the center sat.
It used `γ(θ₀) = 0` after shifting, `γ'` Lipschitz against its value at the
center, and `γ'(θ₀) ≠ 0` — all position-free.

**So the interior does not need a `C¹` cofactor and does not need a second-order
Taylor expansion at the center.**  Reading `eq:W-local-zero` as wanting a
differentiable `U` at `θ₀` asks for a Peano remainder; reading it as wanting a
*bound* asks only for `γ'` Lipschitz, which on the interior follows from the
`γ''` the tree already proves.  This is the same distinction that closed the
endpoint, one center over. -/
theorem exists_bound_im_centeredCofactor_logDeriv {γ dγ : ℝ → ℂ} {θ₀ b L : ℝ}
    (hb : 0 < b) (hL : 0 ≤ L)
    (hd0 : HasDerivAt γ (dγ θ₀) θ₀)
    (hd : ∀ θ ∈ Ioc θ₀ (θ₀ + b), HasDerivAt γ (dγ θ) θ)
    (hlip : ∀ θ ∈ Icc θ₀ (θ₀ + b), ‖dγ θ - dγ θ₀‖ ≤ L * (θ - θ₀))
    (h0 : dγ θ₀ ≠ 0) :
    ∃ b' : ℝ, 0 < b' ∧ b' ≤ b ∧
      ∀ θ ∈ Icc θ₀ (θ₀ + b'), θ ≠ θ₀ →
        |(centeredCofactorDeriv γ dγ θ₀ θ / centeredCofactor γ θ₀ θ).im|
          ≤ 3 * L / ‖dγ θ₀‖ := by
  set g : ℝ → ℂ := fun t : ℝ => γ (t + θ₀) - γ θ₀ with hgdef
  set dg : ℝ → ℂ := fun t : ℝ => dγ (t + θ₀) with hdgdef
  have hg0 : g 0 = 0 := by simp [hgdef]
  have hdg0 : dg 0 = dγ θ₀ := by simp [hdgdef]
  -- at an INTERIOR center the branch is two-sided differentiable; the one-sided
  -- binder at the endpoint was about the endpoint, not about this estimate
  have hgd0 : HasDerivWithinAt g (dg 0) (Ici (0 : ℝ)) 0 := by
    rw [hdg0]
    have hcomp : HasDerivAt (fun u : ℝ => γ (u + θ₀)) (dγ θ₀) 0 :=
      HasDerivAt.comp_add_const (0 : ℝ) θ₀ (by simpa using hd0)
    simpa [hgdef] using (hcomp.sub_const (γ θ₀)).hasDerivWithinAt
  have hgd : ∀ t ∈ Ioc (0 : ℝ) b, HasDerivAt g (dg t) t := by
    intro t ht
    have hmem : t + θ₀ ∈ Ioc θ₀ (θ₀ + b) := by
      constructor <;> [linarith [ht.1]; linarith [ht.2]]
    have hcomp : HasDerivAt (fun u : ℝ => γ (u + θ₀)) (dγ (t + θ₀)) t :=
      HasDerivAt.comp_add_const t θ₀ (hd _ hmem)
    simpa [hgdef, hdgdef] using hcomp.sub_const (γ θ₀)
  have hglip : ∀ t ∈ Icc (0 : ℝ) b, ‖dg t - dg 0‖ ≤ L * t := by
    intro t ht
    have hmem : t + θ₀ ∈ Icc θ₀ (θ₀ + b) := by
      constructor <;> [linarith [ht.1]; linarith [ht.2]]
    have := hlip _ hmem
    simpa [hdgdef, hdg0] using this
  obtain ⟨b', hb'0, hb'b, -, -, hbd⟩ :=
    exists_bound_im_endpointCofactor_logDeriv hb hL hg0 hgd0 hgd hglip (by rwa [hdg0])
  refine ⟨b', hb'0, hb'b, fun θ hθ hθ0 => ?_⟩
  have hmem : θ - θ₀ ∈ Icc (0 : ℝ) b' := by
    constructor <;> [linarith [hθ.1]; linarith [hθ.2]]
  have hne : θ - θ₀ ≠ 0 := sub_ne_zero.2 hθ0
  have hkey := hbd (θ - θ₀) hmem hne
  rw [hdg0] at hkey
  have heq₁ : centeredCofactor γ θ₀ θ = endpointCofactor g (θ - θ₀) := by
    have := centeredCofactor_translate γ θ₀ (θ - θ₀)
    rwa [sub_add_cancel] at this
  have heq₂ : centeredCofactorDeriv γ dγ θ₀ θ = endpointCofactorDeriv g dg (θ - θ₀) := by
    simp [centeredCofactorDeriv, endpointCofactorDeriv, hgdef, hdgdef, Complex.ofReal_sub]
  rw [heq₁, heq₂]
  exact hkey

/-! ### The hypotheses are meetable -/

/-- A branch meeting every hypothesis of `exists_endpoint_phase_deriv_bound_zpow`
with `L` genuinely positive.  An affine `γ` would discharge the Lipschitz binder
at `L = 0`, which is the wrong reason — it would say nothing about whether a
moving `γ'` can meet it. -/
private noncomputable def witnessGamma (s : ℝ) : ℂ := (s : ℂ) + (s : ℂ) ^ 2 * I

private noncomputable def witnessGammaDeriv (s : ℝ) : ℂ := 1 + 2 * (s : ℂ) * I

private theorem hasDerivAt_witnessGamma (s : ℝ) :
    HasDerivAt witnessGamma (witnessGammaDeriv s) s := by
  have hsq : HasDerivAt (fun t : ℝ => (t : ℂ) ^ 2) (2 * (s : ℂ) ^ 1 * 1) s :=
    (hasDerivAt_ofReal s).pow 2
  have h := (hasDerivAt_ofReal s).add (hsq.mul_const I)
  have heq : (1 : ℂ) + 2 * (s : ℂ) ^ 1 * 1 * I = witnessGammaDeriv s := by
    simp [witnessGammaDeriv]
  rw [heq] at h
  exact h

/-- **The binder bundle is simultaneously satisfiable.**  Every hypothesis of
`exists_endpoint_phase_deriv_bound_zpow` is discharged at `witnessGamma`, so the
theorem is not vacuous through an unmeetable hypothesis — the failure mode in
which a bound is stated at a regularity no branch has, and nothing in the build
notices because a stronger hypothesis only makes a theorem harder to apply.

`L = 2` is sharp here: `‖γ'(δ) - γ'(0)‖ = 2δ` with equality, so the Lipschitz
binder is met by an estimate that is doing work rather than by a slack one. -/
theorem exists_endpoint_phase_deriv_bound_witness :
    ∃ b' κ : ℝ, 0 < b' ∧ b' ≤ 1 ∧ 0 ≤ κ ∧
      ∀ M : ℕ, ∀ θ ∈ Icc ((1 : ℝ) / M) b', θ ≠ 0 →
        |(deriv (fun s : ℝ => ((s ^ (1 : ℤ) : ℝ) : ℂ) * endpointCofactor witnessGamma s) θ
            / (((θ ^ (1 : ℤ) : ℝ) : ℂ) * endpointCofactor witnessGamma θ)).im| ≤ κ := by
  refine exists_endpoint_phase_deriv_bound_zpow (γ := witnessGamma)
    (dγ := witnessGammaDeriv) (b := 1) (L := 2) (h := 1) (p := 1)
    one_pos (by norm_num) zero_le_one one_ne_zero ?_ ?_ ?_ ?_ ?_
  · simp [witnessGamma]
  · exact (hasDerivAt_witnessGamma 0).hasDerivWithinAt
  · exact fun θ _ => hasDerivAt_witnessGamma θ
  · intro θ hθ
    have : witnessGammaDeriv θ - witnessGammaDeriv 0 = 2 * (θ : ℂ) * I := by
      simp [witnessGammaDeriv]
    rw [this, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hθ.1]
    norm_num
  · simp [witnessGammaDeriv]

end ForgacsTran
