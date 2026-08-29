/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import ForgacsTran.EndpointUpperOne
import ForgacsTran.EndpointUpperGap
import ForgacsTran.PrincipalSimpleBranch
import ForgacsTran.PencilIndex

/-!
# The upper endpoint's contour bound and amplitude floor at `r = 1`

`thm:weighted-dominance` takes its upper endpoint through two binders that do not
mention the retained cluster: `hCbd₁`, a bound on `B/D` over a fixed circle, and
`hamp₁`, a floor `A_1\eta^{p_1}` under the principal amplitude.  At `2 \le r` both
come off the collapse of the arc into the origin, and
`EndpointUpperGap.exists_upper_contour_bound` and
`EndpointUpperPackage.exists_upper_amplitude_floor` are those proofs.  Neither
survives at `r = 1`, and in opposite directions.

A third fact falls out of the first: the non-vanishing the contour bound records
on its circle is what the retained set needs there too, so `hCbd₁`'s circle and
`haR₁`/`huniq₁`'s are the same circle by construction rather than by coincidence.

**The contour bound.**  At `2 \le r` the spectral parameter is unbounded, and the
circle is justified by `zt^r` dominating `Q` on it —
`EndpointSeparation`'s upper circle is conditioned on `ftUpperWindow \le \|z\|`.
At `r = 1` the parameter tends to a finite limit, so that condition is cleared by
no constant whatever, and the route is not merely inconvenient but unavailable.
What replaces it is the limit itself: `D(\cdot, z(\pi - \delta))` converges
uniformly on any fixed circle to the limiting pencil `D_b`, so a circle carrying
no zero of `D_b` carries a bound.  The bounded parameter is the hypothesis, not
the obstruction.

**The amplitude floor.**  At `2 \le r` the principal point runs into the origin,
`B` and `E` are both nonzero there, and the amplitude vanishes to first order —
`p_1 = 1`.  At `r = 1` the principal point runs into `-L`, where `D_b` has the
double root `EndpointUpperOne` establishes, so `\partial_tD` vanishes in the limit
and the amplitude — a residue with that in its denominator — **diverges**.  So the
floor is a *constant*, `p_1 = 0`, and `\eta` does not appear.

**Both claims are scoped by where `B` sits, and the scope is `ord_{-L}(B)`.**  The
exponent is `ord_{-L}(B) - 1`, measured at `m = 0, 1, 2` in
`scripts/check_upper_amplitude_b_vanishing.py`:

* `m = 0` — the amplitude diverges at rate `\eta^{-1}`, `p_1 = 0` holds, and
  `p_1 = 1` is then the wrong statement rather than a weaker one, because it is
  satisfied by an amplitude that vanishes and nothing vanishes.
* `m = 1` — the amplitude tends to a finite nonzero limit.  `p_1 = 0` still holds,
  and nothing smaller is available.
* `m \ge 2` — the amplitude vanishes, `p_1 = 0` is **false**, and the binder needs
  `A_1\eta^{m-1}`: the `2 \le r` endpoint's shape, arriving here for an unrelated
  reason.

**`ord_{-L}(E)` never appears in that exponent, and the reason is not that it was
neglected.**  Read through `eq:W-on-g`, `\mathcal{W} = -tB(t)/E(t)`, the order is
`ord_{-L}(B) - ord_{-L}(E)`, so the `-1` is the assertion that `E` has a SIMPLE
zero at the collision.  It does: `E' = XQ''` at `r = 1`, so `E'(-L) = (-L)Q''(-L)`,
nonzero because `Q''` is a sum of positive terms on the negative axis.  That is the
**same** positivity that makes the pencil's own root at `-L` exactly double rather
than triple — `EndpointUpperOne.eval_derivative_two_ftRootPolyReal_pos` serves
both.  One fact settling the pencil's multiplicity and the amplitude's order is a
shared cause rather than a coincidence, and
`rootMultiplicity_ftCritical_endpoint_pi_eq_one` is where it is spent the second
time.

So `p_1 = 0` is exactly the `ord_{-L}(B) \le 1` statement, which is what the floor
below is proved under; `EndpointUpperMultiplicity` carries `p_1 = ord_{-L}(B) - 1`
at every `m`, which is what the corners consume.  `p_1 = 0` is also the strongest
the binder's `p_1 : ℕ` shape admits at `m = 0`, where the true rate `\eta^{-1}`
cannot be stated in it at all.

## Main statements

* `exists_endpoint_limits_pi` — the endpoint's limits under one `L`: the radius,
  the critical relation, and the spectral parameter with its value visible.
* `sum_div_add_eq_of_eval_ftCriticalReal_neg` — the deficit equation
  `∑_k L/(a_k+L) = r` from `E(-L) = 0`, at every `r`.  This was an undischarged
  input at both ends of the endpoint argument until it was written down.
* `exists_radius_above_roots`, `exists_contour_bound_of_tendsto` — the contour
  bound from a convergent parameter, at any `r`.
* `exists_upper_contour_bound_one_of_zero_free` — **`hCbd₁` at a given circle**,
  from the circle carrying no zero of the limiting pencil.  This is the form a
  consumer pairs with the retained set, whose circle is `EndpointUpperOne`'s `2L`.
* `exists_upper_contour_bound_one` — the same at every radius past every zero,
  which asks nothing of `n` and is what shows the bound is not vacuous.
* `eventually_le_ftPrincipalAmp_of_endpoint_double_root`,
  `tendsto_ftPrincipalAmp_atTop_of_endpoint_double_root` — the amplitude diverges
  wherever the limiting pencil has a double root and `B` does not vanish there.
* `ftPrincipalAmp_floor_of_endpoint_pi`, `exists_upper_amplitude_floor_one` —
  **`hamp₁` at `r = 1`**, with `p₁ = 0`, at a given `L` and at one produced.
* `eventually_le_ftPrincipalAmp_of_rootMultiplicity_le_one`,
  `rootMultiplicity_ftCritical_endpoint_pi_eq_one`,
  `ftPrincipalAmp_floor_of_endpoint_pi_of_multiplicity` — the same floor over the
  whole range in which it is true, `ord_{-L}(B) ≤ 1`, through `𝒲 = -tB(t)/E(t)`
  and the simple zero of `E` at the collision.
* `branch_data_endpoint_pi` — the chart data both floors consume, derived once.
* `exists_upper_endpoint_binders_one`, `exists_upper_endpoint_binders_one_two_mul`
  — both binders against one `L` and one window, at a free radius and at `2L`.
* `eventually_eval_ftDen_ne_zero_on_sphere_of_tendsto`,
  `eventually_upper_retained_one` — **the retained upper set at `r = 1`**: the
  principal pair is exactly the pencil's zero set in the disk of radius `2L`, and
  both members are simple.  This is `n₁ = r - 2 = 0`.

## References

* `../../shields-2026-forgacs-tran-numerators.tex`, `thm:weighted-dominance`,
  `subsec:proof`, `eq:W-def`, `eq:contour-remainder-bound`.

## Tags

upper endpoint, contour bound, amplitude floor, residue, double root
-/

namespace ForgacsTran

open Real Set Filter Polynomial Complex
open scoped Topology

/-- The upper endpoint's chart `\eta \mapsto b - \eta` carries `0^+` to `b^-`. -/
theorem tendsto_sub_nhdsGT_zero_nhdsLT {b : ℝ} :
    Tendsto (fun δ : ℝ => b - δ) (𝓝[>] (0 : ℝ)) (𝓝[<] b) := by
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
  · have h : Tendsto (fun δ : ℝ => b - δ) (𝓝 (0 : ℝ)) (𝓝 (b - 0)) :=
      tendsto_const_nhds.sub tendsto_id
    simpa using h.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact sub_lt_self b hδ

/-! ### The endpoint's limits, under one `L`

`exists_tendsto_ftTau_nhdsLT_pi` and `exists_tendsto_ftBranchZ_arc_end_pi` each
open their own existential, and the second hides the limit's value.  A consumer
pairing the two has nothing identifying the `L` of one with the `L` behind the
other, and nothing at all connecting either to the `-Q(-L)/(-L)` at which
`EndpointUpperOne` proves the collision.  Both are supplied here under a single
binder, with the parameter's limit written out. -/

/-- **The `r = 1` upper endpoint, as one package.**  The radius tends to `L > 0`,
`-L` is a zero of `E`, and the spectral parameter tends to `-Q(-L)/(-L)` — the
value `EndpointUpperOne`'s collision is stated at.

Only the last is new: it is `FTMinModulus.UpperEndpoint.tendsto_ftBranchZ_upper_pi`
at the `L` the first two already produced, rather than at an independent one. -/
theorem exists_endpoint_limits_pi {n : ℕ} {a : Fin n → ℝ} {c : ℝ} (hn2 : 2 ≤ n)
    (ha : ∀ k, 0 < a k) (hc : 0 < c) :
    ∃ L : ℝ, 0 < L ∧ (ftCriticalReal (ftRootPolyReal c a) 1).eval (-L) = 0 ∧
      Tendsto (ftTau a 1 (n - 1)) (𝓝[<] π) (𝓝 L) ∧
      Tendsto (ftBranchZ a c 1 (n - 1)) (𝓝[<] π)
        (𝓝 (-(ftRootPolyReal c a).eval (-L) / (-L))) := by
  obtain ⟨L, hL, hτ, hE⟩ := exists_tendsto_ftTau_nhdsLT_pi hn2 ha hc
  refine ⟨L, hL, hE, hτ, ?_⟩
  have hcast : π / ((1 : ℕ) : ℝ) = π := pi_div_natCast_one
  have hmem : ∀ᶠ θ in 𝓝[<] π, θ ∈ Ioo 0 π ∧ FTBranchAt a 1 (n - 1) θ := by
    filter_upwards [Ioo_mem_nhdsLT pi_pos] with θ hθ
    refine ⟨hθ, ftBranchAt_of_arc_principal (by omega) ha le_rfl (Or.inl hn2) ?_⟩
    rw [hcast]; exact hθ
  have := tendsto_ftBranchZ_upper_pi (c := c) (l := n - 1) ha hL hmem hτ
  simpa using this

/-- **The deficit equation, from the endpoint condition alone.**  `E(-L) = 0`
gives `∑_k L/(a_k + L) = r`, with no hypothesis beyond the admissible class and
`L > 0`.

Both ends of the argument were carrying this as an undischarged input — this
module at `-L` and `EndpointUpperOne` in every statement it proves at the circle
`2L` — because the equivalence had not been written down.  It is two facts already
in `FTMinModulus.RealCritical`: `E = -Σ·Q`, and `Q > 0` on the negative axis.  `Q`
being nonzero there is what lets the product be divided out, and it is the step
that needs `c > 0` and `a_k > 0` rather than merely `a_k + L ≠ 0`.

Stated at every `r`, not at `r = 1`: nothing in the derivation sees the exponent
except through `Σ`'s additive `r`. -/
theorem sum_div_add_eq_of_eval_ftCriticalReal_neg {n r : ℕ} {c : ℝ} {a : Fin n → ℝ}
    (ha : ∀ k, 0 < a k) (hc : 0 < c) {L : ℝ} (hL : 0 < L)
    (hE : (ftCriticalReal (ftRootPolyReal c a) r).eval (-L) = 0) :
    ∑ k, L / (a k + L) = r := by
  have hne : ∀ k, a k - (-L) ≠ 0 := fun k => by have := ha k; intro h; simp at h; linarith
  have hQ : 0 < (ftRootPolyReal c a).eval (-L) :=
    eval_ftRootPolyReal_pos_of_neg ha hc (by linarith)
  have hsig : ftSigmaReal a r (-L) = 0 := by
    have h := eval_ftCriticalReal_eq_neg_sigma_mul (c := c) (r := r) hne
    rw [hE] at h
    have := h.symm
    rcases mul_eq_zero.1 (by linarith [this] : -(ftSigmaReal a r (-L)) *
      (ftRootPolyReal c a).eval (-L) = 0) with h0 | h0
    · linarith [neg_eq_zero.1 h0]
    · exact absurd h0 hQ.ne'
  have hterm : ∀ k ∈ Finset.univ, (-L) / (a k - -L) = -(L / (a k + L)) := by
    intro k _
    rw [sub_neg_eq_add, neg_div]
  rw [ftSigmaReal, Finset.sum_congr rfl hterm, Finset.sum_neg_distrib] at hsig
  linarith

/-! ### `hCbd₁`: the bound from a convergent spectral parameter

The circle is fixed and the parameter converges, so `D(\cdot, z(\pi - \delta))`
converges to `D_b` uniformly on it — the difference is `(z - b)t^r`, of modulus
`\|z - b\|R^r`.  A circle on which `D_b` does not vanish therefore carries a
positive floor on `\|D\|` for every small `\delta`, and the quotient is bounded by
a bound on `\|B\|` over the same circle.

The bound is `2M_B/m` with `m` the minimum of `\|D_b\|` on the circle; nothing is
assumed uniform in `\delta` and nothing is evaluated at `\delta = 0`, where `z`
carries whatever junk value its definition happens to take off the arc. -/

/-- **Every large enough circle misses the zeros of a polynomial.**  The zeros are
a finite set, so their moduli are bounded, and any radius past that bound meets
none of them. -/
theorem exists_radius_above_roots {P : Polynomial ℂ} (hP : P ≠ 0) :
    ∃ R₀ > (0 : ℝ), ∀ R : ℝ, R₀ ≤ R → ∀ t : ℂ, ‖t‖ = R → P.eval t ≠ 0 := by
  classical
  obtain ⟨M, hM⟩ := Finset.exists_le (P.roots.toFinset.image (fun t : ℂ => ‖t‖))
  refine ⟨max M 0 + 1, by positivity, fun R hR t ht h0 => ?_⟩
  have hmem : ‖t‖ ∈ P.roots.toFinset.image (fun t : ℂ => ‖t‖) :=
    Finset.mem_image.2 ⟨t, Multiset.mem_toFinset.2 (Polynomial.mem_roots'.2 ⟨hP, h0⟩), rfl⟩
  have h1 : ‖t‖ ≤ M := hM _ hmem
  have h2 : M ≤ max M 0 := le_max_left _ _
  rw [ht] at h1
  linarith

/-- **`hCbd₁` from a convergent parameter.**  On a circle carrying no zero of the
limiting pencil, the quotient `B/D` is bounded across a punctured window at the
endpoint.

No hypothesis on `r`, on the branch, or on where the principal point goes: what is
used is that the parameter converges, which at `r = 1` is
`exists_endpoint_limits_pi` and at `2 \le r` is false. -/
theorem exists_contour_bound_of_tendsto {Q B : Polynomial ℂ} {r : ℕ} {zb : ℂ} {w : ℝ → ℂ}
    (hw : Tendsto w (𝓝[>] (0 : ℝ)) (𝓝 zb)) {R : ℝ} (hR : 0 < R)
    (hne : ∀ t : ℂ, ‖t‖ = R → (ftDen Q r zb).eval t ≠ 0) :
    ∃ C, 0 ≤ C ∧ ∃ e > (0 : ℝ), ∀ δ : ℝ, 0 < δ → δ ≤ e →
      ∀ t ∈ Metric.sphere (0 : ℂ) R,
        (ftDen Q r (w δ)).eval t ≠ 0 ∧ ‖B.eval t / (ftDen Q r (w δ)).eval t‖ ≤ C := by
  have hsphere : ∀ t : ℂ, t ∈ Metric.sphere (0 : ℂ) R → ‖t‖ = R := fun t ht => by
    simpa [Complex.dist_eq, sub_zero] using Metric.mem_sphere.1 ht
  have hsc : IsCompact (Metric.sphere (0 : ℂ) R) := isCompact_sphere _ _
  -- the limiting pencil is bounded away from zero on the circle
  obtain ⟨m, hm, hmle⟩ := hsc.exists_forall_le' ((ftDen Q r zb).continuous.norm).continuousOn
    (a := 0) (fun t ht => norm_pos_iff.2 (hne t (hsphere t ht)))
  -- and the numerator is bounded on it
  obtain ⟨MB, hMB⟩ := hsc.exists_bound_of_continuousOn B.continuous.continuousOn
  have hMB0 : 0 ≤ MB := by
    have hmem : ((R : ℝ) : ℂ) ∈ Metric.sphere (0 : ℂ) R := by
      simp [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
    exact le_trans (norm_nonneg _) (hMB _ hmem)
  have hRr : (0 : ℝ) < R ^ r := by positivity
  -- the parameter is within `m/(2R^r)` of its limit on a window
  obtain ⟨e, he, hwin⟩ := window_of_eventually
    (Metric.tendsto_nhds.mp hw (m / (2 * R ^ r)) (by positivity))
  refine ⟨2 * MB / m, by positivity, e, he, fun δ hδ hδe t ht => ?_⟩
  have htn : ‖t‖ = R := hsphere t ht
  have hdiff : ‖w δ - zb‖ < m / (2 * R ^ r) := by
    rw [← dist_eq_norm]; exact hwin δ hδ hδe
  have hsplit : (ftDen Q r (w δ)).eval t = (ftDen Q r zb).eval t + (w δ - zb) * t ^ r := by
    rw [ftDen_eval, ftDen_eval]; ring
  have hsmall : ‖(w δ - zb) * t ^ r‖ ≤ m / 2 := by
    rw [norm_mul, norm_pow, htn]
    have := mul_le_mul_of_nonneg_right hdiff.le (le_of_lt hRr)
    rw [div_mul_eq_mul_div, mul_comm (2 : ℝ) (R ^ r), ← div_div,
      mul_div_assoc, div_self hRr.ne', mul_one] at this
    exact this
  have hDge : m / 2 ≤ ‖(ftDen Q r (w δ)).eval t‖ := by
    have hlow := norm_sub_norm_le ((ftDen Q r zb).eval t) (-((w δ - zb) * t ^ r))
    rw [sub_neg_eq_add, norm_neg] at hlow
    have := hmle t ht
    rw [hsplit]
    linarith
  have hDpos : (0 : ℝ) < ‖(ftDen Q r (w δ)).eval t‖ := lt_of_lt_of_le (by linarith) hDge
  refine ⟨norm_pos_iff.1 hDpos, ?_⟩
  rw [norm_div, div_le_div_iff₀ hDpos hm]
  nlinarith [hMB t ht, hDge, hMB0, hm]

/-! ### The radius the retained set actually uses

`exists_upper_contour_bound_one` places the circle past **every** zero of `D_b`,
which is enough for the bound and asks nothing of `n`.  It is not the circle
`thm:weighted-dominance` wants: `haR₁` and `huniq₁` make `sfun₁ δ` the zeros
inside `R₁`, so a circle past everything gives `n₁ = n - 2`, while the count the
`r = 1` endpoint is written around is `n₁ = 0` — the retained upper cluster is the
principal pair and nothing else.  `EndpointUpperOne` puts that circle at `2L`,
between the collision at modulus `L` and the remaining zero at modulus `8L` or
more.

Both are the same lemma at different radii, and neither is a special case of the
other: past-everything needs no hypothesis on `n` and is what shows the bound is
not vacuous; `2L` needs `n = 3` and is what a consumer can pair with the retained
set. -/

/-- **`hCbd₁` at a given circle.**  Any circle carrying no zero of the limiting
pencil serves; `EndpointUpperOne.eval_ne_zero_on_sphere_two_mul_endpoint_pi` is
that hypothesis at `R₁ = 2L`.

Only the spectral parameter's limit is used, so `hτ` is not among the hypotheses
even though the `L` in `hfree` came from it. -/
theorem exists_upper_contour_bound_one_of_zero_free {n : ℕ} {a : Fin n → ℝ} {c : ℝ}
    {B : Polynomial ℂ} {L : ℝ}
    (hz : Tendsto (ftBranchZ a c 1 (n - 1)) (𝓝[<] π)
      (𝓝 (-(ftRootPolyReal c a).eval (-L) / (-L))))
    {R₁ : ℝ} (hR₁ : 0 < R₁)
    (hfree : ∀ t ∈ Metric.sphere (0 : ℂ) R₁,
      (ftDen (ftRootPoly c a) 1
        ((-((ftRootPolyReal c a).eval (-L)) / (-L) : ℝ) : ℂ)).eval t ≠ 0) :
    ∃ C₁, 0 ≤ C₁ ∧ ∃ e > (0 : ℝ), ∀ δ : ℝ, 0 < δ → δ ≤ e →
      ∀ t ∈ Metric.sphere (0 : ℂ) R₁,
        (ftDen (ftRootPoly c a) 1
            ((ftBranchZ a c 1 (n - 1) (π - δ) : ℝ) : ℂ)).eval t ≠ 0 ∧
          ‖B.eval t / (ftDen (ftRootPoly c a) 1
            ((ftBranchZ a c 1 (n - 1) (π - δ) : ℝ) : ℂ)).eval t‖ ≤ C₁ := by
  refine exists_contour_bound_of_tendsto (B := B) ?_ hR₁ (fun t ht => hfree t ?_)
  · exact (Complex.continuous_ofReal.tendsto _).comp (hz.comp tendsto_sub_nhdsGT_zero_nhdsLT)
  · simpa [Complex.dist_eq, sub_zero] using ht

/-- **`hCbd₁` at the branch, `r = 1`.**  Every circle past the zeros of the
limiting pencil `D_b = Q + bX` carries a bound on `B/D` across a punctured window
at `\theta = \pi`.

The radius is left free above `R_0` rather than fixed, because the retained-set
group picks it for its own reasons; the two are met on the larger of the two
radii.  Compare `exists_upper_contour_bound`, which fixes no radius either but
buys the bound from `\|z\| \to \infty` — the hypothesis this endpoint does not
have. -/
theorem ftDen_one_ne_zero_of_real {n : ℕ} {a : Fin n → ℝ} {c : ℝ} (hc : c ≠ 0)
    (ha : ∀ k, 0 < a k) (z : ℝ) : ftDen (ftRootPoly c a) 1 ((z : ℝ) : ℂ) ≠ 0 := by
  intro h0
  have hev : (ftDen (ftRootPoly c a) 1 ((z : ℝ) : ℂ)).eval 0 = (ftRootPoly c a).eval 0 := by
    rw [ftDen_eval]; simp
  rw [h0] at hev
  simp only [Polynomial.eval_zero] at hev
  exact eval_ftRootPoly_zero_ne_zero hc ha hev.symm

/-- **A radius past every zero of the limiting pencil, at the endpoint's own `L`.**
`exists_radius_above_roots` at `D_b`, which is a nonzero polynomial because
`D_b(0) = Q(0) \ne 0`. -/
theorem exists_radius_above_roots_endpoint_pi {n : ℕ} {a : Fin n → ℝ} {c : ℝ}
    (hc : c ≠ 0) (ha : ∀ k, 0 < a k) (L : ℝ) :
    ∃ R₀ > (0 : ℝ), ∀ R : ℝ, R₀ ≤ R → ∀ t ∈ Metric.sphere (0 : ℂ) R,
      (ftDen (ftRootPoly c a) 1
        ((-((ftRootPolyReal c a).eval (-L)) / (-L) : ℝ) : ℂ)).eval t ≠ 0 := by
  obtain ⟨R₀, hR₀, hroots⟩ :=
    exists_radius_above_roots (ftDen_one_ne_zero_of_real hc ha
      (-((ftRootPolyReal c a).eval (-L)) / (-L)))
  exact ⟨R₀, hR₀, fun R hR t ht =>
    hroots R hR t (by simpa [Complex.dist_eq, sub_zero] using ht)⟩

theorem exists_upper_contour_bound_one {n : ℕ} {a : Fin n → ℝ} {c : ℝ} {B : Polynomial ℂ}
    (hn2 : 2 ≤ n) (ha : ∀ k, 0 < a k) (hc : 0 < c) :
    ∃ L : ℝ, 0 < L ∧ (ftCriticalReal (ftRootPolyReal c a) 1).eval (-L) = 0 ∧
      ∃ R₀ > (0 : ℝ), ∀ R₁ : ℝ, R₀ ≤ R₁ →
        ∃ C₁, 0 ≤ C₁ ∧ ∃ e > (0 : ℝ), ∀ δ : ℝ, 0 < δ → δ ≤ e →
          ∀ t ∈ Metric.sphere (0 : ℂ) R₁,
            (ftDen (ftRootPoly c a) 1
                ((ftBranchZ a c 1 (n - 1) (π - δ) : ℝ) : ℂ)).eval t ≠ 0 ∧
              ‖B.eval t / (ftDen (ftRootPoly c a) 1
                ((ftBranchZ a c 1 (n - 1) (π - δ) : ℝ) : ℂ)).eval t‖ ≤ C₁ := by
  obtain ⟨L, hL, hE, -, hz⟩ := exists_endpoint_limits_pi hn2 ha hc
  obtain ⟨R₀, hR₀, hroots⟩ := exists_radius_above_roots_endpoint_pi hc.ne' ha L
  exact ⟨L, hL, hE, R₀, hR₀, fun R₁ hR₁ =>
    exists_upper_contour_bound_one_of_zero_free (B := B) (L := L) hz
      (lt_of_lt_of_le hR₀ hR₁) (hroots R₁ hR₁)⟩

/-! ### `hamp₁`: the amplitude at a collision

`eq:W-def`'s `\mathcal{W} = -B(t_+)/\partial_tD(t_+)` is a residue, so what the
principal point runs into decides the amplitude's behavior there.  At `2 \le r` it
runs into the origin, where neither `B` nor `E = XQ' - rQ` vanishes, and the
amplitude vanishes with `\tau`.  At `r = 1` it runs into `-L`, where
`EndpointUpperOne.two_le_rootMultiplicity_ftDen_endpoint_pi` puts a **double** root
of the limiting pencil: `\partial_tD \to 0` while `B(-L) \ne 0`, so the residue
diverges.

The floor is therefore a constant and `p_1 = 0`.  `p_1 = 1` is true here too and
is the wrong statement rather than a weaker one — it is met by an amplitude that
vanishes, and nothing vanishes.  What is stated below is the divergence itself:
the floor holds at **every** `A_1`, not merely at some. -/

/-- **The limiting pencil's derivative vanishes at the collision.**
`two_le_rootMultiplicity_ftDen_endpoint_pi` read one order down: a root of order at
least two is a root of the derivative. -/
theorem eval_derivative_ftDen_endpoint_pi_eq_zero {n : ℕ} {a : Fin n → ℝ} {c : ℝ}
    (ha : ∀ k, 0 < a k) (hc : c ≠ 0) {L : ℝ} (hL : 0 < L)
    (hE : (ftCriticalReal (ftRootPolyReal c a) 1).eval (-L) = 0) :
    (derivative (ftDen (ftRootPoly c a) 1
        ((-((ftRootPolyReal c a).eval (-L)) / (-L) : ℝ) : ℂ))).eval ((-L : ℝ) : ℂ) = 0 := by
  have h2 := two_le_rootMultiplicity_ftDen_endpoint_pi ha hc hL hE
  have h := Polynomial.isRoot_iterate_derivative_of_lt_rootMultiplicity
    (p := ftDen (ftRootPoly c a) 1 ((-((ftRootPolyReal c a).eval (-L)) / (-L) : ℝ) : ℂ))
    (t := ((-L : ℝ) : ℂ)) (n := 1) (by omega)
  simpa [Polynomial.IsRoot] using h

/-- **The principal amplitude clears every floor at a collision.**  Wherever the
principal point and the spectral parameter both converge, the limiting pencil has a
double root at the limit point, and `B` does not vanish there, the residue
`-B(t_+)/\partial_tD(t_+)` diverges.

`hsimple` is what keeps the statement about the geometry rather than about Lean's
division convention: without it `\partial_tD(t_+)` may vanish on the window, where
the quotient is `0` by fiat and no floor holds.  It is `eq:principal-simple`, which
`PrincipalSimpleBranch.ft_principal_simple_at_branch` supplies unconditionally
across the open arc. -/
theorem eventually_le_ftPrincipalAmp_of_endpoint_double_root
    {Q B : Polynomial ℂ} {r : ℕ} {b : ℝ} {z τ : ℝ → ℝ} {tb zb : ℂ}
    (hB : B.eval tb ≠ 0)
    (hγ : Tendsto (fun η : ℝ => ftPrincipal τ (b - η)) (𝓝[>] (0 : ℝ)) (𝓝 tb))
    (hz : Tendsto (fun η : ℝ => ((z (b - η) : ℝ) : ℂ)) (𝓝[>] (0 : ℝ)) (𝓝 zb))
    (hD : (derivative (ftDen Q r zb)).eval tb = 0)
    (hroot : ∀ᶠ η in 𝓝[>] (0 : ℝ),
      (ftDen Q r ((z (b - η) : ℝ) : ℂ)).eval (ftPrincipal τ (b - η)) = 0)
    (hsimple : ∀ᶠ η in 𝓝[>] (0 : ℝ),
      (derivative (ftDen Q r ((z (b - η) : ℝ) : ℂ))).eval (ftPrincipal τ (b - η)) ≠ 0)
    (A : ℝ) :
    ∀ᶠ η in 𝓝[>] (0 : ℝ), A ≤ ftPrincipalAmp Q B r z τ (b - η) := by
  set γ : ℝ → ℂ := fun η => ftPrincipal τ (b - η) with hγdef
  set d : ℝ → ℂ := fun η =>
    (derivative (ftDen Q r ((z (b - η) : ℝ) : ℂ))).eval (γ η) with hddef
  -- the residue's denominator vanishes in the limit
  have hd : Tendsto d (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h1 : Tendsto (fun η => (derivative Q).eval (γ η)) (𝓝[>] (0 : ℝ))
        (𝓝 ((derivative Q).eval tb)) := ((derivative Q).continuous.tendsto tb).comp hγ
    have h2 : Tendsto (fun η => ((z (b - η) : ℝ) : ℂ) * (r : ℂ) * (γ η) ^ (r - 1))
        (𝓝[>] (0 : ℝ)) (𝓝 (zb * (r : ℂ) * tb ^ (r - 1))) :=
      (hz.mul tendsto_const_nhds).mul (hγ.pow (r - 1))
    have h3 := h1.add h2
    rw [← eval_derivative_ftDen_eq, hD] at h3
    refine h3.congr fun η => ?_
    simp only [hddef, eval_derivative_ftDen_eq]
  have hBn : Tendsto (fun η => ‖B.eval (γ η)‖) (𝓝[>] (0 : ℝ)) (𝓝 ‖B.eval tb‖) :=
    ((B.continuous.tendsto tb).comp hγ).norm
  set cB : ℝ := ‖B.eval tb‖ with hcBdef
  have hcB : 0 < cB := norm_pos_iff.2 hB
  have hK : (0 : ℝ) < |A| + 1 := by positivity
  have ev1 : ∀ᶠ η in 𝓝[>] (0 : ℝ), cB / 2 < ‖B.eval (γ η)‖ := by
    filter_upwards [Metric.tendsto_nhds.mp hBn (cB / 2) (by positivity)] with η hη
    rw [Real.dist_eq, abs_lt] at hη
    linarith [hη.1]
  have ev2 : ∀ᶠ η in 𝓝[>] (0 : ℝ), ‖d η‖ < cB / (2 * (|A| + 1)) := by
    filter_upwards [Metric.tendsto_nhds.mp hd.norm (cB / (2 * (|A| + 1)))
      (by positivity)] with η hη
    rw [Real.dist_eq] at hη
    simpa [abs_of_nonneg (norm_nonneg (d η))] using hη
  filter_upwards [ev1, ev2, hroot, hsimple] with η h1 h2 hr0 hs0
  have hdpos : 0 < ‖d η‖ := norm_pos_iff.2 hs0
  have hamp : ftPrincipalAmp Q B r z τ (b - η) = ‖B.eval (γ η)‖ / ‖d η‖ := by
    rw [ftPrincipalAmp, ftAmp_eq_neg_div_derivative hr0, norm_div, norm_neg]
  rw [hamp, le_div_iff₀ hdpos]
  have step1 : A * ‖d η‖ ≤ |A| * ‖d η‖ :=
    mul_le_mul_of_nonneg_right (le_abs_self A) (norm_nonneg _)
  have step2 : |A| * ‖d η‖ ≤ |A| * (cB / (2 * (|A| + 1))) :=
    mul_le_mul_of_nonneg_left h2.le (abs_nonneg A)
  have step3 : |A| * (cB / (2 * (|A| + 1))) < cB / 2 := by
    rw [← mul_div_assoc, div_lt_div_iff₀ (by positivity) (by norm_num : (0 : ℝ) < 2)]
    nlinarith [hcB, abs_nonneg A]
  linarith

/-- **`E` has a simple zero at the collision.**  `E = XQ' - rQ` vanishes at `-L` by
the endpoint condition, and at `r = 1` its derivative is `XQ''`, which at `-L` is
`(-L)Q''(-L)` — nonzero because `Q''` is a sum of positive terms on the negative
axis, the same fact that makes the pencil's own root there exactly double.

This is what makes the amplitude's order at the collision `ord_{-L}(B) - 1` rather
than `ord_{-L}(B) - ord_{-L}(E)`. -/
theorem rootMultiplicity_ftCritical_endpoint_pi_eq_one {n : ℕ} {a : Fin n → ℝ} {c : ℝ}
    (hn2 : 2 ≤ n) (ha : ∀ k, 0 < a k) (hc : 0 < c) {L : ℝ} (hL : 0 < L)
    (hE : (ftCriticalReal (ftRootPolyReal c a) 1).eval (-L) = 0) :
    (ftCritical (ftRootPoly c a) 1).rootMultiplicity ((-L : ℝ) : ℂ) = 1 := by
  classical
  have hQ0 : (ftRootPoly c a).eval 0 ≠ 0 := eval_ftRootPoly_zero_ne_zero hc.ne' ha
  have hEne : ftCritical (ftRootPoly c a) 1 ≠ 0 := by
    intro h0
    exact eval_ftCritical_zero_ne_zero le_rfl hQ0 (by rw [h0]; simp)
  -- the endpoint condition, over `ℂ`
  have hEroot : (ftCritical (ftRootPoly c a) 1).eval ((-L : ℝ) : ℂ) = 0 := by
    rw [ftRootPoly_eq_map, ftCritical_map, Polynomial.eval_map,
      show ((-L : ℝ) : ℂ) = algebraMap ℝ ℂ (-L) from rfl, Polynomial.eval₂_at_apply, hE]
    simp
  -- `E' = X Q''` at `r = 1`, and `Q''(-L) > 0`
  have hderiv : derivative (ftCritical (ftRootPoly c a) 1)
      = X * derivative (derivative (ftRootPoly c a)) := by
    rw [ftCritical, derivative_sub, derivative_mul, derivative_X, derivative_C_mul]
    push_cast
    simp only [Polynomial.C_1, one_mul]
    ring
  have hQ2 : (derivative (derivative (ftRootPoly c a))).eval ((-L : ℝ) : ℂ)
      = (((derivative (derivative (ftRootPolyReal c a))).eval (-L) : ℝ) : ℂ) := by
    simpa [Function.iterate_succ_apply'] using
      eval_iterate_derivative_ftRootPoly c a 2 (-L)
  have hQ2pos : 0 < (derivative (derivative (ftRootPolyReal c a))).eval (-L) :=
    eval_derivative_two_ftRootPolyReal_pos hn2 ha hc (by linarith)
  have hEderiv : (derivative (ftCritical (ftRootPoly c a) 1)).eval ((-L : ℝ) : ℂ) ≠ 0 := by
    rw [hderiv, eval_mul, eval_X, hQ2]
    refine mul_ne_zero (by exact_mod_cast (by linarith : (-L : ℝ) ≠ 0)) ?_
    exact_mod_cast hQ2pos.ne'
  -- a root whose derivative does not vanish there has multiplicity exactly one
  have hpos : 0 < (ftCritical (ftRootPoly c a) 1).rootMultiplicity ((-L : ℝ) : ℂ) :=
    (Polynomial.rootMultiplicity_pos hEne).2 hEroot
  have hle : ¬ 1 < (ftCritical (ftRootPoly c a) 1).rootMultiplicity ((-L : ℝ) : ℂ) := by
    intro hgt
    exact hEderiv ((Polynomial.one_lt_rootMultiplicity_iff_isRoot hEne).1 hgt).2
  omega

/-- **The floor at every numerator vanishing to order at most one at the
collision.**  `eq:W-on-g` writes the amplitude as `-tB(t)/E(t)` with
`E = XQ' - rQ`, and `E` carries no `z`, so the whole `\delta`-dependence sits in
where the principal point is.  Both `B` and `E` are then fixed polynomials read
along `t_+ \to t_b`, and the floor is a statement about their orders there.

`ord_{t_b}(E) = 1` and `ord_{t_b}(B) = m` give
`|\mathcal{W}| = |t_+| \cdot d^{m-1} |B_1(t_+)| / |E_1(t_+)|` with
`d = |t_+ - t_b|`, and for `m \le 1` and `d \le 1` the factor `d^m/d` is at least
one — so the floor is the limit of the second factor, which is positive.  **No
rate on `d` is used**, which is what makes `m = 0` and `m = 1` one argument
rather than two: at `m = 0` the amplitude diverges and at `m = 1` it tends to a
positive constant, and the bound below is all either case needs.

At `m \ge 2` the conclusion is FALSE — the amplitude vanishes — and `\eta^{m-1}`
is the honest exponent there.  What that case needs beyond this one is a **lower**
bound on `d`, and only that: not the two-sided splitting rate
`|t_+ - t_b| \asymp \eta`, which is a statement about the local geometry of the
double root.  `EndpointUpperMultiplicity` supplies the lower bound from the
imaginary part alone and carries the floor at every `m`; this theorem is the case
where no bound on `d` is used at all. -/
theorem eventually_le_ftPrincipalAmp_of_rootMultiplicity_le_one
    {Q B : Polynomial ℂ} {r : ℕ} (hr : 1 ≤ r) {b : ℝ} {z τ : ℝ → ℝ} {tb : ℂ}
    (hB0 : B ≠ 0) (hE0 : ftCritical Q r ≠ 0) (htb : tb ≠ 0)
    (hEmult : (ftCritical Q r).rootMultiplicity tb = 1)
    (hm : B.rootMultiplicity tb ≤ 1)
    (hγ : Tendsto (fun η : ℝ => ftPrincipal τ (b - η)) (𝓝[>] (0 : ℝ)) (𝓝 tb))
    (hpne : ∀ᶠ η in 𝓝[>] (0 : ℝ), ftPrincipal τ (b - η) ≠ 0)
    (hroot : ∀ᶠ η in 𝓝[>] (0 : ℝ),
      (ftDen Q r ((z (b - η) : ℝ) : ℂ)).eval (ftPrincipal τ (b - η)) = 0)
    (hEne : ∀ᶠ η in 𝓝[>] (0 : ℝ),
      (ftCritical Q r).eval (ftPrincipal τ (b - η)) ≠ 0) :
    ∃ A > (0 : ℝ), ∀ᶠ η in 𝓝[>] (0 : ℝ), A ≤ ftPrincipalAmp Q B r z τ (b - η) := by
  classical
  set E : Polynomial ℂ := ftCritical Q r with hEdef
  set m : ℕ := B.rootMultiplicity tb with hmdef
  set B₁ : Polynomial ℂ := B /ₘ (X - C tb) ^ m with hB₁def
  set E₁ : Polynomial ℂ := E /ₘ (X - C tb) ^ E.rootMultiplicity tb with hE₁def
  have hB₁ne : B₁.eval tb ≠ 0 := Polynomial.eval_divByMonic_pow_rootMultiplicity_ne_zero tb hB0
  have hE₁ne : E₁.eval tb ≠ 0 := Polynomial.eval_divByMonic_pow_rootMultiplicity_ne_zero tb hE0
  have hBfac : ∀ t : ℂ, B.eval t = (t - tb) ^ m * B₁.eval t := by
    intro t
    conv_lhs => rw [← Polynomial.pow_mul_divByMonic_rootMultiplicity_eq B tb]
    simp [hB₁def, hmdef]
  have hEfac : ∀ t : ℂ, E.eval t = (t - tb) * E₁.eval t := by
    intro t
    conv_lhs => rw [← Polynomial.pow_mul_divByMonic_rootMultiplicity_eq E tb]
    simp [hE₁def, hEmult]
  -- the limit of the second factor
  set Lm : ℝ := ‖tb‖ * ‖B₁.eval tb‖ / ‖E₁.eval tb‖ with hLmdef
  have hLm : 0 < Lm := by
    refine div_pos (mul_pos ?_ ?_) ?_ <;> simp [norm_pos_iff, htb, hB₁ne, hE₁ne]
  have hcont : Tendsto (fun η : ℝ =>
      ‖ftPrincipal τ (b - η)‖ * ‖B₁.eval (ftPrincipal τ (b - η))‖
        / ‖E₁.eval (ftPrincipal τ (b - η))‖) (𝓝[>] (0 : ℝ)) (𝓝 Lm) :=
    ((hγ.norm).mul (((B₁.continuous.tendsto tb).comp hγ).norm)).div
      (((E₁.continuous.tendsto tb).comp hγ).norm) (by simpa using hE₁ne)
  refine ⟨Lm / 2, by linarith, ?_⟩
  filter_upwards [hpne, hroot, hEne,
    Metric.tendsto_nhds.mp hγ 1 one_pos,
    Metric.tendsto_nhds.mp hcont (Lm / 2) (by linarith)] with η hp0 hr0 hE hd hL
  set t : ℂ := ftPrincipal τ (b - η) with htdef
  -- the principal point has not reached the collision, because `E` vanishes there
  have htne : t - tb ≠ 0 := by
    intro h0
    refine hE ?_
    rw [sub_eq_zero.1 h0, hEfac tb]
    simp
  have hd1 : ‖t - tb‖ ≤ 1 := by rw [← Complex.dist_eq]; exact hd.le
  have hdpos : 0 < ‖t - tb‖ := norm_pos_iff.2 htne
  have hE₁t : E₁.eval t ≠ 0 := fun h0 => hE (by rw [hEfac, h0, mul_zero])
  have hE₁pos : 0 < ‖E₁.eval t‖ := norm_pos_iff.2 hE₁t
  -- the amplitude, factored through the orders at `t_b`
  have hamp : ftPrincipalAmp Q B r z τ (b - η)
      = ‖t‖ * (‖t - tb‖ ^ m * ‖B₁.eval t‖) / (‖t - tb‖ * ‖E₁.eval t‖) := by
    rw [ftPrincipalAmp, ftAmp_eq_ftCritical hr hp0 hr0, norm_div, norm_neg, norm_mul,
      ← hEdef, hEfac, hBfac, norm_mul, norm_mul, norm_pow]
  -- `d^m >= d` for `m <= 1` and `0 < d <= 1`: the two cases ARE the two regimes,
  -- `m = 0` where the amplitude diverges and `m = 1` where it tends to a constant
  have hpow : ‖t - tb‖ ≤ ‖t - tb‖ ^ m := by
    rcases (by omega : m = 0 ∨ m = 1) with h | h
    · rw [h, pow_zero]; exact hd1
    · rw [h, pow_one]
  have hL' : Lm / 2 < ‖t‖ * ‖B₁.eval t‖ / ‖E₁.eval t‖ := by
    rw [Real.dist_eq, abs_lt] at hL
    linarith [hL.1]
  have hkey : ‖t‖ * ‖B₁.eval t‖ / ‖E₁.eval t‖
      ≤ ‖t‖ * (‖t - tb‖ ^ m * ‖B₁.eval t‖) / (‖t - tb‖ * ‖E₁.eval t‖) := by
    rw [div_le_div_iff₀ hE₁pos (by positivity)]
    have hX : 0 ≤ ‖t‖ * ‖B₁.eval t‖ * ‖E₁.eval t‖ := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hpow hX]
  rw [hamp]
  linarith

/-- **The amplitude diverges at the collision**, which is the same statement as
`eventually_le_ftPrincipalAmp_of_endpoint_double_root` with the quantifier moved.
It is what separates this endpoint from the `2 \le r` one, where the amplitude
tends to `0`. -/
theorem tendsto_ftPrincipalAmp_atTop_of_endpoint_double_root
    {Q B : Polynomial ℂ} {r : ℕ} {b : ℝ} {z τ : ℝ → ℝ} {tb zb : ℂ}
    (hB : B.eval tb ≠ 0)
    (hγ : Tendsto (fun η : ℝ => ftPrincipal τ (b - η)) (𝓝[>] (0 : ℝ)) (𝓝 tb))
    (hz : Tendsto (fun η : ℝ => ((z (b - η) : ℝ) : ℂ)) (𝓝[>] (0 : ℝ)) (𝓝 zb))
    (hD : (derivative (ftDen Q r zb)).eval tb = 0)
    (hroot : ∀ᶠ η in 𝓝[>] (0 : ℝ),
      (ftDen Q r ((z (b - η) : ℝ) : ℂ)).eval (ftPrincipal τ (b - η)) = 0)
    (hsimple : ∀ᶠ η in 𝓝[>] (0 : ℝ),
      (derivative (ftDen Q r ((z (b - η) : ℝ) : ℂ))).eval (ftPrincipal τ (b - η)) ≠ 0) :
    Tendsto (fun η : ℝ => ftPrincipalAmp Q B r z τ (b - η)) (𝓝[>] (0 : ℝ)) atTop :=
  tendsto_atTop.2 fun A =>
    eventually_le_ftPrincipalAmp_of_endpoint_double_root hB hγ hz hD hroot hsimple A

/-- **The branch's data at the `r = 1` endpoint, in the chart.**  The principal
point runs into `-L`, the spectral parameter into `-Q(-L)/(-L)`, and across the
open arc the point is a nonzero simple zero of the pencil.

Extracted because both amplitude floors below consume exactly this, and two copies
of a chart derivation is how the two come to disagree about which point they are
at. -/
theorem branch_data_endpoint_pi {n : ℕ} {a : Fin n → ℝ} {c x₁ : ℝ}
    (hn2 : 2 ≤ n) (ha : ∀ k, 0 < a k) (hc : 0 < c) {L : ℝ}
    (hτ : Tendsto (ftTau a 1 (n - 1)) (𝓝[<] π) (𝓝 L))
    (hz : Tendsto (ftBranchZ a c 1 (n - 1)) (𝓝[<] π)
      (𝓝 (-(ftRootPolyReal c a).eval (-L) / (-L)))) :
    Tendsto (fun η : ℝ => ftPrincipal (ftTauArc a 1 (n - 1) x₁) (π - η)) (𝓝[>] (0 : ℝ))
        (𝓝 ((-L : ℝ) : ℂ)) ∧
      Tendsto (fun η : ℝ => ((ftBranchZ a c 1 (n - 1) (π - η) : ℝ) : ℂ)) (𝓝[>] (0 : ℝ))
        (𝓝 (((-((ftRootPolyReal c a).eval (-L)) / (-L) : ℝ) : ℝ) : ℂ)) ∧
      (∀ᶠ η in 𝓝[>] (0 : ℝ),
        ftPrincipal (ftTauArc a 1 (n - 1) x₁) (π - η) ≠ 0 ∧
        (ftDen (ftRootPoly c a) 1 ((ftBranchZ a c 1 (n - 1) (π - η) : ℝ) : ℂ)).eval
            (ftPrincipal (ftTauArc a 1 (n - 1) x₁) (π - η)) = 0 ∧
        (derivative (ftDen (ftRootPoly c a) 1
            ((ftBranchZ a c 1 (n - 1) (π - η) : ℝ) : ℂ))).eval
            (ftPrincipal (ftTauArc a 1 (n - 1) x₁) (π - η)) ≠ 0) := by
  have hcast : π / ((1 : ℕ) : ℝ) = π := pi_div_natCast_one
  have harc : ∀ᶠ η in 𝓝[>] (0 : ℝ), π - η ∈ Ioo 0 (π / ((1 : ℕ) : ℝ)) := by
    filter_upwards [Ioo_mem_nhdsGT pi_pos] with η hηπ
    rw [hcast]
    exact ⟨by linarith [hηπ.2], by linarith [hηπ.1]⟩
  have hAgree : ∀ᶠ η in 𝓝[>] (0 : ℝ), ftPrincipal (ftTauArc a 1 (n - 1) x₁) (π - η)
      = ftPrincipal (ftTau a 1 (n - 1)) (π - η) := by
    filter_upwards [harc] with η hη
    rw [ftPrincipal, ftPrincipal, ftTauArc_agree a 1 (n - 1) x₁ hη.1 hη.2]
  refine ⟨?_, (Complex.continuous_ofReal.tendsto _).comp
    (hz.comp tendsto_sub_nhdsGT_zero_nhdsLT), ?_⟩
  · -- the principal point runs into `-L`
    have hTη : Tendsto (fun η : ℝ => ftTau a 1 (n - 1) (π - η)) (𝓝[>] (0 : ℝ)) (𝓝 L) :=
      hτ.comp tendsto_sub_nhdsGT_zero_nhdsLT
    have hexp : Tendsto (fun η : ℝ => Complex.exp (((π - η : ℝ) : ℂ) * I))
        (𝓝[>] (0 : ℝ)) (𝓝 (-1)) := by
      have hb : Tendsto (fun η : ℝ => ((π - η : ℝ) : ℂ) * I) (𝓝[>] (0 : ℝ))
          (𝓝 (((π : ℝ) : ℂ) * I)) :=
        (((Complex.continuous_ofReal.tendsto π).comp
          (tendsto_sub_nhdsGT_zero_nhdsLT.mono_right nhdsWithin_le_nhds)).mul
          tendsto_const_nhds)
      have h := (Complex.continuous_exp.tendsto (((π : ℝ) : ℂ) * I)).comp hb
      simpa [Function.comp_def, Complex.exp_pi_mul_I] using h
    have hmul := ((Complex.continuous_ofReal.tendsto L).comp hTη).mul hexp
    have hval : ((L : ℝ) : ℂ) * (-1) = ((-L : ℝ) : ℂ) := by push_cast; ring
    rw [hval] at hmul
    refine hmul.congr' ?_
    filter_upwards [hAgree] with η hη
    rw [hη, ftPrincipal]
    rfl
  · obtain ⟨hrootA, hposA⟩ := ft_branch_root_and_pos (a := a) (r := 1) c (by omega) ha le_rfl
      (Or.inl hn2)
    filter_upwards [harc, hAgree] with η hη hEq
    refine ⟨?_, ?_, ?_⟩
    · rw [hEq]
      exact ftPrincipal_ne_zero_of_pos (hposA _ hη)
    · rw [hEq]; exact hrootA _ hη
    · rw [hEq]
      exact (ft_principal_simple_at_branch (a := a) (c := c) (r := 1) (by omega) ha hc.ne'
        le_rfl (Or.inl hn2) hη).1

/-- **`hamp₁` at the branch, `r = 1`, at a given `L`.**  The floor holds at every
`A_1` and with `p_1 = 0`.

`B(-L) \ne 0` is the hypothesis, and it is the analogue of the `2 \le r` case's
`B(0) \ne 0`.  It is the `ord_{-L}(B) = 0` case of
`ftPrincipalAmp_floor_of_endpoint_pi_of_multiplicity`, and the only one in which
the floor holds at EVERY `A_1` rather than at some — at `ord = 1` the amplitude is
bounded and `\forall A_1` is false.

The floor holds on the punctured window only, and that is the geometry rather than
a technicality: `\partial_tD(t_+)` vanishes linearly at the collision, which is
exactly why the residue diverges.  `eventually_upper_retained_one` records the same
fact from the other side. -/
theorem ftPrincipalAmp_floor_of_endpoint_pi {n : ℕ} {a : Fin n → ℝ} {c x₁ : ℝ}
    {B : Polynomial ℂ} (hn2 : 2 ≤ n) (ha : ∀ k, 0 < a k) (hc : 0 < c) {L : ℝ} (hL : 0 < L)
    (hE : (ftCriticalReal (ftRootPolyReal c a) 1).eval (-L) = 0)
    (hτ : Tendsto (ftTau a 1 (n - 1)) (𝓝[<] π) (𝓝 L))
    (hz : Tendsto (ftBranchZ a c 1 (n - 1)) (𝓝[<] π)
      (𝓝 (-(ftRootPolyReal c a).eval (-L) / (-L))))
    (hBL : B.eval ((-L : ℝ) : ℂ) ≠ 0) (A₁ : ℝ) :
    ∃ e > (0 : ℝ), ∀ η : ℝ, 0 < η → η ≤ e →
      A₁ * η ^ 0 ≤ ftPrincipalAmp (ftRootPoly c a) B 1 (ftBranchZ a c 1 (n - 1))
        (ftTauArc a 1 (n - 1) x₁) (π - η) := by
  obtain ⟨hγ, hzt, hbr⟩ := branch_data_endpoint_pi (x₁ := x₁) hn2 ha hc hτ hz
  have hev := eventually_le_ftPrincipalAmp_of_endpoint_double_root
    (Q := ftRootPoly c a) (B := B) (r := 1) (b := π)
    (z := ftBranchZ a c 1 (n - 1)) (τ := ftTauArc a 1 (n - 1) x₁) hBL hγ hzt
    (eval_derivative_ftDen_endpoint_pi_eq_zero ha hc.ne' hL hE)
    (hbr.mono fun η h => h.2.1) (hbr.mono fun η h => h.2.2) A₁
  obtain ⟨e, he, hwin⟩ := window_of_eventually hev
  exact ⟨e, he, fun η hη hηe => by simpa using hwin η hη hηe⟩

/-- **`hamp₁` at the branch when `B` vanishes simply at the collision.**  The floor
survives `ord_{-L}(B) \le 1`, which is exactly the range in which `p_1 = 0` is
true — at `ord \ge 2` the amplitude vanishes and the honest exponent is
`ord - 1`.

The conclusion is `\exists A_1 > 0` rather than `\forall A_1`, and the weakening is
the mathematics rather than a limitation of the proof: at `ord = 1` the amplitude
tends to a finite nonzero limit, so no floor above that limit holds.  Only the
`ord = 0` case above clears every constant. -/
theorem ftPrincipalAmp_floor_of_endpoint_pi_of_multiplicity {n : ℕ} {a : Fin n → ℝ}
    {c x₁ : ℝ} {B : Polynomial ℂ} (hn2 : 2 ≤ n) (ha : ∀ k, 0 < a k) (hc : 0 < c)
    {L : ℝ} (hL : 0 < L)
    (hE : (ftCriticalReal (ftRootPolyReal c a) 1).eval (-L) = 0)
    (hτ : Tendsto (ftTau a 1 (n - 1)) (𝓝[<] π) (𝓝 L))
    (hz : Tendsto (ftBranchZ a c 1 (n - 1)) (𝓝[<] π)
      (𝓝 (-(ftRootPolyReal c a).eval (-L) / (-L))))
    (hB0 : B ≠ 0) (hm : B.rootMultiplicity ((-L : ℝ) : ℂ) ≤ 1) :
    ∃ A₁ > (0 : ℝ), ∃ e > (0 : ℝ), ∀ η : ℝ, 0 < η → η ≤ e →
      A₁ * η ^ 0 ≤ ftPrincipalAmp (ftRootPoly c a) B 1 (ftBranchZ a c 1 (n - 1))
        (ftTauArc a 1 (n - 1) x₁) (π - η) := by
  obtain ⟨hγ, -, hbr⟩ := branch_data_endpoint_pi (x₁ := x₁) hn2 ha hc hτ hz
  have hQ0 : (ftRootPoly c a).eval 0 ≠ 0 := eval_ftRootPoly_zero_ne_zero hc.ne' ha
  have hE0 : ftCritical (ftRootPoly c a) 1 ≠ 0 := by
    intro h0
    exact eval_ftCritical_zero_ne_zero le_rfl hQ0 (by rw [h0]; simp)
  -- `E(t_+) \ne 0` is the simplicity, read through `D' = E/t`
  have hEne : ∀ᶠ η in 𝓝[>] (0 : ℝ),
      (ftCritical (ftRootPoly c a) 1).eval
        (ftPrincipal (ftTauArc a 1 (n - 1) x₁) (π - η)) ≠ 0 := by
    filter_upwards [hbr] with η h h0
    refine h.2.2 ?_
    rw [eval_derivative_ftDen_eq_ftCritical_div le_rfl h.1 h.2.1, h0, zero_div]
  obtain ⟨A₁, hA₁, hev⟩ := eventually_le_ftPrincipalAmp_of_rootMultiplicity_le_one
    (Q := ftRootPoly c a) (B := B) (r := 1) (b := π)
    (z := ftBranchZ a c 1 (n - 1)) (τ := ftTauArc a 1 (n - 1) x₁)
    le_rfl hB0 hE0 (by exact_mod_cast (by linarith : (-L : ℝ) ≠ 0))
    (rootMultiplicity_ftCritical_endpoint_pi_eq_one hn2 ha hc hL hE) hm hγ
    (hbr.mono fun η h => h.1) (hbr.mono fun η h => h.2.1) hEne
  obtain ⟨e, he, hwin⟩ := window_of_eventually hev
  exact ⟨A₁, hA₁, e, he, fun η hη hηe => by simpa using hwin η hη hηe⟩

/-- **`hamp₁` at the branch, `r = 1`, with the collision point produced.**
`ftPrincipalAmp_floor_of_endpoint_pi` at the `L` `exists_endpoint_limits_pi`
returns.  Where both binders are wanted, use that pair directly rather than this
one: a second `∃ L` here and a first one there leaves nothing identifying the two,
and a consumer may then take the amplitude's hypothesis at one collision point and
the contour bound's circle at another. -/
theorem exists_upper_amplitude_floor_one {n : ℕ} {a : Fin n → ℝ} {c x₁ : ℝ}
    {B : Polynomial ℂ} (hn2 : 2 ≤ n) (ha : ∀ k, 0 < a k) (hc : 0 < c) :
    ∃ L : ℝ, 0 < L ∧ (ftCriticalReal (ftRootPolyReal c a) 1).eval (-L) = 0 ∧
      (B.eval ((-L : ℝ) : ℂ) ≠ 0 → ∀ A₁ : ℝ, ∃ e > (0 : ℝ), ∀ η : ℝ, 0 < η → η ≤ e →
        A₁ * η ^ 0 ≤ ftPrincipalAmp (ftRootPoly c a) B 1 (ftBranchZ a c 1 (n - 1))
          (ftTauArc a 1 (n - 1) x₁) (π - η)) := by
  obtain ⟨L, hL, hE, hτ, hz⟩ := exists_endpoint_limits_pi hn2 ha hc
  exact ⟨L, hL, hE, fun hBL A₁ =>
    ftPrincipalAmp_floor_of_endpoint_pi (x₁ := x₁) hn2 ha hc hL hE hτ hz hBL A₁⟩

/-! ### The two binders against one window

`thm:weighted-dominance` takes `hCbd₁` on the upper group's own `e_1` and `hamp₁`
on a window of its own, so nothing forces the two to be produced together.  They
are anyway, for the reason `EndpointUpperGap.exists_upper_endpoint_block` gives:
two independent existentials let a consumer pair one producer's radius with the
other's window, which typechecks and means nothing.  Here the collision point `L`
is bound once — the amplitude hypothesis is about the point the contour bound's
limiting pencil is built at — and one `e_1` serves both. -/

/-- **The `r = 1` upper endpoint's two binders, against one window and one `L`.**
`hCbd₁` at every radius past the zeros of the limiting pencil, and `hamp₁` at
every `A_1` with `p_1 = 0`, on the same `(0, e_1]`. -/
theorem exists_upper_endpoint_binders_one {n : ℕ} {a : Fin n → ℝ} {c x₁ : ℝ}
    {B : Polynomial ℂ} (hn2 : 2 ≤ n) (ha : ∀ k, 0 < a k) (hc : 0 < c) :
    ∃ L : ℝ, 0 < L ∧ (ftCriticalReal (ftRootPolyReal c a) 1).eval (-L) = 0 ∧
      ∃ R₀ > (0 : ℝ), ∀ R₁ : ℝ, R₀ ≤ R₁ → ∀ A₁ : ℝ, B.eval ((-L : ℝ) : ℂ) ≠ 0 →
        ∃ C₁, 0 ≤ C₁ ∧ ∃ e₁ > (0 : ℝ),
          (∀ δ : ℝ, 0 < δ → δ ≤ e₁ → ∀ t ∈ Metric.sphere (0 : ℂ) R₁,
            (ftDen (ftRootPoly c a) 1
                ((ftBranchZ a c 1 (n - 1) (π - δ) : ℝ) : ℂ)).eval t ≠ 0 ∧
              ‖B.eval t / (ftDen (ftRootPoly c a) 1
                ((ftBranchZ a c 1 (n - 1) (π - δ) : ℝ) : ℂ)).eval t‖ ≤ C₁) ∧
          (∀ η : ℝ, 0 < η → η ≤ e₁ →
            A₁ * η ^ 0 ≤ ftPrincipalAmp (ftRootPoly c a) B 1 (ftBranchZ a c 1 (n - 1))
              (ftTauArc a 1 (n - 1) x₁) (π - η)) := by
  obtain ⟨L, hL, hE, hτ, hz⟩ := exists_endpoint_limits_pi hn2 ha hc
  obtain ⟨R₀, hR₀, hroots⟩ := exists_radius_above_roots_endpoint_pi hc.ne' ha L
  refine ⟨L, hL, hE, R₀, hR₀, fun R₁ hR₁ A₁ hBL => ?_⟩
  obtain ⟨C₁, hC₁, eC, heC, hC⟩ :=
    exists_upper_contour_bound_one_of_zero_free (B := B) (L := L) hz
      (lt_of_lt_of_le hR₀ hR₁) (hroots R₁ hR₁)
  obtain ⟨eA, heA, hA⟩ :=
    ftPrincipalAmp_floor_of_endpoint_pi (x₁ := x₁) (B := B) hn2 ha hc hL hE hτ hz hBL A₁
  exact ⟨C₁, hC₁, min eC eA, lt_min heC heA,
    fun δ hδ hδe t ht => hC δ hδ (le_trans hδe (min_le_left _ _)) t ht,
    fun η hη hηe => hA η hη (le_trans hηe (min_le_right _ _))⟩

/-- **The two binders at `n = 3` and the retained set's own radius `2L`.**  This is
the consumable form: `n₁ = 0` there, so `hCbd₁` and the retained-set group are
about one circle, and one `L` and one window serve both binders.

The deficit equation `∑_k L/(a_k+L) = 1` that `EndpointUpperOne`'s circle needs is
discharged here rather than assumed — `sum_div_add_eq_of_eval_ftCriticalReal_neg`
gets it from `E(-L) = 0`, which the same `L` already carries.  `B(-L) ≠ 0` is
`hamp₁`'s and is the only hypothesis left, stated about the `L` handed back; both
binders are built from that one `L`'s limits rather than from two producers'
independent ones. -/
theorem exists_upper_endpoint_binders_one_two_mul {a : Fin 3 → ℝ} {c x₁ : ℝ}
    {B : Polynomial ℂ} (ha : ∀ k, 0 < a k) (hc : 0 < c) :
    ∃ L : ℝ, 0 < L ∧ (ftCriticalReal (ftRootPolyReal c a) 1).eval (-L) = 0 ∧
      (B.eval ((-L : ℝ) : ℂ) ≠ 0 → ∀ A₁ : ℝ,
        ∃ C₁, 0 ≤ C₁ ∧ ∃ e₁ > (0 : ℝ),
          (∀ δ : ℝ, 0 < δ → δ ≤ e₁ → ∀ t ∈ Metric.sphere (0 : ℂ) (2 * L),
            (ftDen (ftRootPoly c a) 1
                ((ftBranchZ a c 1 2 (π - δ) : ℝ) : ℂ)).eval t ≠ 0 ∧
              ‖B.eval t / (ftDen (ftRootPoly c a) 1
                ((ftBranchZ a c 1 2 (π - δ) : ℝ) : ℂ)).eval t‖ ≤ C₁) ∧
          (∀ η : ℝ, 0 < η → η ≤ e₁ →
            A₁ * η ^ 0 ≤ ftPrincipalAmp (ftRootPoly c a) B 1 (ftBranchZ a c 1 2)
              (ftTauArc a 1 2 x₁) (π - η))) := by
  obtain ⟨L, hL, hE, hτ, hz⟩ :=
    exists_endpoint_limits_pi (a := a) (c := c) (by norm_num) ha hc
  have hsum1 : ∑ k, L / (a k + L) = 1 := by
    simpa using sum_div_add_eq_of_eval_ftCriticalReal_neg (r := 1) ha hc hL hE
  refine ⟨L, hL, hE, fun hBL A₁ => ?_⟩
  obtain ⟨C₁, hC₁, eC, heC, hC⟩ :=
    exists_upper_contour_bound_one_of_zero_free (B := B) (L := L) hz
      (by positivity) (eval_ne_zero_on_sphere_two_mul_endpoint_pi ha hc hL hE hsum1)
  obtain ⟨eA, heA, hA⟩ :=
    ftPrincipalAmp_floor_of_endpoint_pi (x₁ := x₁) (B := B) (by norm_num) ha hc hL hE hτ hz
      hBL A₁
  exact ⟨C₁, hC₁, min eC eA, lt_min heC heA,
    fun δ hδ hδe t ht => hC δ hδ (le_trans hδe (min_le_left _ _)) t ht,
    fun η hη hηe => hA η hη (le_trans hηe (min_le_right _ _))⟩

/-! ### The retained set at `r = 1`

`n₁ = r - 2 = 0` here: the circle of radius `2L` holds the principal pair and
nothing else, so the retained cluster is empty and `g₁` is a map out of `Fin 0`.

**Which clauses that leaves carrying content, and which it empties.**  Every
binder quantified over `Fin n₁` — `hL₁`, `hratio₁`, `hgapin₁`, `hginj₁`, `hgmem₁`
— is discharged by `Fin.elim0` and tests nothing; `hcl₁` becomes `0 ≤ W/4`.  What
is left is exactly the statement about the pair and the circle, and it is all of
the content: `hroot₁` and `hsimple₁` say the two points are simple zeros,
`haR₁` puts them inside `2L`, `huniq₁` says the disk holds no third zero, and
`hgcard₁` — `card = 0` after erasing both — is where the count `2` is actually
spent.  Those five are proved below from `EndpointUpperOne`'s count rather than
inherited from the `2 ≤ r` packaging, which would have discharged the empty ones
and left the others untested. -/

/-- The circle stays zero-free for the branch pencil, not just for the limiting
one.  `exists_contour_bound_of_tendsto` at `B = 1`, whose conclusion carries the
non-vanishing precisely so a consumer need not re-derive it. -/
theorem eventually_eval_ftDen_ne_zero_on_sphere_of_tendsto {Q : Polynomial ℂ} {r : ℕ}
    {zb : ℂ} {w : ℝ → ℂ} (hw : Tendsto w (𝓝[>] (0 : ℝ)) (𝓝 zb)) {R : ℝ} (hR : 0 < R)
    (hne : ∀ t : ℂ, ‖t‖ = R → (ftDen Q r zb).eval t ≠ 0) :
    ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∀ t : ℂ, ‖t‖ = R → (ftDen Q r (w δ)).eval t ≠ 0 := by
  obtain ⟨_C, -, e, he, h⟩ := exists_contour_bound_of_tendsto (B := 1) hw hR hne
  filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT he] with δ hδ hδe
  exact fun t ht => (h δ hδ hδe.2.le t
    (by simpa [Complex.dist_eq, sub_zero] using ht)).1

/-- **The retained upper set at `r = 1`, eventually.**  The pair
`{t_+, t_-}` is exactly the zero set of the pencil in the closed disk of radius
`2L`, and both members are simple.

`EndpointUpperOne.eventually_card_rootsIn_eq_two_near_pi` supplies the count with
multiplicity; `EndpointSeparation.simple_and_complete_of_count` turns it into
simplicity and completeness once the pair is exhibited inside and the circle is
zero-free.  The circle's zero-freeness is at the BRANCH pencil, which is
`eventually_eval_ftDen_ne_zero_on_sphere_of_tendsto` rather than
`eval_ne_zero_on_sphere_two_mul_endpoint_pi` — the latter is the limiting pencil
and is what that one is proved from.

**The window is punctured and must stay so.**  Simplicity holds at every `δ > 0`,
but it degenerates in the limit: `∂_tD(t_+)` vanishes **linearly** as `δ → 0`,
because the pair collides at `-L` where the limiting pencil has its double root.
So the closed-window form of this statement — at `δ = 0` — is FALSE, and a later
pass that strengthens the puncture away would be proving something untrue.  It is
the same collision that makes `hamp₁`'s amplitude diverge, so the two cannot both
be extended to the endpoint.  Measured at three pencils, slope `1`, in
`scripts/check_upper_retained_r_one.py`. -/
theorem eventually_upper_retained_one {a : Fin 3 → ℝ} {c x₁ : ℝ}
    (ha : ∀ k, 0 < a k) (hc : 0 < c) {L : ℝ} (hL : 0 < L)
    (hE : (ftCriticalReal (ftRootPolyReal c a) 1).eval (-L) = 0)
    (hτ : Tendsto (ftTau a 1 2) (𝓝[<] π) (𝓝 L))
    (hz : Tendsto (ftBranchZ a c 1 2) (𝓝[<] π)
      (𝓝 (-(ftRootPolyReal c a).eval (-L) / (-L)))) :
    ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      0 < ftTauArc a 1 2 x₁ (π - δ) ∧
      ftTauArc a 1 2 x₁ (π - δ) ≤ 3 * L / 2 ∧
      (ftDen (ftRootPoly c a) 1 ((ftBranchZ a c 1 2 (π - δ) : ℝ) : ℂ)).eval
        (ftPrincipal (ftTauArc a 1 2 x₁) (π - δ)) = 0 ∧
      ftPrincipal (ftTauArc a 1 2 x₁) (π - δ) ≠
        ((ftTauArc a 1 2 x₁ (π - δ) : ℝ) : ℂ) * Complex.exp (-((π - δ : ℝ) : ℂ) * I) ∧
      (∀ w ∈ ({ftPrincipal (ftTauArc a 1 2 x₁) (π - δ),
          ((ftTauArc a 1 2 x₁ (π - δ) : ℝ) : ℂ) *
            Complex.exp (-((π - δ : ℝ) : ℂ) * I)} : Finset ℂ),
        (ftDen (ftRootPoly c a) 1 ((ftBranchZ a c 1 2 (π - δ) : ℝ) : ℂ)).eval w = 0 ∧
          ‖w‖ < 2 * L ∧
          (derivative (ftDen (ftRootPoly c a) 1
            ((ftBranchZ a c 1 2 (π - δ) : ℝ) : ℂ))).eval w ≠ 0) ∧
      (∀ t : ℂ, ‖t‖ ≤ 2 * L →
        (ftDen (ftRootPoly c a) 1 ((ftBranchZ a c 1 2 (π - δ) : ℝ) : ℂ)).eval t = 0 →
        t ∈ ({ftPrincipal (ftTauArc a 1 2 x₁) (π - δ),
          ((ftTauArc a 1 2 x₁ (π - δ) : ℝ) : ℂ) *
            Complex.exp (-((π - δ : ℝ) : ℂ) * I)} : Finset ℂ)) := by
  classical
  have hsum1 : ∑ k, L / (a k + L) = 1 := by
    simpa using sum_div_add_eq_of_eval_ftCriticalReal_neg (r := 1) ha hc hL hE
  have hcast : π / ((1 : ℕ) : ℝ) = π := pi_div_natCast_one
  -- the arc data, in the chart
  have harc : ∀ᶠ δ in 𝓝[>] (0 : ℝ), π - δ ∈ Ioo 0 (π / ((1 : ℕ) : ℝ)) := by
    filter_upwards [Ioo_mem_nhdsGT pi_pos] with δ hδπ
    rw [hcast]
    exact ⟨by linarith [hδπ.2], by linarith [hδπ.1]⟩
  have hagree : ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      ftTauArc a 1 2 x₁ (π - δ) = ftTau a 1 2 (π - δ) := by
    filter_upwards [harc] with δ hδ
    exact ftTauArc_agree a 1 2 x₁ hδ.1 hδ.2
  -- the branch's root and positivity across the open arc
  obtain ⟨hrootA, hposA⟩ :=
    ft_branch_root_and_pos (a := a) (r := 1) c (by omega) ha le_rfl (Or.inl (by norm_num))
  -- the radius stays below `3L/2`
  have hTsmall : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ftTau a 1 2 (π - δ) < 3 * L / 2 := by
    filter_upwards [Metric.tendsto_nhds.mp (hτ.comp tendsto_sub_nhdsGT_zero_nhdsLT)
      (L / 2) (by linarith)] with δ hδ
    simp only [Function.comp_apply, Real.dist_eq, abs_lt] at hδ
    linarith [hδ.2]
  -- the circle of radius `2L` is zero-free for the branch pencil
  have hsphere : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∀ t : ℂ, ‖t‖ = 2 * L →
      (ftDen (ftRootPoly c a) 1 ((ftBranchZ a c 1 2 (π - δ) : ℝ) : ℂ)).eval t ≠ 0 := by
    refine eventually_eval_ftDen_ne_zero_on_sphere_of_tendsto
      ((Complex.continuous_ofReal.tendsto _).comp (hz.comp tendsto_sub_nhdsGT_zero_nhdsLT))
      (by positivity) (fun t ht => ?_)
    exact eval_ne_zero_on_sphere_two_mul_endpoint_pi ha hc hL hE hsum1 t
      (by simpa [Complex.dist_eq, sub_zero] using ht)
  -- the count, transported through the chart
  have hcountθ : ∀ᶠ θ in 𝓝[<] π,
      (Shields.rootsIn (ftDen (ftRootPoly c a) 1
        ((ftBranchZ a c 1 2 θ : ℝ) : ℂ)) 0 (2 * L)).card = 2 := by
    refine eventually_card_rootsIn_eq_two_near_pi (l := 2) ha hc hL ?_ hτ hE hsum1
    filter_upwards [Ioo_mem_nhdsLT pi_pos] with θ hθ
    refine ⟨hθ, ftBranchAt_of_arc_principal (by omega) ha le_rfl (Or.inl (by norm_num)) ?_⟩
    rw [hcast]; exact hθ
  have hcount := (tendsto_sub_nhdsGT_zero_nhdsLT (b := π)).eventually hcountθ
  filter_upwards [harc, hagree, hTsmall, hsphere, hcount] with δ hδarc hδag hδsm hδsp hδct
  have hπarc : (π - δ) ∈ Ioo (0 : ℝ) π := by
    refine ⟨hδarc.1, ?_⟩
    have h := hδarc.2; rwa [hcast] at h
  have hTpos : 0 < ftTauArc a 1 2 x₁ (π - δ) := by rw [hδag]; exact hposA _ hδarc
  have hTle : ftTauArc a 1 2 x₁ (π - δ) ≤ 3 * L / 2 := by rw [hδag]; exact hδsm.le
  have hPeq : ftPrincipal (ftTauArc a 1 2 x₁) (π - δ)
      = ftPrincipal (ftTau a 1 2) (π - δ) := by
    rw [ftPrincipal, ftPrincipal, hδag]
  have hProot : (ftDen (ftRootPoly c a) 1 ((ftBranchZ a c 1 2 (π - δ) : ℝ) : ℂ)).eval
      (ftPrincipal (ftTauArc a 1 2 x₁) (π - δ)) = 0 := by
    rw [hPeq]; exact hrootA _ hδarc
  have hCjeq : ((ftTauArc a 1 2 x₁ (π - δ) : ℝ) : ℂ) * Complex.exp (-((π - δ : ℝ) : ℂ) * I)
      = (starRingEnd ℂ) (ftPrincipal (ftTauArc a 1 2 x₁) (π - δ)) :=
    (conj_ftPrincipal' (ftTauArc a 1 2 x₁) (π - δ)).symm
  have hne : ftPrincipal (ftTauArc a 1 2 x₁) (π - δ) ≠
      ((ftTauArc a 1 2 x₁ (π - δ) : ℝ) : ℂ) * Complex.exp (-((π - δ : ℝ) : ℂ) * I) := by
    rw [hCjeq]
    exact ftPrincipal_ne_conj_of_pos hTpos hπarc
  have hCjroot : (ftDen (ftRootPoly c a) 1 ((ftBranchZ a c 1 2 (π - δ) : ℝ) : ℂ)).eval
      (((ftTauArc a 1 2 x₁ (π - δ) : ℝ) : ℂ) * Complex.exp (-((π - δ : ℝ) : ℂ) * I)) = 0 := by
    rw [hCjeq]
    exact ftDen_eval_conj_eq_zero (hasRealCoeffs_ftRootPoly c a) hProot
  have hPnorm : ‖ftPrincipal (ftTauArc a 1 2 x₁) (π - δ)‖ = ftTauArc a 1 2 x₁ (π - δ) :=
    norm_ftPrincipal_eq hTpos
  have hCjnorm : ‖((ftTauArc a 1 2 x₁ (π - δ) : ℝ) : ℂ) *
      Complex.exp (-((π - δ : ℝ) : ℂ) * I)‖ = ftTauArc a 1 2 x₁ (π - δ) := by
    rw [hCjeq]; simpa using hPnorm
  have hlt : ftTauArc a 1 2 x₁ (π - δ) < 2 * L := by linarith
  have hDne : ftDen (ftRootPoly c a) 1 ((ftBranchZ a c 1 2 (π - δ) : ℝ) : ℂ) ≠ 0 :=
    ftDen_one_ne_zero_of_real hc.ne' ha _
  have hTcard : (({ftPrincipal (ftTauArc a 1 2 x₁) (π - δ),
      ((ftTauArc a 1 2 x₁ (π - δ) : ℝ) : ℂ) *
        Complex.exp (-((π - δ : ℝ) : ℂ) * I)} : Finset ℂ)).card = 2 := by
    rw [Finset.card_insert_of_notMem (by simpa using hne), Finset.card_singleton]
  have hTmem : ∀ w ∈ ({ftPrincipal (ftTauArc a 1 2 x₁) (π - δ),
      ((ftTauArc a 1 2 x₁ (π - δ) : ℝ) : ℂ) *
        Complex.exp (-((π - δ : ℝ) : ℂ) * I)} : Finset ℂ),
      (ftDen (ftRootPoly c a) 1 ((ftBranchZ a c 1 2 (π - δ) : ℝ) : ℂ)).eval w = 0 ∧
        ‖w‖ < 2 * L := by
    intro w hw
    rcases Finset.mem_insert.1 hw with rfl | hw
    · exact ⟨hProot, by rw [hPnorm]; exact hlt⟩
    · rw [Finset.mem_singleton] at hw
      subst hw
      exact ⟨hCjroot, by rw [hCjnorm]; exact hlt⟩
  obtain ⟨hsimp, huniq⟩ :=
    simple_and_complete_of_count hDne hδct (fun t ht => hδsp t ht) hTcard hTmem
  exact ⟨hTpos, hTle, hProot, hne,
    fun w hw => ⟨(hTmem w hw).1, (hTmem w hw).2, hsimp w hw⟩, huniq⟩

/-! ### Shape check against the consumer's own binder types

Each producer above is a *claim* about what it delivers, and a claim in this shape
fails by succeeding: a binder built by symmetry with the `2 \le r` one typechecks,
passes the axiom guard, and is the wrong statement.  What tests it is feeding it to
the binder it was written for, in that binder's own type.

The named arguments below elaborate
`weighted_dominance_of_branch_any_multiplicity_at_of_threshold` at `r = 1` with
`hA₁`, `hamp₁`, `hC₁` and `hCbd₁` supplied and every other binder left open, so a
drift in any of the four shapes fails this file.  `p₁ = 0`, `A₁ = 1`, and the
radius, window and contour constant are the ones the block returned. -/

example {n : ℕ} {a : Fin n → ℝ} {c xb : ℝ} {B : Polynomial ℂ}
    (hn2 : 2 ≤ n) (ha : ∀ k, 0 < a k) (hc : 0 < c) : True := by
  obtain ⟨L, -, -, Rb, hRb, hbind⟩ :=
    exists_upper_endpoint_binders_one (x₁ := xb) (B := B) hn2 ha hc
  by_cases hBL : B.eval ((-L : ℝ) : ℂ) = 0
  · trivial
  obtain ⟨C, hC, e, he, hCbd, hamp⟩ := hbind (Rb + 1) (by linarith) 1 hBL
  have _shape := weighted_dominance_of_branch_any_multiplicity_at_of_threshold
    (Q := ftRootPoly c a) (B := B) (r := 1) (b := π) (z := ftBranchZ a c 1 (n - 1))
    (τ := ftTauArc a 1 (n - 1) xb)
    -- the four binders this module owns
    (R₁ := Rb + 1) (e₁ := e) (C₁ := C) (A₁ := 1) (p₁ := 0)
    (hA₁ := one_pos) (hC₁ := hC)
    (hCbd₁ := fun δ hδ hδe t ht => (hCbd δ hδ hδe t ht).2)
    (hamp₁ := ⟨e, he, hamp⟩)
    -- everything else is another lane's; pinned only so the elaborator has values
    (n₀ := 0) (n₁ := 0) (g₀ := fun _ _ => 0) (g₁ := fun _ _ => 0)
    (sfun₀ := fun _ => ∅) (sfun₁ := fun _ => ∅) (x₁ := 1) (ρ := 2)
    (te₀ := 1) (γe₀ := 1) (idx₀ := fun _ => 0) (jp₀ := 0) (νB₀ := 0)
    (cB₀ := 1) (cQ₀ := 1) (R₀ := 1) (τmax₀ := 1) (σ₀ := 1) (e₀ := 1) (C₀ := 0)
    (L₁ := fun _ => 1) (τmax₁ := 1) (σ₁ := 1) (c₀ := 0) (c₁ := 0) (h := 1)
  trivial

/-- **Shape check: the whole upper group at `r = 1`, `n₁ = 0`.**  The previous
example tests the two binders this module set out to prove; this one tests the
block they sit in — the retained set, the radius and the window included — because
a `Fin 0` binder is met by `Fin.elim0` without testing anything, so the block
cannot be trusted to build merely because its empty clauses do.

`R₁ = 2L`, `τmax₁ = 3L/2`, `σ₁ = 3/4`, `n₁ = 0`, `p₁ = 0`, `A₁ = 1`.  Only the
`_0` group and the interior are left open. -/
example {a : Fin 3 → ℝ} {c xb : ℝ} {B : Polynomial ℂ}
    (ha : ∀ k, 0 < a k) (hc : 0 < c) : True := by
  classical
  obtain ⟨L, hL, hE, hτ, hz⟩ := exists_endpoint_limits_pi (a := a) (c := c) (by norm_num) ha hc
  have hsum1 : ∑ k, L / (a k + L) = 1 := by
    simpa using sum_div_add_eq_of_eval_ftCriticalReal_neg (r := 1) ha hc hL hE
  by_cases hBL : B.eval ((-L : ℝ) : ℂ) = 0
  case pos => trivial
  obtain ⟨eR, heR, hret⟩ := window_of_eventually
    (eventually_upper_retained_one (x₁ := xb) ha hc hL hE hτ hz)
  obtain ⟨C₁, hC₁, eC, heC, hC⟩ :=
    exists_upper_contour_bound_one_of_zero_free (B := B) (L := L) hz
      (by positivity) (eval_ne_zero_on_sphere_two_mul_endpoint_pi ha hc hL hE hsum1)
  obtain ⟨eA, heA, hA⟩ :=
    ftPrincipalAmp_floor_of_endpoint_pi (x₁ := xb) (B := B) (by norm_num) ha hc hL hE hτ hz hBL 1
  set e₁ : ℝ := min eR (min eC eA) with he₁def
  have he₁ : 0 < e₁ := lt_min heR (lt_min heC heA)
  have hR : ∀ δ : ℝ, 0 < δ → δ ≤ e₁ → _ :=
    fun δ hδ hδe => hret δ hδ (le_trans hδe (min_le_left _ _))
  have _shape := weighted_dominance_of_branch_any_multiplicity_at_of_threshold
    (Q := ftRootPoly c a) (B := B) (r := 1) (b := π) (z := ftBranchZ a c 1 2)
    (τ := ftTauArc a 1 2 xb)
    -- the retained upper set: the principal pair, and nothing else inside `2L`
    (n₁ := 0) (g₁ := fun _ _ => 0)
    (sfun₁ := fun δ => {ftPrincipal (ftTauArc a 1 2 xb) (π - δ),
      ((ftTauArc a 1 2 xb (π - δ) : ℝ) : ℂ) * Complex.exp (-((π - δ : ℝ) : ℂ) * I)})
    (R₁ := 2 * L) (τmax₁ := 3 * L / 2) (σ₁ := 3 / 4) (e₁ := e₁)
    (hR₁ := by positivity)
    (hσ₁ := by rw [div_le_iff₀ (by positivity : (0:ℝ) < 2 * L)]; nlinarith)
    (hσ₁1 := by norm_num) (he₁ := he₁)
    (hτpos₁ := fun δ hδ hδe => (hR δ hδ hδe).1)
    (hτle₁ := fun δ hδ hδe => (hR δ hδ hδe).2.1)
    (hroot₁ := fun δ hδ hδe w hw => ((hR δ hδ hδe).2.2.2.2.1 w hw).1)
    (haR₁ := fun δ hδ hδe w hw => ((hR δ hδ hδe).2.2.2.2.1 w hw).2.1)
    (hsimple₁ := fun δ hδ hδe w hw => ((hR δ hδ hδe).2.2.2.2.1 w hw).2.2)
    (huniq₁ := fun δ hδ hδe t ht h0 => (hR δ hδ hδe).2.2.2.2.2 t ht h0)
    (hrootplus₁ := fun δ hδ hδe => (hR δ hδ hδe).2.2.1)
    (hne₁ := fun δ hδ hδe => (hR δ hδ hδe).2.2.2.1)
    (hginj₁ := fun δ _ _ => Function.injective_of_subsingleton _)
    (hgmem₁ := fun δ _ _ i => i.elim0)
    (hgcard₁ := fun δ hδ hδe => by
      rw [Finset.erase_insert (by simpa using (hR δ hδ hδe).2.2.2.1),
        Finset.erase_singleton, Finset.card_empty])
    -- the cluster group, empty here
    (L₁ := fun i => i.elim0) (hL₁ := fun i => i.elim0) (hratio₁ := fun i => i.elim0)
    (c₁ := 0) (hgapin₁ := ⟨1, one_pos, fun δ _ _ i => i.elim0⟩)
    (hcl₁ := ⟨1, one_pos, fun A ζ' η W _ _ hW _ _ M _ => by simpa using by linarith⟩)
    -- the two binders this module proves
    (A₁ := 1) (p₁ := 0) (hA₁ := one_pos) (C₁ := C₁) (hC₁ := hC₁)
    (hCbd₁ := fun δ hδ hδe t ht =>
      (hC δ hδ (le_trans hδe (le_trans (min_le_right _ _) (min_le_left _ _))) t ht).2)
    (hamp₁ := ⟨e₁, he₁, fun η hη hηe =>
      hA η hη (le_trans hηe (le_trans (min_le_right _ _) (min_le_right _ _)))⟩)
    -- everything else is another lane's; pinned only so the elaborator has values
    (n₀ := 0) (g₀ := fun _ _ => 0) (sfun₀ := fun _ => ∅) (x₁ := 1) (ρ := 2)
    (te₀ := 1) (γe₀ := 1) (idx₀ := fun _ => 0) (jp₀ := 0) (νB₀ := 0)
    (cB₀ := 1) (cQ₀ := 1) (R₀ := 1) (τmax₀ := 1) (σ₀ := 1) (e₀ := 1) (C₀ := 0)
    (c₀ := 0) (h := 1)
  trivial

end ForgacsTran
