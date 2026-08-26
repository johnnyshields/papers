/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import ForgacsTran.FTMinModulus.ScaleMatching

/-!
# Proposition 3 Case 3, and the endpoint limits of the branch value

The upper endpoint of the viewing arc, where the branch radius collapses, and the
endpoint limits of `z` that `Propositions`' Lemma 6 statement consumes.  With
these two the interval `(a,b)` of `eq:ab-def` is identified.

## Main statements

* the statements of `### Forgacs2017RationalDenominator Prop. 3, Case 3` — the
  upper endpoint, where the collapse of the radius rather than a collision is
  what has to be controlled.
* the statements of `### Forgacs2017RationalDenominator Lemma 6 — the endpoint
  limits of z` — the two limits, in the form `image_Ioo_eq_Ioo_of_tendsto` takes.

## Case 3, where it stands and how to resume

**State.** Every mathematical step from the `z`-free relation to
`zeta_j = nu (1 + c delta) + O(delta^2)` is proved here and compiles:
`exists_upper_ratio_close`, `exists_upper_ratio_bound`,
`exists_ratio_second_order_bound`, `norm_one_add_pow_sub_linear_le`,
`norm_nat_mul_sub_le_of_pow_eq`, `norm_sub_beta_mul_le`,
`norm_mul_linear_expansion_le`, and `norm_upper_member_expansion_le` composing
them.  No `sorry`.  What is *not* done is the instantiation: binding those to the
branch and applying `abs_norm_sub_one_add_re_mul_le_of_unimodular` to reach
`hexp_1`.  Naming, not estimating -- every constant is explicit and every step
pointwise.

**The three inputs.**
* `T` -- `EndpointRegularity.exists_infiniteEndpoint_form`, from `gamma 0 = 0`
  plus a one-sided derivative; gives `ContinuousWithinAt T (Set.Ici 0) 0`,
  `T 0 != 0`.
* `gamma 0 = 0` -- `FTBranchUpperRefutation.not_upper_endpoint_datum_ne_zero`,
  for every `n >= 2`, `r >= 2`.  The fact that refuted the old binder is the
  hypothesis the new route needs.
* the tau-rate -- `FTBranchUpper.exists_bound_ftTau_upper`, pointwise second
  order, `L = r/(sin(pi/r) S)` with `S = sum 1/a_k`.

`hamp_1` at `r >= 2` is `Amplitude.amplitude_lower_bound_of_origin_form`, exponent
`1`.  `weighted_dominance_of_branch` no longer chooses a route: it takes the
amplitude and contour bounds directly.

**Two traps already paid for, neither visible in the code.**

*The `e^(-i delta)` rotation must be split into `c`, never absorbed into `nu`.*
`nu` is `delta`-free but `t_p/tau = e^(i(pi/r - delta))` is not, and they differ
at first order.  Absorbing it hands the transfer lemma a *moving* unimodular
limit and the coefficient comes out short by exactly `-i` -- invisible in the
conclusion, since only `Re c` reaches `hexp_1`.  A wrong number, not a failed
proof.

*A witness at `n = 1` cannot discharge anything routed through the upper
tau-rate.*  `exists_bound_ftTau_upper` needs `2 <= n`, and `Q(t) = 1 - t` -- the
natural smallest upper pencil, and the one the `r = 3` cluster witness uses --
has one root.  "Instantiate at the witness we already have" fails at `hn2` after
the work rather than before it.

**The `S` cancels, and that is the check that the composition is right rather
than merely typechecking.**  The rate carries `S`, the ratio carries `beta = -S`,
and `Re c = (cos(pi/r) - Re nu)/sin(pi/r)` is pencil-free because both do.  A
version losing one would pass at `Q = 1 - t`, where `S = 1`, and fail everywhere
else; `scripts/check_upper_cluster_expansion.py` refutes the `S`-free rate at
four pencils for exactly that reason.

## References

* `../../shields-2026-forgacs-tran-numerators.tex`, «Spectral geometry, residues,
  and the principal amplitude» — `sec:geometry`, `thm:FT-geometry`, `eq:ab-def`.
* `Forgacs2017RationalDenominator`, Proposition 3 Case 3 and Lemma 6.

## Tags

upper endpoint, branch radius, endpoint limit, Forgacs-Tran interval
-/

namespace ForgacsTran

open Polynomial

/-! ### `Forgacs2017RationalDenominator` Prop. 3, Case 3 — the upper endpoint

Above `r = 1` the branch point runs into the origin, so the cluster forms there
rather than at a zero of `Q`, and the model is `Q(0) + zt^r` — no factorization
of `Q` enters and `ρ` plays no part.  The generic half of the lower endpoint's
machinery carries over unchanged: `model_norm_ge_of_near_root` never mentions
`x_1`, and `exists_root_of_dominated` never mentions the pencil.

What is different is the *shape* of the domination, and it is simpler.  On a
circle of radius `κ‖u‖` about a model root, the model is at least
`‖z‖(r/2)κ‖u‖^ρ`, and `‖z‖‖u‖^r = ‖Q(0)‖` exactly — so that lower bound is the
**constant** `(r/2)κ‖Q(0)‖`, while the perturbation `Q(t) - Q(0)` is `O(‖u‖)`.
The lower endpoint needed the two sides compared at the same power of `δ`; here
one side does not move at all.

**A witness at `n = 1` cannot discharge anything routed through the upper
τ-rate.**  `FTBranchUpper.exists_bound_ftTau_upper` requires `2 ≤ n`, and
`Q(t) = 1 - t` — the natural smallest upper-endpoint pencil, and the one the
`r = 3` upper cluster witness uses — has a single root.  That witness reaches
`hexp₁` by a different road, from Vieta and the closed forms of `τ` and the third
root, so it is not in conflict with anything here; but it is not an instance of
this route either, and "instantiate the composition at the witness we already
have" would fail at `hn2` after the work rather than before it.  A witness for
this route needs `n ≥ 2`. -/

/-- **The upper-endpoint perturbation, decomposed exactly.**  Against the model
`Q(0) + zt^r` the pencil differs by exactly `Q(t) - Q(0)`, and nothing else:
the `zt^r` cancels identically.  There is no factorization step, which is why
Case 3 needs no analogue of `ftRootPoly_factor_of_fiber`. -/
theorem norm_pencil_sub_origin_model_le {Q : ℂ[X]} {r : ℕ} {z t : ℂ} :
    (ftDen Q r z).eval t - (Q.eval 0 + z * t ^ r) = Q.eval t - Q.eval 0 := by
  rw [ftDen_eval]
  ring

/-- **Each upper cluster direction carries a pencil root.**  `u` is a root of the
model `zw^r + Q(0)`, and on the circle of radius `κ‖u‖` about it the model beats
the increment `Q(t) - Q(0)`.

`hdom` compares a quantity that vanishes with `‖u‖` against one that does not:
the right-hand side is `(r/2)κ‖Q(0)‖`, free of `z` and of `u`, because
`‖z‖‖u‖^r = ‖Q(0)‖` holds exactly at a model root.  So the hypothesis is
satisfied as soon as the branch point is close enough to the origin, which at
the upper endpoint is what `FTBranchUpper.tendsto_ftTau_nhdsLT_upper` gives. -/
theorem exists_ftDen_root_near_origin_model_root {Q : ℂ[X]} {r : ℕ} (hr : 1 ≤ r)
    (hQ0 : Q.eval 0 ≠ 0) {z u : ℂ} {κ M : ℝ} (hz : z ≠ 0)
    (hroot : z * u ^ r + Q.eval 0 = 0) (hκ : 0 < κ) (hκ4 : κ * (4 * r) ≤ 1)
    (hM : (1 + κ) * ‖u‖ ≤ M)
    (hdom : (∑ k ∈ Finset.range (Q.natDegree + 1), ‖Q.coeff k‖ * ((k : ℝ) * M ^ (k - 1)))
        * ((1 + κ) * ‖u‖) < (r : ℝ) / 2 * κ * ‖Q.eval 0‖) :
    ∃ t : ℂ, ‖t - u‖ < κ * ‖u‖ ∧ (ftDen Q r z).eval t = 0 := by
  have hu : u ≠ 0 := (model_root_simple hr hQ0 hz hroot).1
  have hu0 : (0 : ℝ) < ‖u‖ := norm_pos_iff.mpr hu
  have hR0 : (0 : ℝ) < κ * ‖u‖ := mul_pos hκ hu0
  set L : ℝ := ∑ k ∈ Finset.range (Q.natDegree + 1), ‖Q.coeff k‖ * ((k : ℝ) * M ^ (k - 1))
    with hL
  have hM0 : (0 : ℝ) ≤ M := le_trans (by positivity) hM
  have hL0 : 0 ≤ L := by
    rw [hL]
    exact Finset.sum_nonneg fun k _ =>
      mul_nonneg (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg k) (pow_nonneg hM0 _))
  -- the model's modulus on the circle is a constant
  have hnu : ‖u‖ ^ r * ‖z‖ = ‖Q.eval 0‖ := norm_model_root_pow hroot
  set Mp : ℂ[X] := C z * X ^ r + C (Q.eval 0) with hMp
  have hMpeval : ∀ w : ℂ, Mp.eval w = Q.eval 0 + z * w ^ r := by
    intro w
    simp only [hMp, eval_add, eval_mul, eval_pow, eval_C, eval_X]
    ring
  have hdomsp : ∀ w ∈ Metric.sphere u (κ * ‖u‖),
      ‖(ftDen Q r z - Mp).eval w‖ < ‖Mp.eval w‖ := by
    intro w hw
    have hws : ‖w - u‖ = κ * ‖u‖ := by
      rw [← dist_eq_norm]
      exact Metric.mem_sphere.mp hw
    have hwM : ‖w‖ ≤ (1 + κ) * ‖u‖ := by
      have hsplit : w = (w - u) + u := by ring
      calc ‖w‖ = ‖(w - u) + u‖ := by rw [← hsplit]
        _ ≤ ‖w - u‖ + ‖u‖ := norm_add_le _ _
        _ = (1 + κ) * ‖u‖ := by rw [hws]; ring
    have hwMM : ‖w‖ ≤ M := le_trans hwM hM
    -- the increment
    have hginc : ‖(ftDen Q r z - Mp).eval w‖ ≤ L * ‖w‖ := by
      rw [eval_sub, hMpeval w, norm_pencil_sub_origin_model_le]
      have h0M : ‖(0 : ℂ)‖ ≤ M := by simpa using hM0
      have hq := norm_eval_sub_eval_le_of_norm_le (q := Q) (M := M) hwMM h0M
      rw [← hL, sub_zero] at hq
      exact hq
    -- the model
    have hfge := model_norm_ge_of_near_root (c₀ := Q.eval 0) (c₁ := z) (u := u) (v := w)
      hr hQ0 hz hroot (by rw [hws]; nlinarith only [hκ4, hu0, norm_nonneg u])
    rw [hws] at hfge
    have hpw : ‖u‖ * ‖u‖ ^ (r - 1) = ‖u‖ ^ r := by
      conv_rhs => rw [show r = 1 + (r - 1) by omega]
      rw [pow_add, pow_one]
    have hconst : ‖z‖ * ((r : ℝ) / 2 * (κ * ‖u‖) * ‖u‖ ^ (r - 1))
        = (r : ℝ) / 2 * κ * ‖Q.eval 0‖ := by
      calc ‖z‖ * ((r : ℝ) / 2 * (κ * ‖u‖) * ‖u‖ ^ (r - 1))
          = (r : ℝ) / 2 * κ * (‖u‖ * ‖u‖ ^ (r - 1) * ‖z‖) := by ring
        _ = (r : ℝ) / 2 * κ * (‖u‖ ^ r * ‖z‖) := by rw [hpw]
        _ = (r : ℝ) / 2 * κ * ‖Q.eval 0‖ := by rw [hnu]
    rw [hconst] at hfge
    calc ‖(ftDen Q r z - Mp).eval w‖ ≤ L * ‖w‖ := hginc
      _ ≤ L * ((1 + κ) * ‖u‖) := mul_le_mul_of_nonneg_left hwM hL0
      _ < (r : ℝ) / 2 * κ * ‖Q.eval 0‖ := hdom
      _ ≤ ‖Mp.eval w‖ := by
          rw [hMpeval w, show Q.eval 0 + z * w ^ r = z * w ^ r + Q.eval 0 by ring]
          exact hfge
  have hmem : u ∈ Metric.ball u (κ * ‖u‖) := Metric.mem_ball_self hR0
  have hfw : Mp.eval u = 0 := by rw [hMpeval]; linear_combination hroot
  obtain ⟨t, htb, ht0⟩ := exists_root_of_dominated hR0 (analyticOnNhd_eval Mp _)
    (analyticOnNhd_eval (ftDen Q r z - Mp) _) hdomsp hmem hfw
  refine ⟨t, ?_, ?_⟩
  · rw [← dist_eq_norm]
    exact Metric.mem_ball.mp htb
  · rw [eval_sub] at ht0
    linear_combination ht0

/-- **The upper cluster's members differ by an `r`-th root of unity.**  At the
origin the `z`-free relation is `Q(t)/Q(t_p) = (t/t_p)^r` — no factorization
enters, so it is `Q` itself rather than a cofactor — and `Q` is continuous and
nonzero at `0`, so that ratio is within `e` of `1` once both roots are close to
the origin.  `exists_root_of_unity_close` then makes the relation exact with
error `5e`.

The lower endpoint's `exists_cluster_ratio_close` needed `ρ ≥ 1` and a
factorization `Q = (X - x_1)^ρq`; this needs neither, which is the same
simplification `exists_ftDen_root_near_origin_model_root` shows in the
domination. -/
theorem exists_upper_ratio_close {Q : ℂ[X]} {r : ℕ} (hr : 1 ≤ r) {z t tp : ℂ}
    (hz : z ≠ 0) (ht : (ftDen Q r z).eval t = 0) (htp : (ftDen Q r z).eval tp = 0)
    (htp0 : tp ≠ 0) (hQtp : Q.eval tp ≠ 0) {e : ℝ} (he2 : e ≤ 1 / 2)
    (hclose : ‖Q.eval t / Q.eval tp - 1‖ ≤ e) :
    ∃ μ : ℂ, μ ^ r = 1 ∧ ‖t - μ * tp‖ ≤ 5 * e * ‖tp‖ := by
  rw [ftDen_eval] at ht htp
  have hQt : Q.eval t = -(z * t ^ r) := by linear_combination ht
  have hQp : Q.eval tp = -(z * tp ^ r) := by linear_combination htp
  have hratio : (t / tp) ^ r = Q.eval t / Q.eval tp := by
    rw [hQt, hQp, div_pow]
    field_simp
  obtain ⟨μ, hμ, hb⟩ :=
    exists_root_of_unity_close (ρ := r) hr (u := t / tp) he2 (by rw [hratio]; exact hclose)
  refine ⟨μ, hμ, ?_⟩
  have hfac : t - μ * tp = (t / tp - μ) * tp := by field_simp
  rw [hfac, norm_mul]
  exact mul_le_mul_of_nonneg_right hb (norm_nonneg _)

/-- **`exists_upper_ratio_close`'s `hclose`, from proximity to the origin.**  Two
roots of modulus at most `A` put `Q(t)/Q(t_p)` within `KA` of `1`, and the same
`ε` gives `Q(t_p) ≠ 0` and `KA ≤ 1/2`.

The denominator is bounded below by `Q`'s own continuity at `0` rather than by
compactness, so `K = 4L/‖Q(0)‖` is explicit, with `L` the Lipschitz sum on the
unit disk. -/
theorem exists_upper_ratio_bound {Q : ℂ[X]} (hQ0 : Q.eval 0 ≠ 0) :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ ε > 0, ∀ A : ℝ, 0 < A → A < ε → ∀ t tp : ℂ,
      ‖t‖ ≤ A → ‖tp‖ ≤ A →
      Q.eval tp ≠ 0 ∧ K * A ≤ 1 / 2 ∧ ‖Q.eval t / Q.eval tp - 1‖ ≤ K * A := by
  set L : ℝ := ∑ k ∈ Finset.range (Q.natDegree + 1), ‖Q.coeff k‖ * ((k : ℝ) * 1 ^ (k - 1))
    with hL
  have hL0 : 0 ≤ L := by
    rw [hL]
    exact Finset.sum_nonneg fun k _ =>
      mul_nonneg (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg k) (by positivity))
  have hN0 : (0 : ℝ) < ‖Q.eval 0‖ := norm_pos_iff.mpr hQ0
  set K : ℝ := 4 * L / ‖Q.eval 0‖ with hK
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  refine ⟨K, hK0, min (min 1 (‖Q.eval 0‖ / (2 * (L + 1)))) (1 / (2 * (K + 1))), ?_, ?_⟩
  · exact lt_min (lt_min one_pos (div_pos hN0 (by linarith only [hL0])))
      (div_pos one_pos (by linarith only [hK0]))
  intro A hA hAε t tp htn htpn
  have hA1 : A ≤ 1 :=
    le_of_lt (lt_of_lt_of_le (lt_of_lt_of_le hAε (min_le_left _ _)) (min_le_left _ _))
  have hLA : L * A ≤ ‖Q.eval 0‖ / 2 := by
    have h1 : A < ‖Q.eval 0‖ / (2 * (L + 1)) :=
      lt_of_lt_of_le (lt_of_lt_of_le hAε (min_le_left _ _)) (min_le_right _ _)
    have h2 : A * (2 * (L + 1)) < ‖Q.eval 0‖ :=
      (lt_div_iff₀ (by linarith only [hL0])).mp h1
    nlinarith only [h2, hA, hL0]
  have hKA : K * A ≤ 1 / 2 := by
    have h1 : A < 1 / (2 * (K + 1)) := lt_of_lt_of_le hAε (min_le_right _ _)
    have h2 : A * (2 * (K + 1)) < 1 := (lt_div_iff₀ (by linarith only [hK0])).mp h1
    nlinarith only [h2, hA, hK0]
  have ht1 : ‖t‖ ≤ (1 : ℝ) := le_trans htn hA1
  have htp1 : ‖tp‖ ≤ (1 : ℝ) := le_trans htpn hA1
  have h01 : ‖(0 : ℂ)‖ ≤ (1 : ℝ) := by simp
  -- the denominator stays away from zero
  have hlow : ‖Q.eval 0‖ / 2 ≤ ‖Q.eval tp‖ := by
    have hq := norm_eval_sub_eval_le_of_norm_le (q := Q) (M := (1 : ℝ)) htp1 h01
    rw [← hL, sub_zero] at hq
    have hsub : ‖Q.eval 0‖ - ‖Q.eval tp‖ ≤ ‖Q.eval 0 - Q.eval tp‖ := norm_sub_norm_le _ _
    rw [norm_sub_rev] at hsub
    have hbd : ‖Q.eval tp - Q.eval 0‖ ≤ L * A := le_trans hq (by nlinarith only [htpn, hL0])
    linarith only [hsub, hbd, hLA]
  have hQtp : Q.eval tp ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hlow
    linarith only [hlow, hN0]
  refine ⟨hQtp, hKA, ?_⟩
  have hdiff : ‖Q.eval t - Q.eval tp‖ ≤ L * (2 * A) := by
    refine le_trans (norm_eval_sub_eval_le_of_norm_le (q := Q) (M := (1 : ℝ)) ht1 htp1) ?_
    rw [← hL]
    refine mul_le_mul_of_nonneg_left ?_ hL0
    calc ‖t - tp‖ ≤ ‖t‖ + ‖tp‖ := norm_sub_le _ _
      _ ≤ 2 * A := by linarith only [htn, htpn]
  have hsplit : Q.eval t / Q.eval tp - 1 = (Q.eval t - Q.eval tp) / Q.eval tp := by
    field_simp
  rw [hsplit, norm_div]
  rw [div_le_iff₀ (by linarith only [hlow, hN0])]
  have hKexp : K * A * ‖Q.eval tp‖ ≥ K * A * (‖Q.eval 0‖ / 2) := by
    exact mul_le_mul_of_nonneg_left hlow (by positivity)
  have hval : K * A * (‖Q.eval 0‖ / 2) = 2 * L * A := by
    rw [hK]
    field
  linarith only [hdiff, hKexp, hval]

/-- **The binomial remainder, to second order.**  `(1+u)^r = 1 + ru + O(‖u‖²)`
on `‖u‖ ≤ 1`, with the constant explicit.

This is what the upper endpoint needs and the lower endpoint did not.  There the
ratio was compared to `1` and `exists_root_of_unity_close` turned it into an
exact root of unity, discarding everything past the leading term; here the
discarded term *is* the coefficient, because `‖ζ_j‖ - 1` is of order `τ` rather
than of order `δ`, so the ratio has to be expanded one order further.

The recursion is `E_{r+1} = (1+u)E_r + ru²`, which is exact — nothing is
estimated until the norms are taken. -/
theorem norm_one_add_pow_sub_linear_le {u : ℂ} (hu : ‖u‖ ≤ 1) (r : ℕ) :
    ‖(1 + u) ^ r - (1 + (r : ℂ) * u)‖ ≤ (2 ^ r * r : ℝ) * ‖u‖ ^ 2 := by
  induction r with
  | zero => simp
  | succ r ih =>
    have hid : (1 + u) ^ (r + 1) - (1 + ((r : ℕ) + 1 : ℂ) * u)
        = (1 + u) * ((1 + u) ^ r - (1 + (r : ℂ) * u)) + (r : ℂ) * u ^ 2 := by
      ring
    have hone : ‖1 + u‖ ≤ 2 := by
      calc ‖1 + u‖ ≤ ‖(1 : ℂ)‖ + ‖u‖ := norm_add_le _ _
        _ ≤ 2 := by simp; linarith only [hu]
    have hrn : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg r
    have hpow : (0 : ℝ) ≤ (2 : ℝ) ^ r := by positivity
    have hu2 : (0 : ℝ) ≤ ‖u‖ ^ 2 := sq_nonneg _
    have hstep : ‖(1 + u) ^ (r + 1) - (1 + ((r : ℕ) + 1 : ℂ) * u)‖
        ≤ 2 * ((2 ^ r * r : ℝ) * ‖u‖ ^ 2) + (r : ℝ) * ‖u‖ ^ 2 := by
      rw [hid]
      refine le_trans (norm_add_le _ _) (add_le_add ?_ ?_)
      · rw [norm_mul]
        exact le_trans (mul_le_mul hone ih (norm_nonneg _) (by norm_num))
          (le_of_eq rfl)
      · rw [norm_mul, norm_pow, Complex.norm_natCast]
    have hcast : ((r : ℕ) + 1 : ℂ) = ((r + 1 : ℕ) : ℂ) := by push_cast; ring
    rw [hcast] at hstep
    refine le_trans hstep ?_
    have hle : (r : ℝ) ≤ 2 ^ (r + 1) := by
      calc (r : ℝ) ≤ 2 ^ r := by
            exact_mod_cast Nat.le_of_lt (Nat.lt_two_pow_self)
        _ ≤ 2 ^ (r + 1) := by
            have : (2 : ℝ) ^ r ≤ 2 ^ r * 2 := by nlinarith only [hpow]
            simp [pow_succ]
    push_cast
    have hexp : (2 : ℝ) ^ (r + 1) = 2 * 2 ^ r := by rw [pow_succ]; ring
    have hkey : (r : ℝ) * ‖u‖ ^ 2 ≤ 2 * 2 ^ r * ‖u‖ ^ 2 := by
      refine mul_le_mul_of_nonneg_right ?_ hu2
      rw [← hexp]
      exact hle
    rw [hexp]
    nlinarith only [hkey]

/-- **`Q(t) = Q(0) + Q'(0)t + O(‖t‖²)` on a disk**, with the constant explicit.

Proved by factoring rather than by splitting a coefficient sum: `Q - Q(0)` has a
root at `0`, so `Q(t) - Q(0) = tR(t)` for a polynomial `R` with `R(0) = Q'(0)`,
and the second-order statement is then the *first*-order one applied to `R` —
`norm_eval_sub_eval_le_of_norm_le`, already here.  Nothing is re-derived and no
index range has to be cut at `2`.

This is what turns the upper endpoint's `z`-free relation into a coefficient:
`Q(t)/Q(0) = 1 - St + O(t²)` with `S = -Q'(0)/Q(0)`, which for `Q = c∏(a_k-t)`
is `∑ 1/a_k`. -/
theorem exists_second_order_bound (Q : ℂ[X]) {M : ℝ} (hM : 0 ≤ M) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ t : ℂ, ‖t‖ ≤ M →
      ‖Q.eval t - (Q.eval 0 + (derivative Q).eval 0 * t)‖ ≤ L * ‖t‖ ^ 2 := by
  classical
  have hdvd : X ∣ (Q - C (Q.eval 0)) := by
    rw [X_dvd_iff]
    simp [coeff_zero_eq_eval_zero]
  obtain ⟨R, hR⟩ := hdvd
  have heval : ∀ t : ℂ, Q.eval t - Q.eval 0 = t * R.eval t := by
    intro t
    have h := congrArg (Polynomial.eval t) hR
    simp only [eval_sub, eval_C, eval_mul, eval_X] at h
    exact h
  have hR0 : R.eval 0 = (derivative Q).eval 0 := by
    have h := congrArg (fun p : ℂ[X] => p.coeff 1) hR
    simp only [coeff_sub, coeff_C, coeff_X_mul] at h
    have hd : (derivative Q).eval 0 = Q.coeff 1 := by
      rw [← coeff_zero_eq_eval_zero, Polynomial.coeff_derivative]
      simp
    rw [hd]
    simpa [coeff_zero_eq_eval_zero] using h.symm
  refine ⟨∑ k ∈ Finset.range (R.natDegree + 1), ‖R.coeff k‖ * ((k : ℝ) * M ^ (k - 1)),
    ?_, ?_⟩
  · exact Finset.sum_nonneg fun k _ => mul_nonneg (norm_nonneg _)
      (mul_nonneg (Nat.cast_nonneg k) (pow_nonneg hM _))
  · intro t ht
    have h0 : ‖(0 : ℂ)‖ ≤ M := by simpa using hM
    have hsplit : Q.eval t - (Q.eval 0 + (derivative Q).eval 0 * t)
        = t * (R.eval t - R.eval 0) := by
      rw [hR0]
      have := heval t
      linear_combination this
    rw [hsplit, norm_mul]
    have hq := norm_eval_sub_eval_le_of_norm_le (q := R) (M := M) ht h0
    rw [sub_zero] at hq
    calc ‖t‖ * ‖R.eval t - R.eval 0‖
        ≤ ‖t‖ * ((∑ k ∈ Finset.range (R.natDegree + 1),
            ‖R.coeff k‖ * ((k : ℝ) * M ^ (k - 1))) * ‖t‖) :=
          mul_le_mul_of_nonneg_left hq (norm_nonneg t)
      _ = (∑ k ∈ Finset.range (R.natDegree + 1),
            ‖R.coeff k‖ * ((k : ℝ) * M ^ (k - 1))) * ‖t‖ ^ 2 := by ring

/-- **The `z`-free ratio to second order.**  Near the origin

`Q(t)/Q(t_p) = 1 + β(t - t_p) + O(A²)`,  `β = Q'(0)/Q(0)`,

for any two points of modulus at most `A`.  For `Q = c∏(a_k - t)` the constant is
`β = -∑1/a_k`, which is the `S` the upper endpoint's τ-rate carries — and it is
exactly the factor that cancels against that rate to leave `hexp₁`'s coefficient
free of the pencil.

`exists_upper_ratio_bound` gives the same ratio to *first* order, which is all
`exists_upper_ratio_close` needs to produce the `r`-th root of unity.  This one
is what the coefficient needs, since at the upper endpoint the discarded term is
the coefficient rather than an error. -/
theorem exists_ratio_second_order_bound (Q : ℂ[X]) (hQ0 : Q.eval 0 ≠ 0) :
    ∃ L : ℝ, 0 ≤ L ∧ ∃ ε > 0, ∀ A : ℝ, 0 < A → A ≤ ε → ∀ t tp : ℂ,
      ‖t‖ ≤ A → ‖tp‖ ≤ A →
      Q.eval tp ≠ 0 ∧
        ‖Q.eval t / Q.eval tp
            - (1 + (derivative Q).eval 0 / Q.eval 0 * (t - tp))‖ ≤ L * A ^ 2 := by
  classical
  obtain ⟨L₂, hL₂, hsec⟩ := exists_second_order_bound Q (M := (1 : ℝ)) zero_le_one
  set N : ℝ := ‖Q.eval 0‖ with hN
  have hN0 : 0 < N := by rw [hN]; exact norm_pos_iff.mpr hQ0
  set L₁ : ℝ := ∑ k ∈ Finset.range (Q.natDegree + 1), ‖Q.coeff k‖ * ((k : ℝ) * 1 ^ (k - 1))
    with hL₁
  have hL₁0 : 0 ≤ L₁ := by
    rw [hL₁]
    exact Finset.sum_nonneg fun k _ =>
      mul_nonneg (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg k) (by positivity))
  set β : ℂ := (derivative Q).eval 0 / Q.eval 0 with hβ
  set L : ℝ := 2 / N * (2 * L₂ + ‖β‖ * 2 * (N * ‖β‖ + L₂)) with hL
  have hL0 : 0 ≤ L := by
    rw [hL]
    have h1 : 0 ≤ 2 * L₂ + ‖β‖ * 2 * (N * ‖β‖ + L₂) :=
      by positivity
    positivity
  refine ⟨L, hL0, min 1 (N / (2 * (L₁ + 1))), lt_min one_pos (by positivity), ?_⟩
  intro A hA hAε t tp htn htpn
  have hA1 : A ≤ 1 := le_trans hAε (min_le_left _ _)
  have hL₁A : L₁ * A ≤ N / 2 := by
    have h1 : A ≤ N / (2 * (L₁ + 1)) := le_trans hAε (min_le_right _ _)
    have h2 : A * (2 * (L₁ + 1)) ≤ N := by
      rw [← le_div_iff₀ (by linarith only [hL₁0])]
      exact h1
    nlinarith only [h2, hA, hL₁0]
  have ht1 : ‖t‖ ≤ (1 : ℝ) := le_trans htn hA1
  have htp1 : ‖tp‖ ≤ (1 : ℝ) := le_trans htpn hA1
  -- the denominator stays away from zero
  have hlow : N / 2 ≤ ‖Q.eval tp‖ := by
    have h01 : ‖(0 : ℂ)‖ ≤ (1 : ℝ) := by norm_num
    have hq := norm_eval_sub_eval_le_of_norm_le (q := Q) (M := (1 : ℝ)) htp1 h01
    rw [← hL₁, sub_zero] at hq
    have hsub : ‖Q.eval 0‖ - ‖Q.eval tp‖ ≤ ‖Q.eval 0 - Q.eval tp‖ := norm_sub_norm_le _ _
    rw [norm_sub_rev, ← hN] at hsub
    have hbd : ‖Q.eval tp - Q.eval 0‖ ≤ L₁ * A :=
      le_trans hq (mul_le_mul_of_nonneg_left htpn hL₁0)
    linarith only [hsub, hbd, hL₁A]
  have hQtp : Q.eval tp ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hlow
    linarith only [hlow, hN0]
  refine ⟨hQtp, ?_⟩
  -- the exact numerator identity
  set Et : ℂ := Q.eval t - (Q.eval 0 + (derivative Q).eval 0 * t) with hEt
  set Ep : ℂ := Q.eval tp - (Q.eval 0 + (derivative Q).eval 0 * tp) with hEp
  have hEtb : ‖Et‖ ≤ L₂ * A ^ 2 := by
    refine le_trans (hsec t ht1) ?_
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg t) htn 2) hL₂
  have hEpb : ‖Ep‖ ≤ L₂ * A ^ 2 := by
    refine le_trans (hsec tp htp1) ?_
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg tp) htpn 2) hL₂
  have hnum : Q.eval t - Q.eval tp - β * (t - tp) * Q.eval tp
      = Et - Ep - β * (t - tp) * (Q.eval 0 * β * tp + Ep) := by
    rw [hEt, hEp, hβ]
    field
  have hsplit : Q.eval t / Q.eval tp - (1 + β * (t - tp))
      = (Q.eval t - Q.eval tp - β * (t - tp) * Q.eval tp) / Q.eval tp := by
    field
  rw [hsplit, hnum, norm_div]
  -- bound the numerator
  have hdiff : ‖t - tp‖ ≤ 2 * A :=
    le_trans (norm_sub_le _ _) (by linarith only [htn, htpn])
  have htpb : ‖Q.eval 0 * β * tp + Ep‖ ≤ N * ‖β‖ * A + L₂ * A ^ 2 := by
    refine le_trans (norm_add_le _ _) (add_le_add ?_ hEpb)
    rw [norm_mul, norm_mul, ← hN]
    exact mul_le_mul_of_nonneg_left htpn (by positivity)
  have hA0 : (0 : ℝ) ≤ A := hA.le
  have hnb : ‖Et - Ep - β * (t - tp) * (Q.eval 0 * β * tp + Ep)‖
      ≤ 2 * L₂ * A ^ 2 + ‖β‖ * (2 * A) * (N * ‖β‖ * A + L₂ * A ^ 2) := by
    refine le_trans (norm_sub_le _ _) (add_le_add ?_ ?_)
    · exact le_trans (norm_sub_le _ _) (by linarith only [hEtb, hEpb])
    · rw [norm_mul, norm_mul]
      refine mul_le_mul (mul_le_mul_of_nonneg_left hdiff (norm_nonneg β)) htpb
        (norm_nonneg _) (by positivity)
  rw [div_le_iff₀ (by linarith only [hlow, hN0])]
  have hLA : L * A ^ 2 * (N / 2) = (2 * L₂ + ‖β‖ * 2 * (N * ‖β‖ + L₂)) * A ^ 2 := by
    rw [hL]
    field_simp
  have hmono : L * A ^ 2 * (N / 2) ≤ L * A ^ 2 * ‖Q.eval tp‖ :=
    mul_le_mul_of_nonneg_left hlow (by positivity)
  refine le_trans hnb (le_trans ?_ hmono)
  rw [hLA]
  have hcube : ‖β‖ * L₂ * A ^ 3 ≤ ‖β‖ * L₂ * A ^ 2 := by
    have h := mul_nonneg (mul_nonneg (norm_nonneg β) hL₂)
      (mul_nonneg (sq_nonneg A) (by linarith only [hA1] : (0 : ℝ) ≤ 1 - A))
    nlinarith only [h]
  nlinarith only [hcube]

/-- **The second-order inversion.**  From `(μ(1+u))^r = 1 + w + O(A²)` with
`μ^r = 1` and `‖u‖ = O(A)`, conclude `ru = w + O(A²)`.

This is the step that turns the `z`-free ratio into the member's displacement.
The `μ^r = 1` is what makes the root of unity drop out entirely — the equation
sees `(1+u)^r` — and `norm_one_add_pow_sub_linear_le` then trades `(1+u)^r` for
`1 + ru` at the cost of `O(‖u‖²)`, which is `O(A²)` exactly because the first-order
step has already put `‖u‖` at `O(A)`.  Nothing here is asymptotic: both constants
are explicit and the inequality is pointwise. -/
theorem norm_nat_mul_sub_le_of_pow_eq {r : ℕ} {μ u w : ℂ} {A C K : ℝ}
    (hμ : μ ^ r = 1) (hK : 0 ≤ K) (hA : 0 ≤ A) (hu1 : ‖u‖ ≤ 1) (hu : ‖u‖ ≤ K * A)
    (hratio : ‖(μ * (1 + u)) ^ r - (1 + w)‖ ≤ C * A ^ 2) :
    ‖(r : ℂ) * u - w‖ ≤ (C + 2 ^ r * r * K ^ 2) * A ^ 2 := by
  have hpow : (μ * (1 + u)) ^ r = (1 + u) ^ r := by
    rw [mul_pow, hμ, one_mul]
  rw [hpow] at hratio
  have hbin := norm_one_add_pow_sub_linear_le hu1 r
  have hbin' : ‖(1 + u) ^ r - (1 + (r : ℂ) * u)‖ ≤ (2 ^ r * r : ℝ) * (K * A) ^ 2 := by
    refine le_trans hbin ?_
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact pow_le_pow_left₀ (norm_nonneg u) hu 2
  have hsplit : (r : ℂ) * u - w = ((1 + (r : ℂ) * u) - (1 + u) ^ r)
      + ((1 + u) ^ r - (1 + w)) := by ring
  rw [hsplit]
  refine le_trans (norm_add_le _ _) ?_
  rw [norm_sub_rev ((1 : ℂ) + (r : ℂ) * u)]
  have hfin : (2 ^ r * r : ℝ) * (K * A) ^ 2 + C * A ^ 2
      = (C + 2 ^ r * r * K ^ 2) * A ^ 2 := by ring
  rw [← hfin]
  exact add_le_add hbin' hratio

/-- **The displacement, solved.**  With `t = μt_p(1+u)` the `z`-free relation
reads `ru = β((μ-1)t_p + μt_pu) + O(A²)`, and the `μt_pu` term is itself `O(A²)`
because `‖t_p‖ = O(A)` and `‖u‖ = O(A)` — so

`u = (β/r)(μ-1)t_p + O(A²)`.

The `β` here is `Q'(0)/Q(0) = -S`, and `t_p` is `O(δ)` by the τ-rate, so this is
where the member's linear coefficient in `δ` is finally an explicit number. -/
theorem norm_sub_beta_mul_le {r : ℕ} (hr : 1 ≤ r) {μ u tp β : ℂ} {A C K : ℝ}
    (hK : 0 ≤ K) (hA : 0 ≤ A) (hμ1 : ‖μ‖ = 1) (htp : ‖tp‖ ≤ A) (hu : ‖u‖ ≤ K * A)
    (h : ‖(r : ℂ) * u - β * ((μ - 1) * tp + μ * tp * u)‖ ≤ C * A ^ 2) :
    ‖u - β / r * ((μ - 1) * tp)‖ ≤ (C + ‖β‖ * K) / r * A ^ 2 := by
  have hrR : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  have hrC : ((r : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hrn : ‖((r : ℕ) : ℂ)‖ = (r : ℝ) := by simp
  have hextra : ‖β * (μ * tp * u)‖ ≤ ‖β‖ * K * A ^ 2 := by
    rw [norm_mul, norm_mul, norm_mul, hμ1, one_mul]
    have hb : ‖tp‖ * ‖u‖ ≤ A * (K * A) :=
      mul_le_mul htp hu (norm_nonneg u) hA
    calc ‖β‖ * (‖tp‖ * ‖u‖) ≤ ‖β‖ * (A * (K * A)) :=
          mul_le_mul_of_nonneg_left hb (norm_nonneg β)
      _ = ‖β‖ * K * A ^ 2 := by ring
  have hstep : ‖(r : ℂ) * u - β * ((μ - 1) * tp)‖ ≤ (C + ‖β‖ * K) * A ^ 2 := by
    have hsplit : (r : ℂ) * u - β * ((μ - 1) * tp)
        = ((r : ℂ) * u - β * ((μ - 1) * tp + μ * tp * u)) + β * (μ * tp * u) := by
      ring
    rw [hsplit]
    refine le_trans (norm_add_le _ _) ?_
    have hsum : C * A ^ 2 + ‖β‖ * K * A ^ 2 = (C + ‖β‖ * K) * A ^ 2 := by ring
    rw [← hsum]
    exact add_le_add h hextra
  have hfac : u - β / r * ((μ - 1) * tp)
      = ((r : ℂ))⁻¹ * ((r : ℂ) * u - β * ((μ - 1) * tp)) := by
    field_simp
  rw [hfac, norm_mul, norm_inv, hrn]
  rw [inv_mul_eq_div, div_le_iff₀ hrR]
  calc ‖(r : ℂ) * u - β * ((μ - 1) * tp)‖ ≤ (C + ‖β‖ * K) * A ^ 2 := hstep
    _ = (C + ‖β‖ * K) / r * A ^ 2 * r := by field_simp

/-- **Two linear expansions multiply.**  `x = 1 + aδ + O(δ²)` and
`y = 1 + bδ + O(δ²)` give `xy = 1 + (a+b)δ + O(δ²)`, with the constant explicit.

The upper endpoint needs exactly this and the lower endpoint did not: there the
normalization was by a *real* `τ` and `norm_div_sub_one_add_mul_le` divided, while
here the member is `μ(t_p/τ)(1+u)` — a unimodular rotation times a linear factor —
and the two linear parts have to be added rather than divided.  The `abδ²` is the
only genuinely quadratic term; the rest is the two remainders carried through. -/
theorem norm_mul_linear_expansion_le {x y a b : ℂ} {δ Cx Cy : ℝ}
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hCx : 0 ≤ Cx) (hCy : 0 ≤ Cy)
    (hx : ‖x - (1 + a * (δ : ℂ))‖ ≤ Cx * δ ^ 2)
    (hy : ‖y - (1 + b * (δ : ℂ))‖ ≤ Cy * δ ^ 2) :
    ‖x * y - (1 + (a + b) * (δ : ℂ))‖
      ≤ (Cx * (1 + ‖b‖) + Cy * (1 + ‖a‖) + Cx * Cy + ‖a‖ * ‖b‖) * δ ^ 2 := by
  have hδn : ‖((δ : ℝ) : ℂ)‖ = δ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hδ]
  set X : ℂ := x - (1 + a * (δ : ℂ)) with hX
  set Y : ℂ := y - (1 + b * (δ : ℂ)) with hY
  have hid : x * y - (1 + (a + b) * (δ : ℂ))
      = a * b * (δ : ℂ) ^ 2 + (1 + a * (δ : ℂ)) * Y + X * (1 + b * (δ : ℂ)) + X * Y := by
    rw [hX, hY]; ring
  rw [hid]
  have h1 : ‖a * b * (δ : ℂ) ^ 2‖ = ‖a‖ * ‖b‖ * δ ^ 2 := by
    rw [norm_mul, norm_mul, norm_pow, hδn]
  have hone : ∀ w : ℂ, ‖1 + w * (δ : ℂ)‖ ≤ 1 + ‖w‖ := by
    intro w
    refine le_trans (norm_add_le _ _) ?_
    rw [norm_one, norm_mul, hδn]
    have : ‖w‖ * δ ≤ ‖w‖ * 1 := mul_le_mul_of_nonneg_left hδ1 (norm_nonneg w)
    linarith only [this]
  have h2 : ‖(1 + a * (δ : ℂ)) * Y‖ ≤ (1 + ‖a‖) * (Cy * δ ^ 2) := by
    rw [norm_mul]
    exact mul_le_mul (hone a) hy (norm_nonneg _) (by linarith only [norm_nonneg a])
  have h3 : ‖X * (1 + b * (δ : ℂ))‖ ≤ (Cx * δ ^ 2) * (1 + ‖b‖) := by
    rw [norm_mul]
    exact mul_le_mul hx (hone b) (norm_nonneg _) (by positivity)
  have h4 : ‖X * Y‖ ≤ (Cx * δ ^ 2) * (Cy * δ ^ 2) := by
    rw [norm_mul]
    exact mul_le_mul hx hy (norm_nonneg _) (by positivity)
  have hq : (Cx * δ ^ 2) * (Cy * δ ^ 2) ≤ Cx * Cy * δ ^ 2 := by
    have hle : δ ^ 2 ≤ 1 := by nlinarith only [hδ, hδ1]
    have hprod : 0 ≤ Cx * Cy * δ ^ 2 * (1 - δ ^ 2) :=
      mul_nonneg (mul_nonneg (mul_nonneg hCx hCy) (sq_nonneg δ))
        (by linarith only [hle])
    nlinarith only [hprod]
  refine le_trans (norm_add_le _ _) ?_
  refine le_trans (add_le_add (le_trans (norm_add_le _ _)
    (add_le_add (le_trans (norm_add_le _ _) (add_le_add (le_of_eq h1) h2)) h3)) h4) ?_
  nlinarith only [hq]

/-- **The upper member expansion, assembled.**  The four links composed: with the
displacement solved (`norm_sub_beta_mul_le`), the principal point expanded
(`t_p = Lν₁δ + O(δ²)`, the τ-rate times the rotation) and the unimodular part
expanded (`ν₀ = ν₁(1 - iδ) + O(δ²)`), the member is

`μν₀(1+u) = μν₁(1 + cδ) + O(δ²)`,  `c = -i + (βL/r)(μ-1)ν₁`.

`μν₁` is δ-free and unimodular, and `(μν₁)^r = μ^rν₁^r = -1` at `ν₁ = e^{iπ/r}`,
so it is a cluster direction — which is what
`abs_norm_sub_one_add_re_mul_le_of_unimodular` needs as its `ν`.

**The rotation must be split off, not absorbed.**  `ν₁` is `δ`-free but
`t_p/τ = e^{i(π/r - δ)}` is not, and the two differ at first order.  Absorbing the
rotation into the unimodular limit hands the transfer lemma a *moving* `ν` and
loses the `-i`, so the coefficient comes out short by exactly that — a plausible
shortcut that yields a wrong number rather than a failed proof, which is the
class that gets shipped.  The `-i` here is the whole content of that split, and
it is invisible in the conclusion because it is purely imaginary and only
`Re c` survives to `hexp₁`. -/
theorem norm_upper_member_expansion_le {r : ℕ} (hr : 1 ≤ r)
    {μ ν₀ ν₁ tp u β : ℂ} {δ L Cu Ct Cν : ℝ}
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hμ1 : ‖μ‖ = 1) (hν1 : ‖ν₁‖ = 1)
    (hCu : 0 ≤ Cu) (hCt : 0 ≤ Ct) (hCν : 0 ≤ Cν)
    (hu : ‖u - β / r * ((μ - 1) * tp)‖ ≤ Cu * δ ^ 2)
    (htp : ‖tp - (L : ℂ) * ν₁ * (δ : ℂ)‖ ≤ Ct * δ ^ 2)
    (hν : ‖ν₀ - ν₁ * (1 + (-Complex.I) * (δ : ℂ))‖ ≤ Cν * δ ^ 2) :
    ∃ C' : ℝ, 0 ≤ C' ∧
      ‖μ * ν₀ * (1 + u)
          - μ * ν₁ * (1 + (-Complex.I + β * (L : ℂ) / r * ((μ - 1) * ν₁)) * (δ : ℂ))‖
        ≤ C' * δ ^ 2 := by
  have hν10 : ν₁ ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hν1; norm_num at hν1
  set cA : ℂ := β * (L : ℂ) / r * ((μ - 1) * ν₁) with ha
  -- the displacement against the principal point's own expansion
  have hstep : ‖u - cA * (δ : ℂ)‖ ≤ (Cu + ‖β / r * (μ - 1)‖ * Ct) * δ ^ 2 := by
    have hid : u - cA * (δ : ℂ)
        = (u - β / r * ((μ - 1) * tp))
          + β / r * (μ - 1) * (tp - (L : ℂ) * ν₁ * (δ : ℂ)) := by
      rw [ha]; ring
    rw [hid]
    refine le_trans (norm_add_le _ _) ?_
    have h2 : ‖β / r * (μ - 1) * (tp - (L : ℂ) * ν₁ * (δ : ℂ))‖
        ≤ ‖β / r * (μ - 1)‖ * (Ct * δ ^ 2) := by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left htp (norm_nonneg _)
    have hsum : Cu * δ ^ 2 + ‖β / r * (μ - 1)‖ * (Ct * δ ^ 2)
        = (Cu + ‖β / r * (μ - 1)‖ * Ct) * δ ^ 2 := by ring
    rw [← hsum]
    exact add_le_add hu h2
  -- the rotation, normalized
  have hrot : ‖ν₀ / ν₁ - (1 + (-Complex.I) * (δ : ℂ))‖ ≤ Cν * δ ^ 2 := by
    have hid : ν₀ / ν₁ - (1 + (-Complex.I) * (δ : ℂ))
        = ν₁⁻¹ * (ν₀ - ν₁ * (1 + (-Complex.I) * (δ : ℂ))) := by
      field_simp
    rw [hid, norm_mul, norm_inv, hν1, inv_one, one_mul]
    exact hν
  have hu' : ‖(1 + u) - (1 + cA * (δ : ℂ))‖ ≤ (Cu + ‖β / r * (μ - 1)‖ * Ct) * δ ^ 2 := by
    have hid : (1 + u) - (1 + cA * (δ : ℂ)) = u - cA * (δ : ℂ) := by ring
    rw [hid]; exact hstep
  obtain hprod := norm_mul_linear_expansion_le (x := ν₀ / ν₁) (y := 1 + u)
    (a := -Complex.I) (b := cA) hδ hδ1 hCν
    (by positivity) hrot hu'
  refine ⟨Cν * (1 + ‖cA‖) + (Cu + ‖β / r * (μ - 1)‖ * Ct) * (1 + ‖(-Complex.I : ℂ)‖)
    + Cν * (Cu + ‖β / r * (μ - 1)‖ * Ct) + ‖(-Complex.I : ℂ)‖ * ‖cA‖, by positivity, ?_⟩
  have hid : μ * ν₀ * (1 + u)
      - μ * ν₁ * (1 + (-Complex.I + cA) * (δ : ℂ))
      = μ * ν₁ * ((ν₀ / ν₁) * (1 + u) - (1 + (-Complex.I + cA) * (δ : ℂ))) := by
    field_simp
  rw [hid, norm_mul, norm_mul, hμ1, hν1, one_mul, one_mul]
  exact hprod

/-! ### `Forgacs2017RationalDenominator` Lemma 6 — the endpoint limits of `z`

Their Lemma 6 states the two limits of the spectral parameter along the branch.
What is assembled here is the passage from the branch radius to the parameter:
given the limit of `τ` at an endpoint of the viewing arc, the limit of
`z(θ; l) = ftBranchZ` follows, in the two conventions `eq:ab-def` distinguishes —
a real limit where the branch point stays away from the origin, and divergence
where it runs into it.  The lower endpoint is then closed outright against
`FTBranchEndpoint`'s convergence of `τ`.
-/

private theorem tendsto_re_of_tendsto_ofReal {α : Type*} {F : Filter α} {f : α → ℝ} {w : ℂ}
    (h : Filter.Tendsto (fun x => ((f x : ℝ) : ℂ)) F (nhds w)) :
    Filter.Tendsto f F (nhds w.re) := by
  simpa [Function.comp_def] using (Complex.continuous_re.tendsto w).comp h

private theorem re_ftBranchLimit_ofReal {n : ℕ} {a : Fin n → ℝ} {c : ℝ} {r : ℕ} (t : ℝ) :
    (-(ftRootPoly c a).eval ((t : ℝ) : ℂ) / ((t : ℝ) : ℂ) ^ r).re
      = -(ftRootPolyReal c a).eval t / t ^ r := by
  have h : (ftRootPoly c a).eval ((t : ℝ) : ℂ) = (((ftRootPolyReal c a).eval t : ℝ) : ℂ) := by
    rw [eval_ftRootPoly, eval_ftRootPolyReal]
    push_cast [Complex.ofReal_prod]
    ring
  rw [h, ← Complex.ofReal_pow, ← Complex.ofReal_neg, ← Complex.ofReal_div, Complex.ofReal_re]

/-- **`Forgacs2017RationalDenominator` Lemma 6, the transfer.**  Wherever the
branch radius `τ` converges to a positive limit `L`, the spectral parameter
`z(θ; l)` converges to the value of `-P(t)/t^r` at the limiting branch point
`L e^{-ip}`.  The limit is real because `z` is; `ftBranchZ` is the real form of
the branch value and `ftBranch_ftArcPoint_eq_ftBranchZ` is the identification. -/
theorem tendsto_ftBranchZ_of_tendsto_ftTau {n r l : ℕ} {a : Fin n → ℝ} {c : ℝ}
    (ha : ∀ k, 0 < a k) {p L : ℝ} {S : Set ℝ} (hL : 0 < L)
    (hmem : ∀ᶠ θ in nhdsWithin p S, θ ∈ Set.Ioo 0 Real.pi ∧ FTBranchAt a r l θ)
    (hτ : Filter.Tendsto (ftTau a r l) (nhdsWithin p S) (nhds L)) :
    Filter.Tendsto (ftBranchZ a c r l) (nhdsWithin p S)
      (nhds (-(ftRootPoly c a).eval (ftArcPoint L p) / ftArcPoint L p ^ r).re) := by
  have hγ : Filter.Tendsto (fun θ : ℝ => ftArcPoint (ftTau a r l θ) θ)
      (nhdsWithin p S) (nhds (ftArcPoint L p)) := by
    simpa [ftArcPoint] using tendsto_branchPoint_of_tendsto_tau (τ := ftTau a r l) hτ
  have hne : ftArcPoint L p ≠ 0 := by
    rw [ftArcPoint]
    exact mul_ne_zero (Complex.ofReal_ne_zero.2 hL.ne') (Complex.exp_ne_zero _)
  have hz := tendsto_ftZ_of_tendsto_branchPoint (P := ftRootPoly c a) (r := r) hne hγ
  refine tendsto_re_of_tendsto_ofReal (Filter.Tendsto.congr' ?_ hz)
  filter_upwards [hmem] with θ hθ
  rw [eval_ftRootPoly]
  exact ftBranch_ftArcPoint_eq_ftBranchZ c ha hθ.1 hθ.2

/-- **Lemma 6 at the lower endpoint.**  At `θ → 0` the limiting branch point is
the positive real `L`, so the limit of `z` is `-P(L)/L^r` outright. -/
theorem tendsto_ftBranchZ_lower {n r l : ℕ} {a : Fin n → ℝ} {c : ℝ}
    (ha : ∀ k, 0 < a k) {L : ℝ} {S : Set ℝ} (hL : 0 < L)
    (hmem : ∀ᶠ θ in nhdsWithin (0 : ℝ) S, θ ∈ Set.Ioo 0 Real.pi ∧ FTBranchAt a r l θ)
    (hτ : Filter.Tendsto (ftTau a r l) (nhdsWithin (0 : ℝ) S) (nhds L)) :
    Filter.Tendsto (ftBranchZ a c r l) (nhdsWithin (0 : ℝ) S)
      (nhds (-(ftRootPolyReal c a).eval L / L ^ r)) := by
  have h := tendsto_ftBranchZ_of_tendsto_ftTau (c := c) ha hL hmem hτ
  have harc : ftArcPoint L (0 : ℝ) = ((L : ℝ) : ℂ) := by simp [ftArcPoint]
  rwa [harc, re_ftBranchLimit_ofReal] at h

/-- **Lemma 6 at the finite upper endpoint**, which `eq:ab-def` reaches only at
`r = 1`: there the arc ends at `θ = π`, the limiting branch point is the negative
real `-L`, and `b` is `-P(-L)/(-L)^r`. -/
theorem tendsto_ftBranchZ_upper_pi {n r l : ℕ} {a : Fin n → ℝ} {c : ℝ}
    (ha : ∀ k, 0 < a k) {L : ℝ} {S : Set ℝ} (hL : 0 < L)
    (hmem : ∀ᶠ θ in nhdsWithin Real.pi S, θ ∈ Set.Ioo 0 Real.pi ∧ FTBranchAt a r l θ)
    (hτ : Filter.Tendsto (ftTau a r l) (nhdsWithin Real.pi S) (nhds L)) :
    Filter.Tendsto (ftBranchZ a c r l) (nhdsWithin Real.pi S)
      (nhds (-(ftRootPolyReal c a).eval (-L) / (-L) ^ r)) := by
  have h := tendsto_ftBranchZ_of_tendsto_ftTau (c := c) ha hL hmem hτ
  have harc : ftArcPoint L Real.pi = ((-L : ℝ) : ℂ) := by
    have hexp : Complex.exp (-((Real.pi : ℝ) : ℂ) * Complex.I) = -1 := by
      rw [neg_mul, Complex.exp_neg, Complex.exp_pi_mul_I]
      norm_num
    rw [ftArcPoint, hexp]
    push_cast
    ring
  rwa [harc, re_ftBranchLimit_ofReal] at h

/-- A strictly increasing real function whose modulus diverges at the right
endpoint diverges upward there: the value at any interior point is a fixed lower
bound, so the branch of the modulus that would send it down is excluded. -/
theorem tendsto_atTop_of_abs_atTop_of_strictMonoOn {z : ℝ → ℝ} {p q : ℝ} (hpq : p < q)
    (hmono : StrictMonoOn z (Set.Ioo p q))
    (h : Filter.Tendsto (fun θ => |z θ|) (nhdsWithin q (Set.Ioo p q)) Filter.atTop) :
    Filter.Tendsto z (nhdsWithin q (Set.Ioo p q)) Filter.atTop := by
  have hθ₀ : (p + q) / 2 ∈ Set.Ioo p q := ⟨by linarith, by linarith⟩
  refine Filter.tendsto_atTop.2 fun M => ?_
  have hbig := Filter.tendsto_atTop.1 h (max M (|z ((p + q) / 2)| + 1))
  have hnear : Set.Ioo ((p + q) / 2) q ∈ nhdsWithin q (Set.Ioo p q) :=
    nhdsWithin_mono q Set.Ioo_subset_Iio_self (Ioo_mem_nhdsLT hθ₀.2)
  filter_upwards [hbig, hnear, self_mem_nhdsWithin] with θ hθbig hθnear hθmem
  have hlt : z ((p + q) / 2) < z θ := hmono hθ₀ hθmem hθnear.1
  rcases abs_cases (z θ) with ⟨he, _⟩ | ⟨he, _⟩
  · rw [he] at hθbig
    exact le_trans (le_max_left _ _) hθbig
  · rw [he] at hθbig
    have h1 : |z ((p + q) / 2)| + 1 ≤ -z θ :=
      le_trans (le_max_right M (|z ((p + q) / 2)| + 1)) hθbig
    have h2 := neg_abs_le (z ((p + q) / 2))
    linarith

/-- **Lemma 6 at the unbounded upper endpoint** — `eq:ab-def`'s `b = +∞` for
`r > 1`.  When the branch point runs into the origin the parameter leaves every
bound, and monotonicity fixes the direction. -/
theorem tendsto_ftBranchZ_atTop_of_tendsto_ftTau_zero {n r l : ℕ} {a : Fin n → ℝ} {c : ℝ}
    (hr : 1 ≤ r) (hc : c ≠ 0) (ha : ∀ k, 0 < a k) {p q : ℝ} (hpq : p < q)
    (hmono : StrictMonoOn (ftBranchZ a c r l) (Set.Ioo p q))
    (hmem : ∀ᶠ θ in nhdsWithin q (Set.Ioo p q), θ ∈ Set.Ioo 0 Real.pi ∧ FTBranchAt a r l θ)
    (hτ : Filter.Tendsto (ftTau a r l) (nhdsWithin q (Set.Ioo p q)) (nhds 0)) :
    Filter.Tendsto (ftBranchZ a c r l) (nhdsWithin q (Set.Ioo p q)) Filter.atTop := by
  have hP0 : (ftRootPoly c a).eval 0 ≠ 0 := by
    rw [eval_ftRootPoly]
    refine mul_ne_zero (Complex.ofReal_ne_zero.2 hc) (Finset.prod_ne_zero_iff.2 fun k _ => ?_)
    simpa using Complex.ofReal_ne_zero.2 (ha k).ne'
  have hγ : Filter.Tendsto (fun θ : ℝ => ftArcPoint (ftTau a r l θ) θ)
      (nhdsWithin q (Set.Ioo p q)) (nhds 0) := by
    simpa [ftArcPoint] using tendsto_branchPoint_of_tendsto_tau (τ := ftTau a r l) hτ
  have hne : ∀ᶠ θ in nhdsWithin q (Set.Ioo p q), ftArcPoint (ftTau a r l θ) θ ≠ 0 := by
    filter_upwards [hmem] with θ hθ
    rw [ftArcPoint]
    exact mul_ne_zero (Complex.ofReal_ne_zero.2 (ftTau_pos hθ.2).ne')
      (Complex.exp_ne_zero _)
  have hnorm := tendsto_norm_ftZ_atTop_of_tendsto_zero (P := ftRootPoly c a) hr hP0 hne hγ
  refine tendsto_atTop_of_abs_atTop_of_strictMonoOn hpq hmono (Filter.Tendsto.congr' ?_ hnorm)
  filter_upwards [hmem] with θ hθ
  rw [eval_ftRootPoly, ftBranch_ftArcPoint_eq_ftBranchZ c ha hθ.1 hθ.2,
    Complex.norm_real, Real.norm_eq_abs]

/-- **`Forgacs2017RationalDenominator` Lemma 6, lower endpoint, closed.**  Along
the principal branch the spectral parameter converges as `θ ↓ 0`, with no
hypothesis about limits assumed: `FTBranchEndpoint` supplies the convergence of
`τ` and this is its transfer.  This is `FTGeometryAssembly.ft_geometry`'s `hza`,
at the arc's own filter.

**The quadratic case is not excluded here, and that is not in tension with
`thm:FT-geometry`.**  That theorem excludes `(deg Q, r) = (2,1)` because the
*geometry* degenerates there: `Q(t) + zt` has constant term `Q(0)` and leading
coefficient independent of `z`, so the product of its two zeros is fixed and the
branch radius `τ` is constant in `θ` — which is the strict monotonicity of
`Forgacs2017RationalDenominator` Lemma 3 failing, not the limit failing.  A
constant function converges, and its limit is the positive zero of the critical
polynomial: for `P = c(a_1-t)(a_2-t)` and `r = 1` one has
`E(t) = tP'(t) - P(t) = c(t^2 - a_1a_2)`, whose positive zero `√{a_1a_2}` is
exactly that constant `τ`.  So the endpoint statement is true on a case the
geometry statement must exclude, and `exists_tendsto_ftBranchZ_arc_zero_quadratic`
is the witness.  `rem:quadratic-case` is where the paper treats that case, and
`QuadraticDefect` proves it outright. -/
theorem exists_tendsto_ftBranchZ_arc_zero {n r : ℕ} {a : Fin n → ℝ} (c : ℝ)
    (hn2 : 2 ≤ n) (ha : ∀ k, 0 < a k) (hr : 1 ≤ r) (hc : 0 < c) :
    ∃ za : ℝ, Filter.Tendsto (ftBranchZ a c r (n - 1))
      (nhdsWithin 0 (Set.Ioo 0 (Real.pi / r))) (nhds za) := by
  obtain ⟨L, hL, hτ, _⟩ := exists_tendsto_ftTau_nhdsGT_zero_of_two_le hn2 ha hr hc
  refine ⟨-(ftRootPolyReal c a).eval L / L ^ r, ?_⟩
  refine tendsto_ftBranchZ_lower ha hL ?_
    (hτ.mono_left (nhdsWithin_mono 0 Set.Ioo_subset_Ioi_self))
  filter_upwards [self_mem_nhdsWithin] with θ hθ
  exact ⟨ftArc_subset hr hθ,
    ftBranchAt_of_arc_principal (by omega) ha hr (Or.inl hn2) hθ⟩

/-- **`FTGeometryAssembly.ft_geometry`'s `hzcont`, at the actual objects.**  The
spectral parameter is continuous on the viewing arc.

**Differs from the paper's route.**  `subsec:FT-geometry` reads continuity off
the regularity of the branch — `z` is differentiable where `τ` is, and the
derivative is computed.  Here it is read off `ftBranchZ_eq_chordProd` instead:
along the principal branch `z(θ) = c·∏_k|τ(θ)e^{iθ} - x_k|/τ(θ)^r`, whose factors
are square roots of polynomials in `τ(θ)` and `cos θ`, so only continuity of `τ`
is consumed and no derivative is formed.  The parity `n + (n-1) + 1 = 2n` is what
makes the sign in `ftBranchZ` disappear and the two expressions agree. -/
theorem continuousOn_ftBranchZ {n r : ℕ} {a : Fin n → ℝ} (c : ℝ) (hn : 0 < n)
    (ha : ∀ k, 0 < a k) (hr : 1 ≤ r) (hnr : 2 ≤ n ∨ 2 ≤ r) :
    ContinuousOn (ftBranchZ a c r (n - 1)) (Set.Ioo 0 (Real.pi / r)) := by
  have hb : ∀ θ ∈ Set.Ioo 0 (Real.pi / r), FTBranchAt a r (n - 1) θ := fun θ hθ =>
    ftBranchAt_of_arc_principal hn ha hr hnr hθ
  have hτ : ContinuousOn (ftTau a r (n - 1)) (Set.Ioo 0 (Real.pi / r)) := fun θ hθ =>
    (continuousAt_ftTau hn ha hr hθ hb).continuousWithinAt
  have hprod : ContinuousOn (fun θ => ftChordProd a (ftTau a r (n - 1) θ) θ)
      (Set.Ioo 0 (Real.pi / r)) := by
    unfold ftChordProd
    refine continuousOn_finsetProd _ fun k _ => Real.continuous_sqrt.comp_continuousOn ?_
    exact ((continuousOn_const.sub
      ((continuousOn_const.mul hτ).mul Real.continuous_cos.continuousOn)).add (hτ.pow 2))
  have hg : ContinuousOn
      (fun θ => c * ftChordProd a (ftTau a r (n - 1) θ) θ / ftTau a r (n - 1) θ ^ r)
      (Set.Ioo 0 (Real.pi / r)) :=
    (continuousOn_const.mul hprod).div (hτ.pow r)
      fun θ hθ => pow_ne_zero r (ftTau_pos (hb θ hθ)).ne'
  refine hg.congr fun θ hθ => ?_
  have hpar : Even (n + (n - 1) + 1) := by
    have hEq : n + (n - 1) + 1 = 2 * n := by omega
    rw [hEq]; exact even_two_mul n
  exact ftBranchZ_eq_chordProd ha hpar (ftArc_subset hr hθ) (hb θ hθ) rfl

/-- Non-vacuity of `exists_tendsto_ftBranchZ_arc_zero`, witnessed at `r = 1`.
That regime is the one `FTGeometryAssembly.ft_geometry` needs — its finite `b` is
the `r = 1` convention — and it is reachable: the hypotheses are met at `n = 3`,
`r = 1`, which is `P = (1-t)^3`. -/
theorem exists_tendsto_ftBranchZ_arc_zero_nonvacuous :
    ∃ za : ℝ, Filter.Tendsto (ftBranchZ (fun _ : Fin 3 => (1 : ℝ)) 1 1 2)
      (nhdsWithin 0 (Set.Ioo 0 (Real.pi / ((1 : ℕ) : ℝ)))) (nhds za) :=
  exists_tendsto_ftBranchZ_arc_zero (n := 3) (r := 1) (a := fun _ => 1) 1
    (by omega) (fun _ => one_pos) (by omega) one_pos

/-- The quadratic case `(deg Q, r) = (2,1)` is reached too — the case
`thm:FT-geometry` excludes and `rem:quadratic-case` treats.  `τ` is constant
there, so the limit is immediate; see the note on
`exists_tendsto_ftBranchZ_arc_zero` for why that is consistent rather than an
overclaim. -/
theorem exists_tendsto_ftBranchZ_arc_zero_quadratic :
    ∃ za : ℝ, Filter.Tendsto (ftBranchZ (fun _ : Fin 2 => (1 : ℝ)) 1 1 1)
      (nhdsWithin 0 (Set.Ioo 0 (Real.pi / ((1 : ℕ) : ℝ)))) (nhds za) :=
  exists_tendsto_ftBranchZ_arc_zero (n := 2) (r := 1) (a := fun _ => 1) 1
    (by omega) (fun _ => one_pos) (by omega) one_pos

end ForgacsTran
