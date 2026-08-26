/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import ForgacsTran.ConsequencesComposition.PhaseQuantization

/-!
# The local strong clock, composed, and carried back to `F_M`

The second half: the two `ψ` estimates `local_clock_spacing` consumes, the Taylor
producer that supplies them in `Amplitude`'s parametric idiom, the composition of
`eq:local-strong-clock`, and the transport of the whole statement back to the
coefficient sequence `F_M` the paper actually speaks about.

## Main statements

* the statements of `### local_clock_spacing's two ψ estimates` — the two bounds
  on the phase and its derivative that the spacing law is stated against.
* the statements of `### htaylor's producer` — those estimates produced from a
  Taylor expansion in `Amplitude`'s parametric form, rather than assumed.
* the statements of `### eq:local-strong-clock, composed` — the spacing law with
  every hypothesis discharged.
* the statements of `### Back to F_M` — the same statement about the coefficient
  sequence, which is the object `sec:consequences` states its laws for.

## References

* `../../shields-2026-forgacs-tran-numerators.tex`, «Global and local zero laws» —
  `sec:consequences`, `eq:local-strong-clock`.

## Tags

clock spacing, local zero law, Taylor expansion, coefficient sequence
-/

namespace ForgacsTran

open Real

/-! ### `local_clock_spacing`'s two `ψ` estimates

`hmvt` and `htaylor` are the mean-value and first-order Taylor bounds on the
phase.  Both are proved here from the regularity the step actually consumes,
which is less than the paper spends.

**Differs from the paper's route.**  The manuscript obtains them from
real-analyticity: `W` is real-analytic and nonvanishing on `𝒥_0`, hence
`ψ` is real-analytic and `ψ''` is bounded, hence Taylor.  Analyticity is how
the paper *gets* the bounded second derivative; it is not what the Taylor step
*uses*.  `phase_taylor_bound` takes the `C^2` hypothesis directly — `ψ'`
differentiable with `|ψ''| ≤ κ_2` — and analyticity of `W` along the
branch, which is much heavier to establish, never appears. -/

/-- **`hmvt`.**  A bound on `ψ'` is a Lipschitz bound on `ψ`, by the mean
value theorem on a convex set. -/
theorem phase_mvt_bound {ψ dψ : ℝ → ℝ} {a b κ θk θk1 : ℝ}
    (hψd : ∀ θ ∈ Set.Icc a b, HasDerivAt ψ (dψ θ) θ)
    (hκ : ∀ θ ∈ Set.Icc a b, |dψ θ| ≤ κ)
    (hk : θk ∈ Set.Icc a b) (hk1 : θk1 ∈ Set.Icc a b) (hle : θk ≤ θk1) :
    |ψ θk1 - ψ θk| ≤ κ * (θk1 - θk) := by
  have h := (convex_Icc a b).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := ψ) (f' := dψ) (C := κ)
    (fun x hx => (hψd x hx).hasDerivWithinAt)
    (fun x hx => by simpa [Real.norm_eq_abs] using hκ x hx) hk hk1
  simpa [Real.norm_eq_abs, abs_of_nonneg (by linarith : (0:ℝ) ≤ θk1 - θk)] using h

/-- **`htaylor`.**  First-order Taylor with an `O(Δ^2)` remainder, from a
bound on `ψ''` and nothing else.  The argument is the mean value theorem
applied twice: once to `ψ'`, giving `|ψ'(t) - ψ'(θ_k)| ≤ κ_2Δ`
across the step, and once to `ψ(t) - ψ'(θ_k)t`, whose derivative is
exactly that difference. -/
theorem phase_taylor_bound {ψ dψ ddψ : ℝ → ℝ} {a b κ₂ θk θk1 : ℝ}
    (hψd : ∀ θ ∈ Set.Icc a b, HasDerivAt ψ (dψ θ) θ)
    (hψdd : ∀ θ ∈ Set.Icc a b, HasDerivAt dψ (ddψ θ) θ)
    (hκ₂ : ∀ θ ∈ Set.Icc a b, |ddψ θ| ≤ κ₂)
    (hk : θk ∈ Set.Icc a b) (hk1 : θk1 ∈ Set.Icc a b) (hle : θk ≤ θk1) :
    |ψ θk1 - ψ θk - dψ θk * (θk1 - θk)| ≤ κ₂ * (θk1 - θk) ^ 2 := by
  have hΔ : (0 : ℝ) ≤ θk1 - θk := by linarith
  -- the derivative of `ψ` moves by at most `κ₂Δ` across the step
  have hslope : ∀ θ ∈ Set.Icc a b, θk ≤ θ → θ ≤ θk1 →
      |dψ θ - dψ θk| ≤ κ₂ * (θk1 - θk) := by
    intro θ hθ h1 h2
    have h := (convex_Icc a b).norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := dψ) (f' := ddψ) (C := κ₂)
      (fun x hx => (hψdd x hx).hasDerivWithinAt)
      (fun x hx => by simpa [Real.norm_eq_abs] using hκ₂ x hx) hk hθ
    rw [Real.norm_eq_abs, Real.norm_eq_abs] at h
    have habs : |θ - θk| ≤ θk1 - θk := by
      rw [abs_of_nonneg (by linarith)]; linarith
    have hκ0 : (0 : ℝ) ≤ κ₂ := le_trans (abs_nonneg _) (hκ₂ θk hk)
    exact le_trans h (mul_le_mul_of_nonneg_left habs hκ0)
  -- the Taylor error is that slope integrated, by the mean value theorem again
  set g : ℝ → ℝ := fun θ => ψ θ - dψ θk * θ with hg
  have hgd : ∀ θ ∈ Set.Icc θk θk1, HasDerivWithinAt g (dψ θ - dψ θk) (Set.Icc θk θk1) θ := by
    intro θ hθ
    have hmem : θ ∈ Set.Icc a b := ⟨le_trans hk.1 hθ.1, le_trans hθ.2 hk1.2⟩
    have h1 : HasDerivAt (fun s : ℝ => dψ θk * s) (dψ θk) θ := by
      simpa using (hasDerivAt_id θ).const_mul (dψ θk)
    exact ((hψd θ hmem).sub h1).hasDerivWithinAt
  have hbound : ∀ θ ∈ Set.Icc θk θk1, ‖dψ θ - dψ θk‖ ≤ κ₂ * (θk1 - θk) := by
    intro θ hθ
    have hmem : θ ∈ Set.Icc a b := ⟨le_trans hk.1 hθ.1, le_trans hθ.2 hk1.2⟩
    simpa [Real.norm_eq_abs] using hslope θ hmem hθ.1 hθ.2
  have h := (convex_Icc θk θk1).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := g) (f' := fun θ => dψ θ - dψ θk) (C := κ₂ * (θk1 - θk))
    hgd hbound ⟨le_rfl, hle⟩ ⟨hle, le_rfl⟩
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hΔ] at h
  have hrw : g θk1 - g θk = ψ θk1 - ψ θk - dψ θk * (θk1 - θk) := by
    simp only [hg]; ring
  rw [hrw] at h
  calc |ψ θk1 - ψ θk - dψ θk * (θk1 - θk)| ≤ κ₂ * (θk1 - θk) * (θk1 - θk) := h
    _ = κ₂ * (θk1 - θk) ^ 2 := by ring

/-! ### `htaylor`'s producer, in `Amplitude`'s parametric idiom

`Amplitude.exists_phase_derivative_bound` takes the cofactor and its derivative
as *hypotheses* and never differentiates anything itself; the identity
`ψ' = Im(W'/W)` does the work and the regularity requirement sits on whoever
supplies `U`.  The second-order companion has the same shape, so the debt states
as *"the cofactor is twice differentiable along the branch"* rather than as a
missing construction.

These live here rather than in `Amplitude` only because that file is another
lane's and active; nothing in them depends on this module. -/

/-- **`ψ'' = Im(W''/W - (W'/W)^2)`.**  The quotient rule on the logarithmic
derivative, with the imaginary part taken — the exact second-order analogue of
`Amplitude.im_logDeriv_of_factor`. -/
theorem hasDerivAt_im_logDeriv {W dW ddW : ℝ → ℂ} {θ : ℝ}
    (hW : HasDerivAt W (dW θ) θ) (hdW : HasDerivAt dW (ddW θ) θ) (h0 : W θ ≠ 0) :
    HasDerivAt (fun s : ℝ => (dW s / W s).im)
      ((ddW θ / W θ - (dW θ / W θ) ^ 2).im) θ := by
  have hq : HasDerivAt (fun s : ℝ => dW s / W s)
      ((ddW θ * W θ - dW θ * dW θ) / W θ ^ 2) θ := hdW.div hW h0
  have heq : (ddW θ * W θ - dW θ * dW θ) / W θ ^ 2
      = ddW θ / W θ - (dW θ / W θ) ^ 2 := by
    field_simp
  rw [heq] at hq
  exact Complex.imCLM.hasFDerivAt.comp_hasDerivAt θ hq

/-- **The second-derivative bound, by compactness**, mirroring
`Amplitude.exists_phase_derivative_bound` one order up.  What it asks of the
branch is that `W` be twice differentiable with a continuous
`Im(W''/W - (W'/W)^2)`; what it gives is `htaylor`'s `κ_2`. -/
theorem exists_phase_second_derivative_bound {W dW ddW : ℝ → ℂ} {a b : ℝ}
    (hW : ∀ θ ∈ Set.Icc a b, HasDerivAt W (dW θ) θ)
    (hdW : ∀ θ ∈ Set.Icc a b, HasDerivAt dW (ddW θ) θ)
    (hW0 : ∀ θ ∈ Set.Icc a b, W θ ≠ 0)
    (hcont : ContinuousOn (fun θ => (ddW θ / W θ - (dW θ / W θ) ^ 2).im)
      (Set.Icc a b)) :
    ∃ κ₂ ≥ (0 : ℝ), ∀ θ ∈ Set.Icc a b,
      HasDerivAt (fun s : ℝ => (dW s / W s).im)
          ((ddW θ / W θ - (dW θ / W θ) ^ 2).im) θ ∧
        |(ddW θ / W θ - (dW θ / W θ) ^ 2).im| ≤ κ₂ := by
  obtain ⟨κ₂, hκ⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  refine ⟨max κ₂ 0, le_max_right _ _, fun θ hθ => ⟨?_, ?_⟩⟩
  · exact hasDerivAt_im_logDeriv (hW θ hθ) (hdW θ hθ) (hW0 θ hθ)
  · exact le_trans (by simpa [Real.norm_eq_abs] using hκ θ hθ) (le_max_left _ _)

/-- **`htaylor` at the paper's objects.**  `phase_taylor_bound` fed by the
logarithmic-derivative identity: on a compact zero-free subarc where `W` is twice
differentiable, the phase satisfies the first-order Taylor bound with a constant
produced by compactness rather than assumed.

This closes `local_clock_spacing`'s last input.  What the chain now rests on is
one regularity hypothesis on the branch — `W` twice differentiable with the
second logarithmic derivative continuous — stated where `W` enters, not scattered
through the composition. -/
theorem exists_phase_taylor_bound {W dW ddW : ℝ → ℂ} {ψ : ℝ → ℝ} {a b : ℝ}
    (hψd : ∀ θ ∈ Set.Icc a b, HasDerivAt ψ ((dW θ / W θ).im) θ)
    (hW : ∀ θ ∈ Set.Icc a b, HasDerivAt W (dW θ) θ)
    (hdW : ∀ θ ∈ Set.Icc a b, HasDerivAt dW (ddW θ) θ)
    (hW0 : ∀ θ ∈ Set.Icc a b, W θ ≠ 0)
    (hcont : ContinuousOn (fun θ => (ddW θ / W θ - (dW θ / W θ) ^ 2).im)
      (Set.Icc a b)) :
    ∃ κ₂ ≥ (0 : ℝ), ∀ θk ∈ Set.Icc a b, ∀ θk1 ∈ Set.Icc a b, θk ≤ θk1 →
      |ψ θk1 - ψ θk - (dW θk / W θk).im * (θk1 - θk)| ≤ κ₂ * (θk1 - θk) ^ 2 := by
  obtain ⟨κ₂, hκ0, hb⟩ := exists_phase_second_derivative_bound hW hdW hW0 hcont
  refine ⟨κ₂, hκ0, fun θk hk θk1 hk1 hle => ?_⟩
  exact phase_taylor_bound (dψ := fun θ => (dW θ / W θ).im)
    (ddψ := fun θ => (ddW θ / W θ - (dW θ / W θ) ^ 2).im)
    hψd (fun θ hθ => (hb θ hθ).1) (fun θ hθ => (hb θ hθ).2) hk hk1 hle


/-! ### Why `κ_2` may not be existential in the conclusion

`κ_2` is a constant of the pencil and the subarc, like `κ`: it bounds `ψ''`
uniformly there, and `exists_phase_taylor_bound` produces it at exactly that
scope.  A conclusion of the form `∃ κ_2 ≥ 0, … ≤ (2E + κ_2P)/D + Q` chooses it
*after* the two zeros instead, and the lemma below is why that says nothing —
the right side is strictly increasing and unbounded in `κ_2`, so **every** left
side is covered by a large enough choice.

That is not a quantifier nicety.  A route that dropped the `ψ''` term entirely
would still elaborate against such a statement, because it could absorb the
error into `κ_2`; the fitted rate of `scripts/check_cubic_strong_clock.py` would
fall from `-3.0082` to `-2.0076` and nothing in Lean would fail. -/

/-- **The absorbing choice, exhibited.**  With `P > 0` and `D > 0` the bound
`X ≤ (2E + κ_2P)/D + Q` holds for *every* `X` at a large enough `κ_2 ≥ 0`, so a
conclusion existential in `κ_2` at that position is vacuous.

Stated over bare reals so that it is about the shape rather than about the
clock. -/
theorem exists_absorbing_constant (X E D P Q : ℝ) (hD : 0 < D) (hP : 0 < P) :
    ∃ κ₂ ≥ (0 : ℝ), X ≤ (2 * E + κ₂ * P) / D + Q := by
  refine ⟨max 0 (((X - Q) * D - 2 * E) / P), le_max_left _ _, ?_⟩
  have hge : ((X - Q) * D - 2 * E) / P ≤ max 0 (((X - Q) * D - 2 * E) / P) :=
    le_max_right _ _
  have hmul : (X - Q) * D - 2 * E ≤ max 0 (((X - Q) * D - 2 * E) / P) * P := by
    rw [← div_le_iff₀ hP]
    exact hge
  have hstep : (X - Q) * D ≤ 2 * E + max 0 (((X - Q) * D - 2 * E) / P) * P := by
    linarith [hmul]
  have hfin : X - Q ≤ (2 * E + max 0 (((X - Q) * D - 2 * E) / P) * P) / D := by
    rw [le_div_iff₀ hD]; exact hstep
  linarith

/-! ### `eq:local-strong-clock`, composed

Every producer instantiated at once.  The composition is where the shapes are
tested against each other rather than read off individually, which is the step
that has found a defect in each of the last two rounds. -/

/-- **`eq:local-strong-clock` at the paper's objects.**  The spacing of two
consecutive zero angles, with every input supplied:

* `hquant` is `phase_quantization_identity`, applied here rather than assumed;
* `hek`, `hek1` are `phase_quantization_error`, so `E = (π/2)C` with `C` the
  `O(σ^M)` error of `interior_cos_decomposition_on_subarc`;
* `0 < Δ` is the ordering `exists_two_consecutive_phase_zeros` derives;
* `hmvt` is `phase_mvt_bound` and `htaylor` is `exists_phase_taylor_bound`;
* `hdψ`, `hL` are `eq:phase-derivative-bound`.

Nothing here is an analytic input: the analytic content entered at
`interior_cos_decomposition_on_subarc` and at the `C^1` and `C^2` regularity, and
what remains is the arithmetic `Consequences.local_clock_spacing` performs. -/
theorem ft_local_strong_clock {Φ ψ dψ : ℝ → ℝ} {L u₀ θk θk1 κ κ₂ C : ℝ}
    (hΦ : ∀ θ : ℝ, Φ θ = L * θ - ψ θ)
    (hκ0 : 0 ≤ κ) (hκ₂ : 0 ≤ κ₂) (hC : 0 ≤ C) (hL : κ + 1 ≤ L)
    (hlt : θk < θk1)
    (hdψ : |dψ θk| ≤ κ)
    (hek : |Φ θk - u₀| ≤ Real.pi / 2 * C)
    (hek1 : |Φ θk1 - (u₀ + Real.pi)| ≤ Real.pi / 2 * C)
    (hmvt : |ψ θk1 - ψ θk| ≤ κ * (θk1 - θk))
    (htaylor : |ψ θk1 - ψ θk - dψ θk * (θk1 - θk)| ≤ κ₂ * (θk1 - θk) ^ 2) :
    θk1 - θk ≤ (Real.pi + 2 * (Real.pi / 2 * C)) / (L - κ) ∧
      |(θk1 - θk) - Real.pi / L - Real.pi * dψ θk / L ^ 2|
        ≤ (2 * (Real.pi / 2 * C)
              + κ₂ * ((Real.pi + 2 * (Real.pi / 2 * C)) / (L - κ)) ^ 2) / (L - κ)
            + Real.pi * κ ^ 2 / (L ^ 2 * (L - κ)) := by
  have hE : (0 : ℝ) ≤ Real.pi / 2 * C :=
    mul_nonneg (by positivity) hC
  exact local_clock_spacing hκ0 hκ₂ hE hL (by linarith) hdψ hek hek1
    (phase_quantization_identity hΦ) hmvt htaylor

/-- **The same, with the error at its `O(M^{-3})` rate.**  `local_clock_rate`
applied to the composed bound at `L = M+1`: for every large `M` the spacing is
`π/(M+1) + πψ'/(M+1)^2` to within a constant over `(M+1)^3`, and the
constant carries no `M`.

This is `eq:local-strong-clock` as the paper states it. -/
theorem ft_local_strong_clock_rate {κ κ₂ A σ : ℝ} (hκ : 0 ≤ κ) (hκ₂ : 0 ≤ κ₂)
    (hA : 0 ≤ A) (hσ0 : 0 ≤ σ) (hσ1 : σ < 1) :
    ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
      ∀ {Φ ψ dψ : ℝ → ℝ} {u₀ θk θk1 C : ℝ},
        (∀ θ : ℝ, Φ θ = ((M : ℝ) + 1) * θ - ψ θ) →
        0 ≤ C → Real.pi / 2 * C ≤ A * σ ^ M → κ + 1 ≤ (M : ℝ) + 1 →
        θk < θk1 → |dψ θk| ≤ κ →
        |Φ θk - u₀| ≤ Real.pi / 2 * C →
        |Φ θk1 - (u₀ + Real.pi)| ≤ Real.pi / 2 * C →
        |ψ θk1 - ψ θk| ≤ κ * (θk1 - θk) →
        |ψ θk1 - ψ θk - dψ θk * (θk1 - θk)| ≤ κ₂ * (θk1 - θk) ^ 2 →
        |(θk1 - θk) - Real.pi / ((M : ℝ) + 1)
            - Real.pi * dψ θk / ((M : ℝ) + 1) ^ 2|
          ≤ (1 + 8 * κ₂ * (Real.pi + 2 * A) ^ 2 + 2 * Real.pi * κ ^ 2)
              / ((M : ℝ) + 1) ^ 3 := by
  obtain ⟨M₀, hM₀⟩ := local_clock_rate (κ := κ) (κ₂ := κ₂) (A := A) (σ := σ)
    hκ hκ₂ hA hσ0 hσ1
  refine ⟨M₀, fun M hM Φ ψ dψ u₀ θk θk1 C hΦ hC hCA hL hlt hdψ hek hek1 hmvt htaylor => ?_⟩
  obtain ⟨-, hspace⟩ := ft_local_strong_clock hΦ hκ hκ₂ hC hL hlt hdψ hek hek1 hmvt htaylor
  refine le_trans hspace ?_
  exact hM₀ M hM (Real.pi / 2 * C) (mul_nonneg (by positivity) hC) hCA

/-- **The composed hypothesis set is jointly satisfiable.**  At `ψ ≡ 0`,
`L = 2`, `κ = κ_2 = C = 0`, `u_0 = 0` and the two angles `0` and
`π/2`, every binder of `ft_local_strong_clock` holds and the conclusion is the
exactly tight statement `π/2 ≤ π/2` with zero second-order error — the
error-free clock, which is what the spacing law must degenerate to when the
phase is linear and the remainder vanishes.

Instantiating the *composition* matters separately from instantiating its
pieces: each producer was checked on its own, and this is the first point at
which their hypotheses have to hold simultaneously with the same constants. -/
theorem ft_local_strong_clock_nonvacuous :
    Real.pi / 2 - 0 ≤ (Real.pi + 2 * (Real.pi / 2 * 0)) / (2 - 0) ∧
      |(Real.pi / 2 - 0) - Real.pi / 2 - Real.pi * 0 / 2 ^ 2|
        ≤ (2 * (Real.pi / 2 * 0)
              + 0 * ((Real.pi + 2 * (Real.pi / 2 * 0)) / (2 - 0)) ^ 2) / (2 - 0)
            + Real.pi * 0 ^ 2 / (2 ^ 2 * (2 - 0)) := by
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  refine ft_local_strong_clock (Φ := fun θ => 2 * θ) (ψ := fun _ => 0)
    (dψ := fun _ => 0) (u₀ := 0) (θk := 0) (θk1 := Real.pi / 2)
    (fun θ => by ring) le_rfl le_rfl le_rfl (by norm_num) (by linarith)
    (by norm_num) (by norm_num) ?_ (by norm_num) (by norm_num)
  have : (2 : ℝ) * (Real.pi / 2) - (0 + Real.pi) = 0 := by ring
  rw [this]
  norm_num


/-! ### Back to `F_M`

Everything above localizes zeros of `cosΦ_M + e`, which is a statement about
a phase function.  `prop:local-strong-clock` is a claim about the zeros of
`F_M(z)`.  Dividing out the two positive factors — `τ^{M+1}` and `2|W|` — is
what turns the one into the other, and it is the step that makes the chain about
the paper's own object rather than about something adjacent to it. -/

/-- A real polynomial's complexification takes real values at real points, so a
vanishing real part is a vanishing value.  This is where `hPmap` earns its place
in the capstone's binder list: without it `Re F_M = 0` would not give
`F_M = 0`. -/
theorem eval_eq_zero_of_re_eq_zero {P : Polynomial ℝ} {x : ℝ}
    (hre : ((P.map (algebraMap ℝ ℂ)).eval ((x : ℝ) : ℂ)).re = 0) :
    (P.map (algebraMap ℝ ℂ)).eval ((x : ℝ) : ℂ) = 0 := by
  have hval : (P.map (algebraMap ℝ ℂ)).eval ((x : ℝ) : ℂ) = ((P.eval x : ℝ) : ℂ) := by
    rw [Polynomial.eval_map]
    simpa using Polynomial.eval₂_at_apply (algebraMap ℝ ℂ) x
  rw [hval] at hre ⊢
  rw [Complex.ofReal_re] at hre
  rw [hre, Complex.ofReal_zero]

/-- The normalizing power is a positive real, so it does not move the real
part's vanishing. -/
theorem re_scaled_eq_zero {τ : ℝ} (hτ : 0 < τ) {M : ℕ} {w : ℂ}
    (h : (((τ : ℝ) : ℂ) ^ (M + 1) * w).re = 0) : w.re = 0 := by
  have hpow : (((τ : ℝ) : ℂ)) ^ (M + 1) = (((τ ^ (M + 1) : ℝ)) : ℂ) := by
    rw [Complex.ofReal_pow]
  rw [hpow, Complex.re_ofReal_mul] at h
  have hne : (τ : ℝ) ^ (M + 1) ≠ 0 := by positivity
  exact (mul_eq_zero.1 h).resolve_left hne

/-- **`prop:local-strong-clock` is about `F_M`.**  A zero of the phase equation
is a zero of the coefficient polynomial: divide by `2|W| > 0`, then by
`τ^{M+1} > 0`, then use that `F_M` is real at a real point.

With this, `exists_unique_phase_zero` and `exists_two_consecutive_phase_zeros`
localize zeros of `F_M(z(θ))` itself, and `ft_local_strong_clock` spaces
them. -/
theorem ftCoeffPoly_eval_eq_zero_of_phase_zero {Q B : Polynomial ℂ} {r M : ℕ}
    {z τ ψ : ℝ → ℝ} {θ e : ℝ} {P : Polynomial ℝ}
    (hPmap : P.map (algebraMap ℝ ℂ) = ftCoeffPoly Q B r M)
    (hτ : 0 < τ θ) (hW : 0 < ftPrincipalAmp Q B r z τ θ)
    (hdecomp : ((((τ θ : ℝ) : ℂ)) ^ (M + 1)
          * (ftCoeffPoly Q B r M).eval ((z θ : ℝ) : ℂ)).re
        / (2 * ftPrincipalAmp Q B r z τ θ)
      = Real.cos (((M : ℝ) + 1) * θ - ψ θ) + e)
    (hzero : Real.cos (((M : ℝ) + 1) * θ - ψ θ) + e = 0) :
    (ftCoeffPoly Q B r M).eval ((z θ : ℝ) : ℂ) = 0 := by
  have h2W : (0 : ℝ) < 2 * ftPrincipalAmp Q B r z τ θ := by linarith
  have hquot : ((((τ θ : ℝ) : ℂ)) ^ (M + 1)
      * (ftCoeffPoly Q B r M).eval ((z θ : ℝ) : ℂ)).re
      / (2 * ftPrincipalAmp Q B r z τ θ) = 0 := by rw [hdecomp, hzero]
  have hre : ((((τ θ : ℝ) : ℂ)) ^ (M + 1)
      * (ftCoeffPoly Q B r M).eval ((z θ : ℝ) : ℂ)).re = 0 :=
    (div_eq_zero_iff.1 hquot).resolve_right h2W.ne'
  have hre' : ((ftCoeffPoly Q B r M).eval ((z θ : ℝ) : ℂ)).re = 0 :=
    re_scaled_eq_zero hτ hre
  rw [← hPmap] at hre' ⊢
  exact eval_eq_zero_of_re_eq_zero hre'

/-- **The producer table, composed.**  `local_clock_spacing` reached with every
input *applied* rather than assumed: `hquant` from `phase_quantization_identity`,
`hek`/`hek1` from `phase_quantization_error`, `hmvt` from `phase_mvt_bound`,
`htaylor` from `exists_phase_taylor_bound`.  What is left in the binder list is
the branch data and the `C^2` regularity, which is where the debt belongs.

Writing it out is what checks the table, and it caught three things a table
cannot see.

* `local_clock_spacing`'s `dψ` is a free real while the Taylor producer
  supplies the *logarithmic derivative* `Im(W'/W)`; they compose only at
  `dψ = Im(W'/W)`, which is `eq:phase-derivative-bound`'s own identity.
* `local_clock_spacing` wants `|dψ| ≤ κ` at the single point
  `θ_k`; `phase_mvt_bound` needs it at *every* point of the interval.  The
  same `eq:phase-derivative-bound` supplies both, but only the uniform form
  composes, and the elaborator rejected the pointwise one outright.
* `κ_2` is *existential* in the producer and a *parameter* of the consumer,
  appearing in its conclusion.  So the composition has to obtain `κ_2` and
  hand it on, which makes this statement existential too — and a version that
  merely carried the Taylor bound as a hypothesis would have left the producer
  uncalled and its four regularity inputs inert.

The third is the one a producer table is least able to catch: nothing about the
names is wrong, and the shapes differ only in a quantifier. -/
theorem ft_local_strong_clock_composed {Φ ψ : ℝ → ℝ} {W dW ddW : ℝ → ℂ}
    {L u₀ θk θk1 κ C a b : ℝ}
    (hΦ : ∀ θ : ℝ, Φ θ = L * θ - ψ θ)
    (hκ0 : 0 ≤ κ) (hC : 0 ≤ C) (hL : κ + 1 ≤ L)
    (hlt : θk < θk1) (hk : θk ∈ Set.Icc a b) (hk1 : θk1 ∈ Set.Icc a b)
    -- the phase is `arg W`, and `eq:phase-derivative-bound` bounds it uniformly
    (hψd : ∀ θ ∈ Set.Icc a b, HasDerivAt ψ ((dW θ / W θ).im) θ)
    (hdψ : ∀ θ ∈ Set.Icc a b, |(dW θ / W θ).im| ≤ κ)
    -- the `C^2` regularity, consumed by `exists_phase_taylor_bound`
    (hW : ∀ θ ∈ Set.Icc a b, HasDerivAt W (dW θ) θ)
    (hdW : ∀ θ ∈ Set.Icc a b, HasDerivAt dW (ddW θ) θ)
    (hW0 : ∀ θ ∈ Set.Icc a b, W θ ≠ 0)
    (hcont : ContinuousOn (fun θ => (ddW θ / W θ - (dW θ / W θ) ^ 2).im) (Set.Icc a b))
    -- the two quantization points
    (hcos : Real.cos u₀ = 0)
    (hnear : |Φ θk - u₀| ≤ Real.pi / 2)
    (hnear1 : |Φ θk1 - (u₀ + Real.pi)| ≤ Real.pi / 2)
    {ε ε1 : ℝ} (hz : Real.cos (Φ θk) + ε = 0) (hz1 : Real.cos (Φ θk1) + ε1 = 0)
    (hε : |ε| ≤ C) (hε1 : |ε1| ≤ C) :
    ∃ κ₂ ≥ (0 : ℝ),
      θk1 - θk ≤ (Real.pi + 2 * (Real.pi / 2 * C)) / (L - κ) ∧
        |(θk1 - θk) - Real.pi / L - Real.pi * (dW θk / W θk).im / L ^ 2|
          ≤ (2 * (Real.pi / 2 * C)
                + κ₂ * ((Real.pi + 2 * (Real.pi / 2 * C)) / (L - κ)) ^ 2) / (L - κ)
              + Real.pi * κ ^ 2 / (L ^ 2 * (L - κ)) := by
  have hcos1 : Real.cos (u₀ + Real.pi) = 0 := by rw [Real.cos_add_pi, hcos, neg_zero]
  obtain ⟨κ₂, hκ₂, htay⟩ := exists_phase_taylor_bound hψd hW hdW hW0 hcont
  exact ⟨κ₂, hκ₂,
    ft_local_strong_clock (dψ := fun θ => (dW θ / W θ).im) hΦ hκ0 hκ₂ hC hL hlt
      (hdψ θk hk)
      (phase_quantization_error hcos hnear hz hε)
      (phase_quantization_error hcos1 hnear1 hz1 hε1)
      (phase_mvt_bound hψd hdψ hk hk1 hlt.le)
      (htay θk hk θk1 hk1 hlt.le)⟩

/-- **`prop:local-strong-clock`, its own conclusion.**  Two consecutive zeros of
`F_M` in `z(𝒥)`, ordered, with `eq:local-strong-clock`'s spacing law
between their angles.

Everything is applied rather than assumed: the pair from
`exists_two_consecutive_phase_zeros`, the passage to `F_M` from
`ftCoeffPoly_eval_eq_zero_of_phase_zero`, and the spacing from
`ft_local_strong_clock_composed`, which itself calls the quantization, the mean
value bound and the Taylor producer.  What is left in the binder list is the
branch data, the `C^2` regularity, and the decomposition — all supplier-side.

This is the statement the chain existed to reach: before it, the tree localized
zeros of a phase function and spaced them; the zeros here are zeros of the
coefficient polynomial the paper is about. -/
theorem ft_local_strong_clock_on_FM {Q B : Polynomial ℂ} {r M : ℕ}
    {z τ ψ Φ dΦ e de : ℝ → ℝ} {W dW ddW : ℝ → ℂ}
    {a b u₀ δ Ce L κ C : ℝ} {P : Polynomial ℝ}
    -- the phase and its window
    (hΦdef : ∀ θ : ℝ, Φ θ = L * θ - ψ θ) (hL : L = (M : ℝ) + 1)
    (hab : a ≤ b) (hcos : Real.cos u₀ = 0) (hδ : 0 < δ) (hδ4 : δ ≤ Real.pi / 4)
    (hmono : StrictMonoOn Φ (Set.Icc a b))
    (hΦd : ∀ θ ∈ Set.Icc a b, HasDerivAt Φ (dΦ θ) θ)
    (hed : ∀ θ ∈ Set.Icc a b, HasDerivAt e (de θ) θ)
    (hΦpos : ∀ θ ∈ Set.Icc a b, 0 < dΦ θ)
    (hdeb : ∀ θ ∈ Set.Icc a b, |de θ| ≤ Ce)
    (hCe : ∀ θ ∈ Set.Icc a b, Ce < Real.sqrt 2 / 2 * dΦ θ)
    (heb : ∀ θ ∈ Set.Icc a b, |e θ| < Real.sin δ)
    (hlo : Φ a ≤ u₀ - δ) (hhi : u₀ + Real.pi + δ ≤ Φ b)
    -- the passage back to `F_M`
    (hPmap : P.map (algebraMap ℝ ℂ) = ftCoeffPoly Q B r M)
    (hτ : ∀ θ ∈ Set.Icc a b, 0 < τ θ)
    (hW : ∀ θ ∈ Set.Icc a b, 0 < ftPrincipalAmp Q B r z τ θ)
    (hdec : ∀ θ ∈ Set.Icc a b,
      ((((τ θ : ℝ) : ℂ)) ^ (M + 1) * (ftCoeffPoly Q B r M).eval ((z θ : ℝ) : ℂ)).re
          / (2 * ftPrincipalAmp Q B r z τ θ)
        = Real.cos (Φ θ) + e θ)
    -- the spacing law's own inputs
    (hκ0 : 0 ≤ κ) (hCnn : 0 ≤ C) (hLκ : κ + 1 ≤ L)
    (hψd : ∀ θ ∈ Set.Icc a b, HasDerivAt ψ ((dW θ / W θ).im) θ)
    (hdψ : ∀ θ ∈ Set.Icc a b, |(dW θ / W θ).im| ≤ κ)
    (hWd : ∀ θ ∈ Set.Icc a b, HasDerivAt W (dW θ) θ)
    (hdWd : ∀ θ ∈ Set.Icc a b, HasDerivAt dW (ddW θ) θ)
    (hW0 : ∀ θ ∈ Set.Icc a b, W θ ≠ 0)
    (hcont : ContinuousOn (fun θ => (ddW θ / W θ - (dW θ / W θ) ^ 2).im) (Set.Icc a b))
    (hCeb : ∀ θ ∈ Set.Icc a b, |e θ| ≤ C) :
    ∃ θk ∈ Set.Icc a b, ∃ θk1 ∈ Set.Icc a b, θk < θk1 ∧
      (ftCoeffPoly Q B r M).eval ((z θk : ℝ) : ℂ) = 0 ∧
      (ftCoeffPoly Q B r M).eval ((z θk1 : ℝ) : ℂ) = 0 ∧
      ∃ κ₂ ≥ (0 : ℝ),
        θk1 - θk ≤ (Real.pi + 2 * (Real.pi / 2 * C)) / (L - κ) ∧
          |(θk1 - θk) - Real.pi / L - Real.pi * (dW θk / W θk).im / L ^ 2|
            ≤ (2 * (Real.pi / 2 * C)
                  + κ₂ * ((Real.pi + 2 * (Real.pi / 2 * C)) / (L - κ)) ^ 2) / (L - κ)
                + Real.pi * κ ^ 2 / (L ^ 2 * (L - κ)) := by
  obtain ⟨θk, hk, θk1, hk1, hlt, hzk, hzk1, hnear, hnear1⟩ :=
    exists_two_consecutive_phase_zeros hab hcos hδ hδ4 hmono hΦd hed hΦpos hdeb hCe heb
      hlo hhi
  -- `δ ≤ π/4` widens each window to the half-turn the quantization step wants
  have hδ2 : δ ≤ Real.pi / 2 := by linarith [Real.pi_pos]
  refine ⟨θk, hk, θk1, hk1, hlt, ?_, ?_, ?_⟩
  · exact ftCoeffPoly_eval_eq_zero_of_phase_zero (ψ := fun θ => ψ θ) hPmap (hτ θk hk)
      (hW θk hk) (by rw [hdec θk hk, hΦdef, hL]) (by rw [← hL, ← hΦdef θk]; exact hzk)
  · exact ftCoeffPoly_eval_eq_zero_of_phase_zero (ψ := fun θ => ψ θ) hPmap (hτ θk1 hk1)
      (hW θk1 hk1) (by rw [hdec θk1 hk1, hΦdef, hL]) (by rw [← hL, ← hΦdef θk1]; exact hzk1)
  · exact ft_local_strong_clock_composed hΦdef hκ0 hCnn hLκ hlt hk hk1 hψd hdψ hWd hdWd
      hW0 hcont hcos (hnear.le.trans hδ2) (hnear1.le.trans hδ2) hzk hzk1
      (hCeb θk hk) (hCeb θk1 hk1)

/-- **The two phase windows cannot both be imposed on the whole interval.**
`prop:local-strong-clock` places two consecutive quantization points a half turn
apart, so a bound holding at *every* angle of `[a,b]` cannot say that the phase
stays within `π/2` of the second one: the left endpoint is where `Φ` is below the
first point by `δ`, and that already contradicts it.

The quantization bounds `eq:local-phase-quantization` needs are therefore
pointwise, at `θk` and `θk1`, and `exists_two_consecutive_phase_zeros` returns
them there.  Stating them on the closed window instead is well-typed, is met by
nothing, and would make every conclusion drawn from the pair vacuous. -/
theorem not_forall_phase_near_second_point {Φ : ℝ → ℝ} {a b u₀ δ : ℝ}
    (hab : a ≤ b) (hδ : 0 < δ) (hlo : Φ a ≤ u₀ - δ)
    (hnear1 : ∀ θ ∈ Set.Icc a b, |Φ θ - (u₀ + Real.pi)| ≤ Real.pi / 2) : False := by
  have ha : a ∈ Set.Icc a b := ⟨le_rfl, hab⟩
  have h := abs_le.1 (hnear1 a ha)
  linarith [Real.pi_pos, h.1]

/-! ### The same, with `κ_2` where it belongs

`κ_2` bound before the zeros rather than after them, which is what makes
`eq:local-strong-clock` assert something (see `exists_absorbing_constant`).
`exists_phase_taylor_bound` produces it at exactly this scope, so a caller
obtains it once for the subarc and hands it down.

**Four hypotheses drop out.**  `hW`, `hdW`, `hW0` and `hcont` existed only to
feed `exists_phase_taylor_bound`; with the Taylor bound supplied they are gone,
so these forms are strictly weaker in hypotheses as well as strictly stronger in
conclusion. -/

/-- **`ft_local_strong_clock_composed` with `κ_2` a parameter.** -/
theorem ft_local_strong_clock_composed_of {Φ ψ : ℝ → ℝ} {W dW : ℝ → ℂ}
    {L u₀ θk θk1 κ κ₂ C a b : ℝ}
    (hΦ : ∀ θ : ℝ, Φ θ = L * θ - ψ θ)
    (hκ0 : 0 ≤ κ) (hκ₂ : 0 ≤ κ₂) (hC : 0 ≤ C) (hL : κ + 1 ≤ L)
    (hlt : θk < θk1) (hk : θk ∈ Set.Icc a b) (hk1 : θk1 ∈ Set.Icc a b)
    (hψd : ∀ θ ∈ Set.Icc a b, HasDerivAt ψ ((dW θ / W θ).im) θ)
    (hdψ : ∀ θ ∈ Set.Icc a b, |(dW θ / W θ).im| ≤ κ)
    (htay : ∀ θa ∈ Set.Icc a b, ∀ θb ∈ Set.Icc a b, θa ≤ θb →
      |ψ θb - ψ θa - (dW θa / W θa).im * (θb - θa)| ≤ κ₂ * (θb - θa) ^ 2)
    (hcos : Real.cos u₀ = 0)
    (hnear : |Φ θk - u₀| ≤ Real.pi / 2)
    (hnear1 : |Φ θk1 - (u₀ + Real.pi)| ≤ Real.pi / 2)
    {ε ε1 : ℝ} (hz : Real.cos (Φ θk) + ε = 0) (hz1 : Real.cos (Φ θk1) + ε1 = 0)
    (hε : |ε| ≤ C) (hε1 : |ε1| ≤ C) :
    θk1 - θk ≤ (Real.pi + 2 * (Real.pi / 2 * C)) / (L - κ) ∧
      |(θk1 - θk) - Real.pi / L - Real.pi * (dW θk / W θk).im / L ^ 2|
        ≤ (2 * (Real.pi / 2 * C)
              + κ₂ * ((Real.pi + 2 * (Real.pi / 2 * C)) / (L - κ)) ^ 2) / (L - κ)
            + Real.pi * κ ^ 2 / (L ^ 2 * (L - κ)) := by
  have hcos1 : Real.cos (u₀ + Real.pi) = 0 := by rw [Real.cos_add_pi, hcos, neg_zero]
  exact ft_local_strong_clock (dψ := fun θ => (dW θ / W θ).im) hΦ hκ0 hκ₂ hC hL hlt
    (hdψ θk hk)
    (phase_quantization_error hcos hnear hz hε)
    (phase_quantization_error hcos1 hnear1 hz1 hε1)
    (phase_mvt_bound hψd hdψ hk hk1 hlt.le)
    (htay θk hk θk1 hk1 hlt.le)

/-- **`ft_local_strong_clock_on_FM` with `κ_2` a parameter.**  The spacing law
between two consecutive zeros of `F_M`, at one `κ_2` fixed before the pair is
produced — so the second inequality is a claim about the pencil rather than a
choice made after the fact. -/
theorem ft_local_strong_clock_on_FM_of {Q B : Polynomial ℂ} {r M : ℕ}
    {z τ ψ Φ dΦ e de : ℝ → ℝ} {W dW : ℝ → ℂ}
    {a b u₀ δ Ce L κ κ₂ C : ℝ} {P : Polynomial ℝ}
    (hΦdef : ∀ θ : ℝ, Φ θ = L * θ - ψ θ) (hL : L = (M : ℝ) + 1)
    (hab : a ≤ b) (hcos : Real.cos u₀ = 0) (hδ : 0 < δ) (hδ4 : δ ≤ Real.pi / 4)
    (hmono : StrictMonoOn Φ (Set.Icc a b))
    (hΦd : ∀ θ ∈ Set.Icc a b, HasDerivAt Φ (dΦ θ) θ)
    (hed : ∀ θ ∈ Set.Icc a b, HasDerivAt e (de θ) θ)
    (hΦpos : ∀ θ ∈ Set.Icc a b, 0 < dΦ θ)
    (hdeb : ∀ θ ∈ Set.Icc a b, |de θ| ≤ Ce)
    (hCe : ∀ θ ∈ Set.Icc a b, Ce < Real.sqrt 2 / 2 * dΦ θ)
    (heb : ∀ θ ∈ Set.Icc a b, |e θ| < Real.sin δ)
    (hlo : Φ a ≤ u₀ - δ) (hhi : u₀ + Real.pi + δ ≤ Φ b)
    (hPmap : P.map (algebraMap ℝ ℂ) = ftCoeffPoly Q B r M)
    (hτ : ∀ θ ∈ Set.Icc a b, 0 < τ θ)
    (hW : ∀ θ ∈ Set.Icc a b, 0 < ftPrincipalAmp Q B r z τ θ)
    (hdec : ∀ θ ∈ Set.Icc a b,
      ((((τ θ : ℝ) : ℂ)) ^ (M + 1) * (ftCoeffPoly Q B r M).eval ((z θ : ℝ) : ℂ)).re
          / (2 * ftPrincipalAmp Q B r z τ θ)
        = Real.cos (Φ θ) + e θ)
    (hκ0 : 0 ≤ κ) (hκ₂ : 0 ≤ κ₂) (hCnn : 0 ≤ C) (hLκ : κ + 1 ≤ L)
    (hψd : ∀ θ ∈ Set.Icc a b, HasDerivAt ψ ((dW θ / W θ).im) θ)
    (hdψ : ∀ θ ∈ Set.Icc a b, |(dW θ / W θ).im| ≤ κ)
    (htay : ∀ θa ∈ Set.Icc a b, ∀ θb ∈ Set.Icc a b, θa ≤ θb →
      |ψ θb - ψ θa - (dW θa / W θa).im * (θb - θa)| ≤ κ₂ * (θb - θa) ^ 2)
    (hCeb : ∀ θ ∈ Set.Icc a b, |e θ| ≤ C) :
    ∃ θk ∈ Set.Icc a b, ∃ θk1 ∈ Set.Icc a b, θk < θk1 ∧
      (ftCoeffPoly Q B r M).eval ((z θk : ℝ) : ℂ) = 0 ∧
      (ftCoeffPoly Q B r M).eval ((z θk1 : ℝ) : ℂ) = 0 ∧
      θk1 - θk ≤ (Real.pi + 2 * (Real.pi / 2 * C)) / (L - κ) ∧
        |(θk1 - θk) - Real.pi / L - Real.pi * (dW θk / W θk).im / L ^ 2|
          ≤ (2 * (Real.pi / 2 * C)
                + κ₂ * ((Real.pi + 2 * (Real.pi / 2 * C)) / (L - κ)) ^ 2) / (L - κ)
              + Real.pi * κ ^ 2 / (L ^ 2 * (L - κ)) := by
  obtain ⟨θk, hk, θk1, hk1, hlt, hzk, hzk1, hnear, hnear1⟩ :=
    exists_two_consecutive_phase_zeros hab hcos hδ hδ4 hmono hΦd hed hΦpos hdeb hCe heb
      hlo hhi
  have hδ2 : δ ≤ Real.pi / 2 := by linarith [Real.pi_pos]
  refine ⟨θk, hk, θk1, hk1, hlt, ?_, ?_, ?_⟩
  · exact ftCoeffPoly_eval_eq_zero_of_phase_zero (ψ := fun θ => ψ θ) hPmap (hτ θk hk)
      (hW θk hk) (by rw [hdec θk hk, hΦdef, hL]) (by rw [← hL, ← hΦdef θk]; exact hzk)
  · exact ftCoeffPoly_eval_eq_zero_of_phase_zero (ψ := fun θ => ψ θ) hPmap (hτ θk1 hk1)
      (hW θk1 hk1) (by rw [hdec θk1 hk1, hΦdef, hL]) (by rw [← hL, ← hΦdef θk1]; exact hzk1)
  · exact ft_local_strong_clock_composed_of hΦdef hκ0 hκ₂ hCnn hLκ hlt hk hk1 hψd hdψ
      htay hcos (hnear.le.trans hδ2) (hnear1.le.trans hδ2) hzk hzk1
      (hCeb θk hk) (hCeb θk1 hk1)

/-- **The converse: a zero of `F_M` is a zero of the phase equation.**  If the
coefficient vanishes the numerator does, so the quotient does, so `cosΦ + e`
does.

`ftCoeffPoly_eval_eq_zero_of_phase_zero` is the forward direction and needs real
coefficients, the positivity of `τ` and of `2|W|`; this direction needs none of
them — only the decomposition itself.  Without it there is no way to say that
zeros of `F_M` are *only* the ones the phase produced, which is what
`prop:local-strong-clock`'s "every zero of `F_M` in `z(𝒥)` … is `z(θ_{k,M})`"
asserts and what makes a pair *consecutive* rather than merely spaced. -/
theorem phase_zero_of_ftCoeffPoly_eval_eq_zero {Q B : Polynomial ℂ} {r M : ℕ}
    {z τ : ℝ → ℝ} {θ u e : ℝ}
    (hdecomp : ((((τ θ : ℝ) : ℂ)) ^ (M + 1)
          * (ftCoeffPoly Q B r M).eval ((z θ : ℝ) : ℂ)).re
        / (2 * ftPrincipalAmp Q B r z τ θ)
      = Real.cos u + e)
    (hzero : (ftCoeffPoly Q B r M).eval ((z θ : ℝ) : ℂ) = 0) :
    Real.cos u + e = 0 := by
  rw [← hdecomp, hzero, mul_zero, Complex.zero_re, zero_div]

/-- **`ft_local_strong_clock_on_FM_of`, with the pair shown CONSECUTIVE.**  Same
two zeros and the same spacing law, plus the clause `prop:local-strong-clock`
states and the spacing bound alone does not: **no zero of `F_M` lies strictly
between them**.

That clause is what makes `eq:local-strong-clock` a clock rather than an
estimate.  A pair satisfying `π/(M+1) + πψ'/(M+1)^2 + O(M^{-3})` with
unaccounted zeros in between is compatible with the inequality and not with the
proposition.

It is reached by reading the quantization backwards: the isolation of the phase
zeros (`PhaseQuantization.exists_two_consecutive_phase_zeros_isolated`) plus
`phase_zero_of_ftCoeffPoly_eval_eq_zero`, which carries a zero of `F_M` back to
a zero of `cosΦ + e`. -/
theorem ft_local_strong_clock_on_FM_consecutive {Q B : Polynomial ℂ} {r M : ℕ}
    {z τ ψ Φ dΦ e de : ℝ → ℝ} {W dW : ℝ → ℂ}
    {a b u₀ δ Ce L κ κ₂ C : ℝ} {P : Polynomial ℝ}
    (hΦdef : ∀ θ : ℝ, Φ θ = L * θ - ψ θ) (hL : L = (M : ℝ) + 1)
    (hab : a ≤ b) (hcos : Real.cos u₀ = 0) (hδ : 0 < δ) (hδ4 : δ ≤ Real.pi / 4)
    (hmono : StrictMonoOn Φ (Set.Icc a b))
    (hΦd : ∀ θ ∈ Set.Icc a b, HasDerivAt Φ (dΦ θ) θ)
    (hed : ∀ θ ∈ Set.Icc a b, HasDerivAt e (de θ) θ)
    (hΦpos : ∀ θ ∈ Set.Icc a b, 0 < dΦ θ)
    (hdeb : ∀ θ ∈ Set.Icc a b, |de θ| ≤ Ce)
    (hCe : ∀ θ ∈ Set.Icc a b, Ce < Real.sqrt 2 / 2 * dΦ θ)
    (heb : ∀ θ ∈ Set.Icc a b, |e θ| < Real.sin δ)
    (hlo : Φ a ≤ u₀ - δ) (hhi : u₀ + Real.pi + δ ≤ Φ b)
    (hPmap : P.map (algebraMap ℝ ℂ) = ftCoeffPoly Q B r M)
    (hτ : ∀ θ ∈ Set.Icc a b, 0 < τ θ)
    (hW : ∀ θ ∈ Set.Icc a b, 0 < ftPrincipalAmp Q B r z τ θ)
    (hdec : ∀ θ ∈ Set.Icc a b,
      ((((τ θ : ℝ) : ℂ)) ^ (M + 1) * (ftCoeffPoly Q B r M).eval ((z θ : ℝ) : ℂ)).re
          / (2 * ftPrincipalAmp Q B r z τ θ)
        = Real.cos (Φ θ) + e θ)
    (hκ0 : 0 ≤ κ) (hκ₂ : 0 ≤ κ₂) (hCnn : 0 ≤ C) (hLκ : κ + 1 ≤ L)
    (hψd : ∀ θ ∈ Set.Icc a b, HasDerivAt ψ ((dW θ / W θ).im) θ)
    (hdψ : ∀ θ ∈ Set.Icc a b, |(dW θ / W θ).im| ≤ κ)
    (htay : ∀ θa ∈ Set.Icc a b, ∀ θb ∈ Set.Icc a b, θa ≤ θb →
      |ψ θb - ψ θa - (dW θa / W θa).im * (θb - θa)| ≤ κ₂ * (θb - θa) ^ 2)
    (hCeb : ∀ θ ∈ Set.Icc a b, |e θ| ≤ C) :
    ∃ θk ∈ Set.Icc a b, ∃ θk1 ∈ Set.Icc a b, θk < θk1 ∧
      (ftCoeffPoly Q B r M).eval ((z θk : ℝ) : ℂ) = 0 ∧
      (ftCoeffPoly Q B r M).eval ((z θk1 : ℝ) : ℂ) = 0 ∧
      (∀ θ ∈ Set.Icc a b, θk < θ → θ < θk1 →
        (ftCoeffPoly Q B r M).eval ((z θ : ℝ) : ℂ) ≠ 0) ∧
      θk1 - θk ≤ (Real.pi + 2 * (Real.pi / 2 * C)) / (L - κ) ∧
        |(θk1 - θk) - Real.pi / L - Real.pi * (dW θk / W θk).im / L ^ 2|
          ≤ (2 * (Real.pi / 2 * C)
                + κ₂ * ((Real.pi + 2 * (Real.pi / 2 * C)) / (L - κ)) ^ 2) / (L - κ)
              + Real.pi * κ ^ 2 / (L ^ 2 * (L - κ)) := by
  obtain ⟨θk, hk, θk1, hk1, hlt, hzk, hzk1, hnear, hnear1, hiso⟩ :=
    exists_two_consecutive_phase_zeros_isolated hab hcos hδ hδ4 hmono hΦd hed hΦpos
      hdeb hCe heb hlo hhi
  have hδ2 : δ ≤ Real.pi / 2 := by linarith [Real.pi_pos]
  refine ⟨θk, hk, θk1, hk1, hlt, ?_, ?_, ?_, ?_⟩
  · exact ftCoeffPoly_eval_eq_zero_of_phase_zero (ψ := fun θ => ψ θ) hPmap (hτ θk hk)
      (hW θk hk) (by rw [hdec θk hk, hΦdef, hL]) (by rw [← hL, ← hΦdef θk]; exact hzk)
  · exact ftCoeffPoly_eval_eq_zero_of_phase_zero (ψ := fun θ => ψ θ) hPmap (hτ θk1 hk1)
      (hW θk1 hk1) (by rw [hdec θk1 hk1, hΦdef, hL]) (by rw [← hL, ← hΦdef θk1]; exact hzk1)
  · -- the consecutiveness: an intervening zero of `F_M` would be a phase zero
    intro θ hθ hgt hltθ hzero
    exact hiso θ hθ hgt hltθ
      (phase_zero_of_ftCoeffPoly_eval_eq_zero (hdec θ hθ) hzero)
  · exact ft_local_strong_clock_composed_of hΦdef hκ0 hκ₂ hCnn hLκ hlt hk hk1 hψd hdψ
      htay hcos (hnear.le.trans hδ2) (hnear1.le.trans hδ2) hzk hzk1
      (hCeb θk hk) (hCeb θk1 hk1)

/-! ### Simplicity

`prop:local-strong-clock` asserts that every zero of `F_M` in `z(𝒥)` is
**simple**, which the spacing law does not give.  It comes from the same three
inequalities the quantization already carries, read at the zero rather than
across the window: `|e| < sinδ` pins `|cosΦ|` below `sinδ`, hence `|sinΦ|`
above `cosδ ≥ √2/2`; `Φ' > 0`; and `|e'| ≤ C_e < (√2/2)Φ'`.  So the phase
equation crosses transversally, and the decomposition carries that across to
`F_M`. -/

/-- **The phase equation crosses transversally at its zeros.**  `δ ≤ π/4` is
what makes `cosδ ≥ √2/2` meet `hCe` on the nose; the inequality is strict
because `hCe` is. -/
theorem deriv_phase_eq_ne_zero {Φ dΦ e de : ℝ → ℝ} {δ θ Ce : ℝ}
    (hδ : 0 < δ) (hδ4 : δ ≤ Real.pi / 4)
    (hΦpos : 0 < dΦ θ) (hde : |de θ| ≤ Ce) (hCe : Ce < Real.sqrt 2 / 2 * dΦ θ)
    (he : |e θ| < Real.sin δ) (hzero : Real.cos (Φ θ) + e θ = 0) :
    -Real.sin (Φ θ) * dΦ θ + de θ ≠ 0 := by
  have hπ := Real.pi_pos
  have hs2 : Real.sqrt 2 / 2 ≤ Real.cos δ := by
    rw [← Real.cos_pi_div_four]
    exact Real.cos_le_cos_of_nonneg_of_le_pi hδ.le (by linarith) hδ4
  have hsinδ : Real.sin δ ≤ 1 := Real.sin_le_one δ
  -- `|cos Φ| = |e| < sin δ`, so `sin²Φ > cos²δ`
  have hcos : |Real.cos (Φ θ)| < Real.sin δ := by
    have : Real.cos (Φ θ) = -e θ := by linarith
    rw [this, abs_neg]; exact he
  have hpyth : Real.sin (Φ θ) ^ 2 + Real.cos (Φ θ) ^ 2 = 1 := Real.sin_sq_add_cos_sq _
  have hδpyth : Real.sin δ ^ 2 + Real.cos δ ^ 2 = 1 := Real.sin_sq_add_cos_sq δ
  have hcos2 : Real.cos (Φ θ) ^ 2 < Real.sin δ ^ 2 := by
    have h1 : |Real.cos (Φ θ)| ^ 2 = Real.cos (Φ θ) ^ 2 := sq_abs _
    nlinarith [abs_nonneg (Real.cos (Φ θ)), Real.sin_nonneg_of_nonneg_of_le_pi hδ.le
      (by linarith)]
  have hsin2 : Real.cos δ ^ 2 < Real.sin (Φ θ) ^ 2 := by nlinarith
  have hcosδ0 : 0 < Real.cos δ := lt_of_lt_of_le (by positivity) hs2
  have habs : Real.cos δ < |Real.sin (Φ θ)| := by
    nlinarith [abs_nonneg (Real.sin (Φ θ)), sq_abs (Real.sin (Φ θ))]
  -- the crossing term dominates the error's slope
  have hbig : Ce < |Real.sin (Φ θ) * dΦ θ| := by
    rw [abs_mul, abs_of_pos hΦpos]
    have : Real.sqrt 2 / 2 * dΦ θ ≤ |Real.sin (Φ θ)| * dΦ θ :=
      mul_le_mul_of_nonneg_right (le_trans hs2 habs.le) hΦpos.le
    linarith
  intro hcon
  have : |Real.sin (Φ θ) * dΦ θ| = |de θ| := by
    have hEq : Real.sin (Φ θ) * dΦ θ = de θ := by linarith [hcon]
    rw [hEq]
  linarith [hde, hbig, this.symm ▸ hde]

/-- **Simplicity, carried across the decomposition.**  At a zero the two sides
differentiate to `τ^{M+1}P'(z)z'` and `2A·(-sinΦ·Φ' + e')`, because the
undifferentiated factors are exactly the two things that vanish there.  The right
side is nonzero by transversality, so `P'(z) ≠ 0`.

Stated over the *real* model `P` and the *real* identity, which is what makes the
`.re` transparent: `F_M` is real at a real point, so nothing is lost taking real
parts and nothing has to be recovered afterwards. -/
theorem derivative_eval_ne_zero_of_transversal {P : Polynomial ℝ}
    {τ z A Φ e dΦ de : ℝ → ℝ} {τ' z' A' : ℝ} {M : ℕ} {θ : ℝ}
    (hid : (fun s => τ s ^ (M + 1) * P.eval (z s))
      =ᶠ[nhds θ] fun s => 2 * A s * (Real.cos (Φ s) + e s))
    (hτ : HasDerivAt τ τ' θ) (hτ0 : 0 < τ θ)
    (hz : HasDerivAt z z' θ) (hz0 : z' ≠ 0)
    (hA : HasDerivAt A A' θ) (hA0 : 0 < A θ)
    (hΦ : HasDerivAt Φ (dΦ θ) θ) (hedv : HasDerivAt e (de θ) θ)
    (hPz : P.eval (z θ) = 0) (hzero : Real.cos (Φ θ) + e θ = 0)
    (hcross : -Real.sin (Φ θ) * dΦ θ + de θ ≠ 0) :
    (Polynomial.derivative P).eval (z θ) ≠ 0 := by
  -- the left side, with the vanishing factor killing the prefactor's term
  have hPc : HasDerivAt (fun s => P.eval (z s))
      ((Polynomial.derivative P).eval (z θ) * z') θ := (P.hasDerivAt (z θ)).comp θ hz
  have hL : HasDerivAt (fun s => τ s ^ (M + 1) * P.eval (z s))
      (τ θ ^ (M + 1) * ((Polynomial.derivative P).eval (z θ) * z')) θ := by
    have h := (hτ.pow (M + 1)).mul hPc
    rwa [hPz, mul_zero, zero_add] at h
  -- the right side, with the vanishing bracket killing `A'`
  have hcos : HasDerivAt (fun s => Real.cos (Φ s)) (-Real.sin (Φ θ) * dΦ θ) θ := hΦ.cos
  have hR : HasDerivAt (fun s => 2 * A s * (Real.cos (Φ s) + e s))
      (2 * A θ * (-Real.sin (Φ θ) * dΦ θ + de θ)) θ := by
    have h := (hA.const_mul 2).mul (hcos.add hedv)
    simp only [Pi.add_apply] at h
    rwa [hzero, mul_zero, zero_add] at h
  -- the identity transports the derivative, and uniqueness equates the two
  have hL' : HasDerivAt (fun s => 2 * A s * (Real.cos (Φ s) + e s))
      (τ θ ^ (M + 1) * ((Polynomial.derivative P).eval (z θ) * z')) θ :=
    hL.congr_of_eventuallyEq hid.symm
  have heq : τ θ ^ (M + 1) * ((Polynomial.derivative P).eval (z θ) * z')
      = 2 * A θ * (-Real.sin (Φ θ) * dΦ θ + de θ) := hL'.unique hR
  intro hcon
  rw [hcon, zero_mul, mul_zero] at heq
  exact mul_ne_zero (by positivity) hcross heq.symm

/-- A real polynomial's complexification, evaluated at a real point, is the
real value coerced.  Factored out because both the value and the derivative
transfer through it. -/
theorem eval_map_ofReal {P : Polynomial ℝ} {x : ℝ} :
    (P.map (algebraMap ℝ ℂ)).eval ((x : ℝ) : ℂ) = ((P.eval x : ℝ) : ℂ) := by
  rw [Polynomial.eval_map]
  simpa using Polynomial.eval₂_at_apply (algebraMap ℝ ℂ) x

/-- The normalized coefficient is real at a real parameter, so its real part is
the real model's value outright.  This is what makes the identity
`derivative_eval_ne_zero_of_transversal` differentiates a *real* one. -/
theorem re_scaled_coeff_eq {P : Polynomial ℝ} {t x : ℝ} {M : ℕ} :
    ((((t : ℝ) : ℂ)) ^ (M + 1) * (P.map (algebraMap ℝ ℂ)).eval ((x : ℝ) : ℂ)).re
      = t ^ (M + 1) * P.eval x := by
  rw [eval_map_ofReal, ← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]

/-! ### Every zero sits in a quantization window

`exists_two_consecutive_phase_zeros_isolated` shows there is no zero *between*
the pair it produces.  The enumeration `prop:local-strong-clock` asserts —
"the indices `k` running consecutively" — needs the complementary fact: an
**arbitrary** zero of `cosΦ + e` lies in one of the windows, so the zeros are
indexed by the quantization points and by nothing else.

It is the same estimate as the isolation, read without a pair in hand: a zero
forces `|sinΦ|`-distance below `sinδ`, and that confines the phase to a
`δ`-neighbourhood of a half-integer multiple of `π`. -/

/-- **`|sin y| < sinδ` confines `y` to a `δ`-neighbourhood of `πℤ`.**  Through
`round`, which is what makes the index an integer rather than an existential
with no arithmetic. -/
theorem exists_int_near_of_abs_sin_lt {y δ : ℝ} (hδ : 0 < δ)
    (hδ2 : δ ≤ Real.pi / 2) (h : |Real.sin y| < Real.sin δ) :
    ∃ k : ℤ, |y - k * Real.pi| < δ := by
  have hπ := Real.pi_pos
  refine ⟨round (y / Real.pi), ?_⟩
  set k : ℤ := round (y / Real.pi) with hk
  set t : ℝ := y - k * Real.pi with ht
  have hfac : y - k * Real.pi = (y / Real.pi - k) * Real.pi := by field_simp
  have habs : |t| ≤ Real.pi / 2 := by
    have h1 : |y / Real.pi - k| ≤ 1 / 2 := abs_sub_round (y / Real.pi)
    rw [ht, hfac, abs_mul, abs_of_pos hπ]
    nlinarith [h1, abs_nonneg (y / Real.pi - k)]
  -- the sine is `π`-periodic up to sign, so the absolute values agree
  have hsin : |Real.sin y| = |Real.sin t| := by
    have hy : y = t + k * Real.pi := by rw [ht]; ring
    rw [hy, Real.sin_add_int_mul_pi, abs_mul, abs_zpow, abs_neg, abs_one,
      one_zpow, one_mul]
  -- `|sin t| = sin |t|` on `[-π/2, π/2]`, and there the sine is strictly monotone
  have hst : |Real.sin t| = Real.sin |t| := by
    rcases le_or_gt 0 t with hpos | hneg
    · have ht2 : t ≤ Real.pi / 2 := by rwa [abs_of_nonneg hpos] at habs
      rw [abs_of_nonneg hpos, abs_of_nonneg
        (Real.sin_nonneg_of_nonneg_of_le_pi hpos (by linarith))]
    · have ht2 : -t ≤ Real.pi / 2 := by rwa [abs_of_neg hneg] at habs
      have h1 : 0 ≤ Real.sin (-t) :=
        Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
      rw [Real.sin_neg] at h1
      rw [abs_of_neg hneg, Real.sin_neg, abs_of_nonpos (by linarith)]
  rw [hsin, hst] at h
  by_contra hcon
  push Not at hcon
  have hmem1 : δ ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := ⟨by linarith, hδ2⟩
  have hmem2 : |t| ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) :=
    ⟨by linarith [abs_nonneg t], habs⟩
  have := Real.strictMonoOn_sin.monotoneOn hmem1 hmem2 hcon
  linarith

/-- **Every zero of the phase equation lies in a quantization window.**  The
index is an integer, so the zeros are labelled by `ℤ` and the statement
"the indices `k` running consecutively" has something to run over. -/
theorem phase_zero_localized {Φ e : ℝ → ℝ} {u₀ δ θ : ℝ}
    (hδ : 0 < δ) (hδ2 : δ ≤ Real.pi / 2) (hcos : Real.cos u₀ = 0)
    (he : |e θ| < Real.sin δ) (hzero : Real.cos (Φ θ) + e θ = 0) :
    ∃ k : ℤ, |Φ θ - (u₀ + k * Real.pi)| < δ := by
  have hcosabs : |Real.cos (Φ θ)| < Real.sin δ := by
    have hEq : Real.cos (Φ θ) = -e θ := by linarith
    rw [hEq, abs_neg]; exact he
  have hshift : Real.cos (Φ θ) = Real.cos (u₀ + (Φ θ - u₀)) := by congr 1; ring
  rw [hshift, abs_cos_shift hcos] at hcosabs
  obtain ⟨k, hk⟩ := exists_int_near_of_abs_sin_lt hδ hδ2 hcosabs
  exact ⟨k, by rw [show Φ θ - (u₀ + k * Real.pi) = Φ θ - u₀ - k * Real.pi by ring]; exact hk⟩

/-- **Adjacent zeros carry consecutive indices.**  With `phase_zero_localized`
labelling every zero by an integer and `phase_zero_index_unique` making that
label well defined, this is the last clause of
`prop:local-strong-clock`'s "the indices `k` running consecutively".

**The window-fitting constraint is interior, so it costs no hypothesis.**
Uniqueness avoided it by letting the two zeros supply their own interval; this
half genuinely needs *existence*, hence `exists_unique_phase_zero`, hence a
window that fits.  But the intervening point `u_0 + (k+1)π` sits strictly
between two phases already in range, so applying that lemma on `[θ, θ']` rather
than on `[a, b]` makes `Φθ ≤ u - δ` and `u + δ ≤ Φθ'` consequences of
`2δ ≤ π` — which `δ ≤ π/4` already gives.  The zero it produces then lies
strictly between the two, contradicting adjacency. -/
theorem adjacent_phase_zeros_consecutive_index {Φ dΦ e de : ℝ → ℝ}
    {a b u₀ δ Ce : ℝ}
    (hδ : 0 < δ) (hδ4 : δ ≤ Real.pi / 4) (hcos : Real.cos u₀ = 0)
    (hmono : StrictMonoOn Φ (Set.Icc a b))
    (hΦd : ∀ θ ∈ Set.Icc a b, HasDerivAt Φ (dΦ θ) θ)
    (hed : ∀ θ ∈ Set.Icc a b, HasDerivAt e (de θ) θ)
    (hΦpos : ∀ θ ∈ Set.Icc a b, 0 < dΦ θ)
    (hde : ∀ θ ∈ Set.Icc a b, |de θ| ≤ Ce)
    (hCe : ∀ θ ∈ Set.Icc a b, Ce < Real.sqrt 2 / 2 * dΦ θ)
    (he : ∀ θ ∈ Set.Icc a b, |e θ| < Real.sin δ)
    {θ θ' : ℝ} {k k' : ℤ}
    (hθ : θ ∈ Set.Icc a b) (hθ' : θ' ∈ Set.Icc a b) (hlt : θ < θ')
    (hz : Real.cos (Φ θ) + e θ = 0) (hz' : Real.cos (Φ θ') + e θ' = 0)
    (hk : |Φ θ - (u₀ + k * Real.pi)| < δ)
    (hk' : |Φ θ' - (u₀ + k' * Real.pi)| < δ)
    (hadj : ∀ s ∈ Set.Icc a b, θ < s → s < θ' → Real.cos (Φ s) + e s ≠ 0) :
    k' = k + 1 := by
  have hπ := Real.pi_pos
  have hcosk : ∀ j : ℤ, Real.cos (u₀ + j * Real.pi) = 0 := by
    intro j; rw [Real.cos_add_int_mul_pi, hcos, mul_zero]
  have hkb := abs_lt.1 hk
  have hk'b := abs_lt.1 hk'
  have hΦlt : Φ θ < Φ θ' := hmono hθ hθ' hlt
  -- `k ≤ k'` from the two windows and `2δ ≤ π`
  have hle : k ≤ k' := by
    by_contra hcon
    push Not at hcon
    have h1 : (k' : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast hcon
    nlinarith [hkb.1, hk'b.2, hΦlt, hπ, hδ4]
  -- `k ≠ k'` because the index is unique
  have hne : k ≠ k' := by
    intro hEq
    exact absurd (phase_zero_index_unique hδ hδ4 hcos hmono hΦd hed hΦpos hde hCe
      (hcosk k) hθ hθ' hz hz' hk (hEq ▸ hk')) (ne_of_lt hlt)
  -- so `k + 1 ≤ k'`; adjacency forbids `k + 2 ≤ k'`
  have hlt' : k + 1 ≤ k' := by omega
  by_contra hcon
  have hge : k + 2 ≤ k' := by omega
  set u : ℝ := u₀ + ((k : ℝ) + 1) * Real.pi with hu
  have hkr : ((k : ℝ)) + 2 ≤ (k' : ℝ) := by exact_mod_cast hge
  have hfitlo : Φ θ ≤ u - δ := by rw [hu]; nlinarith [hkb.2, hδ4, hπ]
  have hfithi : u + δ ≤ Φ θ' := by rw [hu]; nlinarith [hk'b.1, hkr, hδ4, hπ]
  have hsub : Set.Icc θ θ' ⊆ Set.Icc a b := Set.Icc_subset_Icc hθ.1 hθ'.2
  have hucos : Real.cos u = 0 := by
    rw [hu, show ((k : ℝ) + 1) = ((k + 1 : ℤ) : ℝ) by push_cast; ring]
    exact hcosk (k + 1)
  obtain ⟨lo, hlo, hi, hhi, hlolt, hΦlo, hΦhi, ξ, hξ, hzξ, -⟩ :=
    exists_unique_phase_zero hlt.le hucos hδ hδ4 (hmono.mono hsub)
      (fun s hs => hΦd s (hsub hs)) (fun s hs => hed s (hsub hs))
      (fun s hs => hΦpos s (hsub hs)) (fun s hs => hde s (hsub hs))
      (fun s hs => hCe s (hsub hs)) (fun s hs => he s (hsub hs)) hfitlo hfithi
  have hξmem : ξ ∈ Set.Icc θ θ' :=
    Set.Icc_subset_Icc hlo.1 hhi.2 ⟨hξ.1.le, hξ.2.le⟩
  -- `ξ` is strictly inside, so adjacency is contradicted
  have hΦξlo : Φ lo < Φ ξ :=
    (hmono.mono hsub) ⟨hlo.1, le_trans hlolt.le hhi.2⟩ hξmem hξ.1
  have hΦξhi : Φ ξ < Φ hi :=
    (hmono.mono hsub) hξmem ⟨le_trans hlo.1 hlolt.le, hhi.2⟩ hξ.2
  rw [hΦlo] at hΦξlo
  rw [hΦhi] at hΦξhi
  have hgt : θ < ξ := by
    by_contra hc
    push Not at hc
    have := (hmono.mono hsub) hξmem ⟨le_rfl, hlt.le⟩ (lt_of_le_of_ne hc ?_)
    · linarith
    · rintro rfl; linarith
  have hltξ : ξ < θ' := by
    by_contra hc
    push Not at hc
    have := (hmono.mono hsub) ⟨hlt.le, le_rfl⟩ hξmem (lt_of_le_of_ne hc ?_)
    · linarith
    · rintro rfl; linarith
  exact hadj ξ (hsub hξmem) hgt hltξ hzξ

/-! ### The quantization points are dense enough to be hit

Every clause of `prop:local-strong-clock` sits under "for a quantization point
`u_0` placed so that the window fits".  That is a hypothesis, and a hypothesis
nothing exhibits leaves the whole statement vacuous — the two window conditions
pin `u_0` to an interval which is **empty** at small `M`, since `Φ_M` has not yet
turned far enough.

The fix is arithmetic, not analytic: the zeros of the cosine are `π` apart, so
any interval of length `π` contains one. -/

/-- **An interval of length `π` contains a zero of the cosine.**  Through
`Int.ceil`, so the point is exhibited rather than merely shown to exist. -/
theorem exists_quantization_point_in_interval {A B : ℝ} (h : A + Real.pi ≤ B) :
    ∃ u : ℝ, Real.cos u = 0 ∧ A ≤ u ∧ u ≤ B := by
  have hπ := Real.pi_pos
  set k : ℤ := ⌈(A - Real.pi / 2) / Real.pi⌉ with hk
  refine ⟨Real.pi / 2 + (k : ℝ) * Real.pi, ?_, ?_, ?_⟩
  · rw [Real.cos_add_int_mul_pi, Real.cos_pi_div_two, mul_zero]
  · have h1 : (A - Real.pi / 2) / Real.pi ≤ (k : ℝ) := Int.le_ceil _
    rw [div_le_iff₀ hπ] at h1
    linarith
  · have h2 : (k : ℝ) < (A - Real.pi / 2) / Real.pi + 1 := Int.ceil_lt_add_one _
    have h3 : (k : ℝ) * Real.pi < ((A - Real.pi / 2) / Real.pi + 1) * Real.pi :=
      mul_lt_mul_of_pos_right h2 hπ
    rw [add_mul, div_mul_cancel₀ _ hπ.ne', one_mul] at h3
    linarith

end ForgacsTran
