/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib
import ForgacsTran.Amplitude

/-!
# `eq:phase-derivative-bound` does not move with the collar

`eq:retained-range` is `[h/M, π/r - h/M]`, which shrinks as `M` grows, so a
bound on `|ψ'|` obtained by compactness *on the retained range* is a `κ_M` and
`κ_M < M+1` is then a growth claim rather than a threshold on `M`.  Nothing in
the counting argument would notice; the composition would.

It is not a real obstruction, and this module says why in one lemma.  `ψ'` is
`Im(W'/W)`, and every place `W` degenerates along the arc it degenerates through
a **real** factor: `(θ-θ_j)^{ν_j}` at an amplitude zero (`eq:W-local-zero`) and
`δ^p` at either endpoint (`eq:W-endpoint-form`), with `δ` the real angular
distance.  A real factor contributes `ρ'/ρ ∈ ℝ` to the logarithmic derivative
and therefore **nothing at all** to its imaginary part.  So `|ψ'|` is bounded by
the cofactor's contribution alone, which is continuous across the degeneracy,
and one compactness argument on the *closed* arc serves every `M`.

`Amplitude.exists_phase_derivative_bound` is this for the amplitude zeros, at a
natural-number exponent.  What follows generalizes it to an arbitrary real
factor, which covers the endpoints too — where the exponent `p` of
`eq:W-endpoint-form` is an integer and may be negative, so the natural-number
form does not reach them.

## Main statements

* `im_logDeriv_real_factor` — a real factor drops out of `Im(W'/W)`.
* `exists_phase_deriv_bound_real_factor` — hence `|ψ'|` is bounded on a compact
  arc by the cofactor alone, the degeneracy notwithstanding.
* `exists_phase_deriv_bound_zpow` — the endpoint instance, `W = δ^p V(δ)` with
  `p : ℤ`.
* `phase_deriv_bound_uniform_in_collar` — the consequence
  `AngularDiscrepancyFT.FTPhaseSupply` consumes: **one** `κ`, chosen on the
  closed arc, bounds `|ψ'|` across `[h/M, b]` for *every* `M` at once.

## Implementation notes

The side condition is `ρ θ ≠ 0` rather than `θ ≠ θ₀`, because at an endpoint
with `p < 0` the factor is not merely zero but undefined; asking only that it be
nonzero where the identity is used costs nothing and reaches both cases.  The
bound itself is taken over the closed arc, including the degenerate point, since
the cofactor is continuous there — that asymmetry is the whole mechanism.

Sorry-free.

## References

Formalizes `../shields-2026-forgacs-tran-numerators.tex`, «Spectral geometry,
residues, and the principal amplitude» (`sec:geometry`, `lem:amplitude-divisor`,
`eq:W-local-zero`, `eq:W-endpoint-form`, `eq:phase-derivative-bound`), in the
form «Angular discrepancy and proof of the main theorem» (`subsec:proof`,
`eq:retained-range`) consumes it.

## Tags

phase derivative, amplitude divisor, endpoint form, uniformity
-/

namespace ForgacsTran

open Set Complex

/-- **A real factor is invisible to the phase.**  If `W = ρ·U` with `ρ`
real-valued and nonzero, then `Im(W'/W) = Im(U'/U)`: the factor contributes
`ρ'/ρ`, which is real.

This is `eq:W-local-zero` and `eq:W-endpoint-form` at once — both write `W` as a
real power of a real quantity times an analytic nonvanishing cofactor, and it is
the *realness*, not the exponent, that does the work. -/
theorem im_logDeriv_real_factor {ρ : ℝ → ℝ} {U : ℝ → ℂ} {ρ' : ℝ} {U' : ℂ} {θ : ℝ}
    (hρ : HasDerivAt ρ ρ' θ) (hU : HasDerivAt U U' θ)
    (hρ0 : ρ θ ≠ 0) (hU0 : U θ ≠ 0) :
    (deriv (fun s : ℝ => ((ρ s : ℝ) : ℂ) * U s) θ / (((ρ θ : ℝ) : ℂ) * U θ)).im
      = (U' / U θ).im := by
  have hρc : HasDerivAt (fun s : ℝ => ((ρ s : ℝ) : ℂ) ) ((ρ' : ℝ) : ℂ) θ := hρ.ofReal_comp
  have hW : HasDerivAt (fun s : ℝ => ((ρ s : ℝ) : ℂ) * U s)
      (((ρ' : ℝ) : ℂ) * U θ + ((ρ θ : ℝ) : ℂ) * U') θ := hρc.mul hU
  have hρ0' : ((ρ θ : ℝ) : ℂ) ≠ 0 := by
    simpa using hρ0
  rw [hW.deriv]
  have hsplit : (((ρ' : ℝ) : ℂ) * U θ + ((ρ θ : ℝ) : ℂ) * U') / (((ρ θ : ℝ) : ℂ) * U θ)
      = ((ρ' / ρ θ : ℝ) : ℂ) + U' / U θ := by
    push_cast
    field_simp
  rw [hsplit, Complex.add_im, Complex.ofReal_im, zero_add]

/-- **`eq:phase-derivative-bound` across a real degeneracy.**  The bound is taken
over the *closed* arc — the degenerate point included — because the cofactor is
continuous there; the identity is used only where the real factor is nonzero.

`Amplitude.exists_phase_derivative_bound` is the case `ρ θ = (θ-θ₀)^ν`. -/
theorem exists_phase_deriv_bound_of_bound {ρ dρ : ℝ → ℝ} {U dU : ℝ → ℂ} {a b κ₀ : ℝ}
    (hρ : ∀ θ ∈ Icc a b, ρ θ ≠ 0 → HasDerivAt ρ (dρ θ) θ)
    (hU : ∀ θ ∈ Icc a b, ρ θ ≠ 0 → HasDerivAt U (dU θ) θ)
    (hbd : ∀ θ ∈ Icc a b, ρ θ ≠ 0 → |(dU θ / U θ).im| ≤ κ₀)
    (hU0 : ∀ θ ∈ Icc a b, ρ θ ≠ 0 → U θ ≠ 0) :
    ∃ κ : ℝ, 0 ≤ κ ∧ ∀ θ ∈ Icc a b, ρ θ ≠ 0 →
      |(deriv (fun s : ℝ => ((ρ s : ℝ) : ℂ) * U s) θ
          / (((ρ θ : ℝ) : ℂ) * U θ)).im| ≤ κ := by
  refine ⟨max κ₀ 0, le_max_right _ _, fun θ hθ hρ0 => ?_⟩
  rw [im_logDeriv_real_factor (hρ θ hθ hρ0) (hU θ hθ hρ0) hρ0 (hU0 θ hθ hρ0)]
  exact le_trans (hbd θ hθ hρ0) (le_max_left _ _)

/-- The same with the bound produced by compactness rather than supplied.  This
is the convenient form where `Im(dU/U)` extends continuously to the degenerate
point; `exists_phase_deriv_bound_of_bound` is the one to use where it does not,
or where the limit is not known to exist. -/
theorem exists_phase_deriv_bound_real_factor {ρ dρ : ℝ → ℝ} {U dU : ℝ → ℂ} {a b : ℝ}
    (hρ : ∀ θ ∈ Icc a b, ρ θ ≠ 0 → HasDerivAt ρ (dρ θ) θ)
    (hU : ∀ θ ∈ Icc a b, ρ θ ≠ 0 → HasDerivAt U (dU θ) θ)
    (hcont : ContinuousOn (fun θ => (dU θ / U θ).im) (Icc a b))
    (hU0 : ∀ θ ∈ Icc a b, ρ θ ≠ 0 → U θ ≠ 0) :
    ∃ κ : ℝ, 0 ≤ κ ∧ ∀ θ ∈ Icc a b, ρ θ ≠ 0 →
      |(deriv (fun s : ℝ => ((ρ s : ℝ) : ℂ) * U s) θ
          / (((ρ θ : ℝ) : ℂ) * U θ)).im| ≤ κ := by
  obtain ⟨κ₀, hκ₀⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  exact exists_phase_deriv_bound_of_bound hρ hU
    (fun θ hθ _ => by simpa [Real.norm_eq_abs] using hκ₀ θ hθ) hU0

/-- **`eq:W-endpoint-form`.**  At an endpoint `W = δ^p V(δ)` with `p ∈ ℤ`,
possibly negative, so the natural-number form does not reach it.  The real
factor `δ^p` still drops out, and `|ψ'|` is bounded on `(0,b]` by a constant
taken over the closed `[0,b]`. -/
theorem exists_phase_deriv_bound_zpow {U dU : ℝ → ℂ} {b : ℝ} (p : ℤ)
    (hU : ∀ θ ∈ Icc (0 : ℝ) b, θ ^ p ≠ 0 → HasDerivAt U (dU θ) θ)
    (hcont : ContinuousOn (fun θ => (dU θ / U θ).im) (Icc (0 : ℝ) b))
    (hU0 : ∀ θ ∈ Icc (0 : ℝ) b, θ ^ p ≠ 0 → U θ ≠ 0) :
    ∃ κ : ℝ, 0 ≤ κ ∧ ∀ θ ∈ Icc (0 : ℝ) b, θ ≠ 0 →
      |(deriv (fun s : ℝ => ((s ^ p : ℝ) : ℂ) * U s) θ
          / (((θ ^ p : ℝ) : ℂ) * U θ)).im| ≤ κ := by
  obtain ⟨κ, hκ0, hκ⟩ := exists_phase_deriv_bound_real_factor
    (ρ := fun s : ℝ => s ^ p) (dρ := fun s : ℝ => (p : ℝ) * s ^ (p - 1))
    (U := U) (dU := dU) (a := 0) (b := b)
    (fun θ hθ h0 => by
      rcases lt_or_ge p 0 with hp | hp
      · have h0' : θ ^ p ≠ 0 := h0
        exact hasDerivAt_zpow p θ
          (Or.inl fun hz => h0' (by rw [hz]; exact zero_zpow p (ne_of_lt hp)))
      · exact hasDerivAt_zpow p θ (Or.inr hp))
    hU hcont hU0
  exact ⟨κ, hκ0, fun θ hθ hθ0 => hκ θ hθ (zpow_ne_zero _ hθ0)⟩

/-- **The bound does not move with the collar.**  One `κ`, chosen once on the
closed arc, bounds `|ψ'| = |Im(W'/W)|` on `[h/M, b]` for **every** `M` — which is
what `AngularDiscrepancyFT.FTPhaseSupply`'s `|dψ| < M+1` clause needs, and the
reason that clause is a threshold on `M` rather than a growth claim about a
`κ_M`.

The content is entirely in `exists_phase_deriv_bound_real_factor` taking its
bound over the *closed* arc: `[h/M, b] ⊆ [0, b]` for every `M`, so nothing is
re-derived per index. -/
theorem phase_deriv_bound_uniform_in_collar {ρ dρ : ℝ → ℝ} {U dU : ℝ → ℂ} {b h : ℝ}
    (hh : 0 ≤ h)
    (hρ : ∀ θ ∈ Icc (0 : ℝ) b, ρ θ ≠ 0 → HasDerivAt ρ (dρ θ) θ)
    (hU : ∀ θ ∈ Icc (0 : ℝ) b, ρ θ ≠ 0 → HasDerivAt U (dU θ) θ)
    (hcont : ContinuousOn (fun θ => (dU θ / U θ).im) (Icc (0 : ℝ) b))
    (hU0 : ∀ θ ∈ Icc (0 : ℝ) b, ρ θ ≠ 0 → U θ ≠ 0) :
    ∃ κ : ℝ, 0 ≤ κ ∧ ∀ M : ℕ, ∀ θ ∈ Icc (h / M) b, ρ θ ≠ 0 →
      |(deriv (fun s : ℝ => ((ρ s : ℝ) : ℂ) * U s) θ
          / (((ρ θ : ℝ) : ℂ) * U θ)).im| ≤ κ := by
  obtain ⟨κ, hκ0, hκ⟩ := exists_phase_deriv_bound_real_factor hρ hU hcont hU0
  refine ⟨κ, hκ0, fun M θ hθ hρ0 => hκ θ ⟨?_, hθ.2⟩ hρ0⟩
  exact le_trans (by positivity) hθ.1

/-- **The collar bound off an explicit estimate.**  `phase_deriv_bound_uniform_in_collar`
gets its constant from compactness on the closed arc, which asks that
`Im(dU/U)` have a **limit** at the degenerate point.  This asks only for a
**bound** on the set where `ρ` does not vanish — no limit, and nothing about the
endpoint at all.

The distinction is not cosmetic at the Forgács–Tran branch.  Writing
`γ - t_a = θ·u(θ)`, the surviving term of `Im(W'/W)` is `-m·Im(u'/u)`, and `u'`
is second order in `γ`; so the *limit* is not determined by `γ'(0)` and the
pencil, and reaching it needs one-sided `C²` regularity the endpoint package does
not have.  A *bound* on `u'/u` over `(0,b]` follows from `γ'` merely Lipschitz.
Whether that is reachable is a question about the endpoint package, not about
this lemma; what this lemma settles is that a bound is all it would have to
supply. -/
theorem phase_deriv_bound_uniform_in_collar_of_bound {ρ dρ : ℝ → ℝ} {U dU : ℝ → ℂ}
    {b h κ₀ : ℝ} (hh : 0 ≤ h)
    (hρ : ∀ θ ∈ Icc (0 : ℝ) b, ρ θ ≠ 0 → HasDerivAt ρ (dρ θ) θ)
    (hU : ∀ θ ∈ Icc (0 : ℝ) b, ρ θ ≠ 0 → HasDerivAt U (dU θ) θ)
    (hbd : ∀ θ ∈ Icc (0 : ℝ) b, ρ θ ≠ 0 → |(dU θ / U θ).im| ≤ κ₀)
    (hU0 : ∀ θ ∈ Icc (0 : ℝ) b, ρ θ ≠ 0 → U θ ≠ 0) :
    ∃ κ : ℝ, 0 ≤ κ ∧ ∀ M : ℕ, ∀ θ ∈ Icc (h / M) b, ρ θ ≠ 0 →
      |(deriv (fun s : ℝ => ((ρ s : ℝ) : ℂ) * U s) θ
          / (((ρ θ : ℝ) : ℂ) * U θ)).im| ≤ κ := by
  obtain ⟨κ, hκ0, hκ⟩ := exists_phase_deriv_bound_of_bound hρ hU hbd hU0
  refine ⟨κ, hκ0, fun M θ hθ hρ0 => hκ θ ⟨?_, hθ.2⟩ hρ0⟩
  exact le_trans (by positivity) hθ.1

end ForgacsTran
