/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import ForgacsTran.ConsequencesComposition.PhaseQuantization
import ForgacsTran.ConsequencesComposition.ClockSpacing
import ForgacsTran.ConsequencesComposition.AngularSupply

/-!
# `sec:consequences` on the proven count

`Consequences` states the three results of `sec:consequences` against the angular
discrepancy as a numeric hypothesis, because at the time nothing proved it.  The
count is proven now — `PhaseCount.exists_interiorZeros_of_dominance` builds the
zeros and `PhaseCount.count_add_card_le_natDegree` bounds them against the degree
— so this module supplies that hypothesis instead of assuming it.

## Main statements

* `count_lower_of_phase_turning` — the count in an angular window, in the shape
  `eq:angular-discrepancy` needs: `Φ` turns by at least
  `(M+1)(β-α) - V` across the window, so the window carries at least
  `(M+1)(β-α)/π - V/π - 2` distinct zeros.
* `angular_discrepancy_of_counts` — **`eq:angular-discrepancy`**, both sides: the
  lower bound on the window is one half, and the same bound on the two
  complementary windows together with the degree comparison is the other.
* `equidistribution_of_counts` — **`eq:normalized-angular-discrepancy`**, that
  fed to `Consequences.equidistribution_of_angular_discrepancy`.
* `angular_clock_of_bracketing` — **`eq:angular-clock`**,
  `Consequences.angular_rigidity` and `Consequences.angular_clock` composed on
  the same input.

* `ftWindow`, `ftWindow_subset`, `notMem_ftWindow` — the `z`-image of an angular
  window as a set of complex numbers, `eq:angular-subinterval`, and the
  disjointness the upper half of `eq:angular-discrepancy` needs: `z` is injective
  on the angular interval, so the complementary windows cannot re-count the zeros
  the inner one already carries.
* `natDegree_le_angular_measure` — `lem:eventual-degree`'s `⌊ M/r⌋`
  against the total angular measure `(M+1)/r`, so the rounding costs nothing.
* `ft_angular_discrepancy` — **`eq:angular-discrepancy` for the roots of `F_M`**,
  the inner count with multiplicity and the outer one over the two complementary
  windows, compared against the degree by
  `PhaseCount.count_add_card_le_natDegree`.
* `ft_equidistribution` — **`prop:equidistribution`**, that normalized by
  `deg F_M`.
* `ft_angular_clock`, `ft_angular_clock_numeratorUniform` —
  **`cor:angular-rigidity`** for the roots of `F_M`, with the defect printed in
  the `E_0 + E_1deg B_N` shape of `PhaseVariation.NumeratorUniform`.
* `local_clock_rate` — the `O_{Q,r,B,𝒥(M^{-3})` of
  `eq:local-strong-clock`, with the constant exhibited.
* `ft_clock_correction` — `eq:numerator-clock-correction` at `ftAmp`.

* the `C^1` input — a separating circle that is zero-free across the closed
  window, and `z` and `τ` differentiable on the subarc.  These are what
  `PoleExpansion.hasDerivAt_ftContourRem` and
  `exists_tau_slope_bound_on_subarc` consume.
* the `C^2` regularity — `W` twice differentiable along the branch with
  `Im(W''/W - (W'/W)^2)` continuous, which is what
  `exists_phase_second_derivative_bound` consumes.  Note this is *weaker* than
  the manuscript spends here: the paper routes through real-analyticity of `W`
  to obtain a bounded `ψ''`, and only the bounded `ψ''` is used.

## Implementation notes

The three above are stated over abstract reals, which is the right intermediate:
what makes them statements about `F_M` rather than about arbitrary counts is the
second half of this module.

**`prop:local-strong-clock`: what it needed, and where that now stands.**

*The set was never the obstruction.*  `𝒥` is a compact interval inside
one component of the complement of the amplitude zeros, and the retained range of
`eq:dominance-bound` moves with `M`; those are different sets.  But the bound the
strong clock consumes does not come from the retained range.
`DominanceFTSupply.interior_remainder_uniform` holds on a **fixed compact interval**
with no window condition at all, and on a compact zero-free subarc the amplitude
floor is compactness of `|W|`, not `eq:amplitude-deletion`.  The deleted windows
exist to handle the *zeros* of the amplitude; a subarc chosen to avoid them needs
none.

*The order was the obstruction, and it is now proved.*
`Consequences.exists_c1_interior_remainder_bound` takes a `C^0` bound and a `C^1`
bound.  The `C^0` half was already available in the shape it wants; the `C^1`
half — a bound on `∂_θ(τ^{M+1}F_M(z(θ)))` with no factor of
`M` beyond the explicit `(M+1)` — was proved nowhere in this tree.  The paper
does prove it, through holomorphy of `E_M` in `z` and Cauchy's estimate on a
fixed disk; what was missing was any Lean statement of it.
`PoleExpansion.hasDerivAt_ftContourRem` and
`PoleExpansion.norm_smul_ftContourRemDeriv_le` supply it: the spectral parameter
enters the pencil linearly, so the second-order expansion of `D_w^{-1}` is an
exact identity with a quadratic tail, and integrating it over the separating
circle gives both the derivative and its bound.  The constant is
`τ_{max}ZC_Γ R^r/m^2` and the ratio is the same `σ = τ/R` the
`C^0` half carries — `M` appears in neither.

What remains between that and `eq:local-strong-clock` is assembly, not a missing
statement: `exists_unique_zero_near_phase_point` gives the simple zero and the
quantization, `local_clock_spacing` the spacing, `local_clock_rate` its `M^{-3}`
rate, and `ft_clock_correction` the `ψ'` split.

**What the `prop:local-strong-clock` chain rests on, and what it does not.**

Two hypotheses on the branch supplier, both stated where the branch enters
rather than scattered through the composition, and neither a missing
construction:

Recording them as supplier hypotheses matters.  A reader scanning for gaps will
otherwise write them down as unformalized statements, and they are not: each is
an ordinary regularity assumption that whoever constructs the Forgács--Tran
branch discharges, in the same place the existing first-order phase bound
already puts its own requirement.

**Not claimed.**  The indexed family `θ_{k,M}` over all `k` — that the
zeros of `F_M` in `z(𝒥)` are *exactly* `\{θ_{k,M}\}` for `k` in a
range — is a strictly stronger statement than the consecutive pairs
`exists_two_consecutive_phase_zeros` supplies, and it is what the spacing law
consumes.  The two are not the same and are not conflated here.

Sorry-free.

## References

Formalizes `../shields-2026-forgacs-tran-numerators.tex`, «Global and local zero
laws» (`sec:consequences`, `subsec:zero-bulk`, `prop:equidistribution`,
`cor:angular-rigidity`), composed onto `prop:angular-discrepancy` as
`PhaseCount` proves it.

## Tags

zero distribution, clock spacing, composition, phase count

## Implementation notes

This module is a re-export.  At 1,665 lines it sat over Mathlib's 1,500-line cap, so
it is cut in two at the point the argument turns from the window to the spacing law:

* `ConsequencesComposition.PhaseQuantization` — the counting inequalities, the angular
  window, and `eq:local-phase-quantization` on it.
* `ConsequencesComposition.ClockSpacing` — the two `ψ` estimates, the composed
  `eq:local-strong-clock`, and its transport back to `F_M`.

The cut is at 1242 rather than at the nearer section boundary because the private
`sigma_sq` is consumed as far down as the quantitative half of the quantization, and a
private declaration is file-scoped.  Importing `ForgacsTran.ConsequencesComposition`
still brings in both halves.
-/
