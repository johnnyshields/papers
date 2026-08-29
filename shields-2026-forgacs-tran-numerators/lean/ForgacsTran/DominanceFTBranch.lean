/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import ForgacsTran.DominanceFTSupply

/-!
# `thm:weighted-dominance` on the branch, at any multiplicity

`DominanceFTSupply` discharges the supplies; this module states the theorem on
the Forgács--Tran branch itself, over four forms that differ only in which
interior datum the caller supplies and which the theorem builds.  The smallest
zero is left at arbitrary multiplicity throughout — the `ρ ≥ 2` specializations
the composition layer consumes are `DominanceFT`'s.

## Main statements

In increasing order of what the theorem does for its caller:

* `weighted_dominance_of_branch_any_multiplicity_at_of_threshold_of_data` — the
  interior antecedent is `hdata_entry_of_interior`'s **conclusion**, not the
  fixed-circle block that theorem consumes.  The distinction is not
  presentational: from `3 ≤ r` the fixed form is unsatisfiable, because a
  non-principal cluster member collapses into the origin at the upper endpoint
  while `sup τ` sits at the lower one and no single radius separates them.  This
  is the form a caller can meet at every `r`.
* `weighted_dominance_of_branch_any_multiplicity_at_of_threshold` — the same with
  the interior geometry supplied instead, and the threshold `h` still an input.
* `weighted_dominance_of_branch_any_multiplicity_at` — `eq:endpoint-linear-gap`
  extracted rather than assumed, so `ε` is produced before `Θ` is chosen and the
  deleted family may be built from that `ε`'s own `σ`.
* `weighted_dominance_of_branch_any_multiplicity` — **paper
  `thm:weighted-dominance`, on the cited branch and its modulus gap**, with `Θ`
  fixed first and the interior data demanded at every `e`.

## Implementation notes

**Where the binders are.**  They are declared in `variable` blocks rather than
written out per theorem, at three nested levels: all four share the pencil, the
branch and the lower endpoint's factorization, residue ratio, retained cluster
and contour bound; the two `_of_threshold` forms then share the upper-endpoint
block, the interior gap and the cluster sums; and the two extracted-gap forms
share the expansion group at both endpoints together with the upper-endpoint
block.  The nesting follows the split, because the expansion group precedes the
upper endpoint in the second pair and is absent in the first, so no single block
serves both.

Each theorem's type is unchanged by this — `variable` prepends in declaration
order, and `#check @` on all four is byte-identical over 383 lines to what it
was when the binders were written out four times.

**What each surviving hypothesis is.**  `eq:endpoint-linear-gap` and
`eq:lower-residue-ratio` are **not** among them.  The manuscript's proof of
`thm:FT-geometry` says Prop. 3 of `Forgacs2017RationalDenominator` supplies the
endpoint *expansion* and that "we extract the uniform separation asserted above",
so the gap is our step, not the cited one; and Forgács--Tran state nothing about
residue ratios at all.  Both are therefore derived here — the gap from the
expansion through `Geometry.endpoint_linear_coeff_pos` and
`Geometry.exists_endpoint_linear_gap`, the ratio from the leading behavior of `B`
and `∂_tD` through `Cluster.tendsto_residue_ratio_cluster`.

**Containment.**  What follows reads the shared `variable` block above, which is
what all four forms draw their hypotheses from.  The conclusion relates
`ftRemainder` to `ftPrincipalAmp`; no binder of that block mentions
`ftRemainder`, and none mentions `ftCoeffPoly`, which is the whole of
`ftRemainder`'s coefficient side.  The comparison is produced by
`DominanceFTSupply.weighted_dominance_ftCoeffPoly_at_of_threshold`, which is
where its content sits.  Exactly one binder mentions `ftPrincipalAmp` —
`hamp₁`, the upper endpoint's amplitude floor — and it names only that side; the
lower endpoint's floor is derived rather than assumed.  Two mention `ftAmp`:
`hinterior`, only to say which `θ` its zero set contains and that the deleted
windows avoid them, and `hratio₁`, only through a ratio of two of its values.
Neither relates the amplitude to the remainder.

**The endpoint binders are one-sided, and the two halves take different
domains.**  `hγd₀` is `HasDerivWithinAt … (Set.Ici 0) 0`; `hrootev₀` is
`∀ᶠ δ in 𝓝[>] 0`.  Not uniform, and deliberately so: the derivative needs the
endpoint *in* its domain, because `Amplitude.amplitude_endpoint_form` returns
`V`'s value and continuity **at** the endpoint; the eventual condition must
exclude it, because every conclusion downstream already does and including it
would smuggle in a condition `hk₀` supplies separately.

One-sided is the only form available.  `τ` sees `θ` only through `cos`, hence is
even, so the one-sided difference quotients at the endpoint are exact negatives —
both `∓1/√3`, differing by at least `1.135`, a corner rather than a derivative
(`scripts/check_endpoint_derivative_onesided.py`).  The manuscript agrees:
`lem:principal-endpoint-regularity` extends the branch to a regular arc on the
**closed** `[0, π/r]` with `δ` the angular *distance* to the endpoint, so `δ ≥ 0`
throughout and no two-sided statement is ever claimed.

Sorry-free.

## References

Formalizes `../shields-2026-forgacs-tran-numerators.tex`, «Principal-pair
dominance and the fixed-numerator theorem» (`sec:dominance`,
`subsec:weighted-dominance`, `thm:weighted-dominance`, `eq:retained-range`).

## Tags

weighted dominance, Forgacs-Tran branch, endpoint expansion
-/

namespace ForgacsTran

open Polynomial Complex

/-! ### `thm:weighted-dominance` on the branch alone -/

section BranchDominance

/-! The four theorems below are one statement at four levels of supply, and the
first 72 binders of each were identical: the pencil, the branch, the lower
endpoint's factorization, its residue ratio, its retained cluster and its
contour bound.  They are declared once here.  `variable` prepends them in
declaration order, so each theorem's type is unchanged -- which is what the
positional applications in `DominanceFT`, `RhoOneDominanceComposition`,
`SimpleWitness`, `WeightedDominanceBranch`, `WeightedDominanceBranchOne` and
`EndpointUpperOneBinders` check on every build, and `#print axioms` cannot. -/

variable {Q B : Polynomial ℂ}
    (hQ : HasRealCoeffs Q) (hB : HasRealCoeffs B) (hB0 : B ≠ 0)
    {r : ℕ} (hr : 1 ≤ r) (hQ0 : Q.eval 0 ≠ 0)
    {b : ℝ} {z τ : ℝ → ℝ}
    {Θ : ℕ → Set ℝ}
    {n₀ n₁ : ℕ} {g₀ : ℝ → Fin n₀ → ℂ} {g₁ : ℝ → Fin n₁ → ℂ}
    {sfun₀ sfun₁ : ℝ → Finset ℂ}
    {x₁ : ℝ} (hx₁ : 0 < x₁) {ρ : ℕ} (hρ : 0 < n₀ → 2 ≤ ρ)
    -- lower endpoint: the endpoint factorization
    {te₀ γe₀ : ℂ} (hte₀ : te₀ ≠ 0) (hγe₀ : γe₀ ≠ 0)
    (hγ0₀ : ftPrincipal τ 0 = te₀)
    (hγd₀ : HasDerivWithinAt (fun δ => ftPrincipal τ δ) γe₀ (Set.Ici 0) 0)
    (hk₀ : 1 ≤ (ftDen Q r ((z 0 : ℝ) : ℂ)).rootMultiplicity te₀)
    (hrootev₀ : ∀ᶠ δ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      (ftDen Q r ((z δ : ℝ) : ℂ)).eval (ftPrincipal τ δ) = 0)
    -- lower endpoint: the residue ratio
    -- `eq:lower-residue-ratio` is *not* assumed either: what is taken is the
    -- leading behavior of `B` and of `∂_tD` along each branch, which Taylor at
    -- `x_1` reads off Prop. 3's expansion; the ratio is `Cluster`'s theorem
    {idx₀ : Fin n₀ → ℕ} {jp₀ : ℕ} {νB₀ : ℕ} {cB₀ cQ₀ : ℂ}
    (hcB₀ : 0 < n₀ → cB₀ ≠ 0) (hcQ₀ : 0 < n₀ → cQ₀ ≠ 0)
    (hBj₀ : ∀ i : Fin n₀, Filter.Tendsto
      (fun δ : ℝ => B.eval (g₀ δ i) / ((δ : ℝ) : ℂ) ^ (νB₀ : ℤ))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (cB₀ * clusterAlpha x₁ ρ (idx₀ i) ^ νB₀)))
    (hBp₀ : 0 < n₀ → Filter.Tendsto
      (fun δ : ℝ => B.eval (ftPrincipal τ δ) / ((δ : ℝ) : ℂ) ^ (νB₀ : ℤ))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (cB₀ * clusterAlpha x₁ ρ jp₀ ^ νB₀)))
    (hEj₀ : ∀ i : Fin n₀, Filter.Tendsto
      (fun δ : ℝ => (derivative (ftDen Q r ((z δ : ℝ) : ℂ))).eval (g₀ δ i)
        / ((δ : ℝ) : ℂ) ^ ((ρ - 1 : ℕ) : ℤ))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (cQ₀ * clusterAlpha x₁ ρ (idx₀ i) ^ (ρ - 1))))
    (hEp₀ : 0 < n₀ → Filter.Tendsto
      (fun δ : ℝ => (derivative (ftDen Q r ((z δ : ℝ) : ℂ))).eval (ftPrincipal τ δ)
        / ((δ : ℝ) : ℂ) ^ ((ρ - 1 : ℕ) : ℤ))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (cQ₀ * clusterAlpha x₁ ρ jp₀ ^ (ρ - 1))))
    -- lower endpoint: the retained cluster and the contour bound
    {R₀ τmax₀ σ₀ e₀ : ℝ} (hR₀ : 0 < R₀) (hσ₀ : τmax₀ / R₀ ≤ σ₀) (hσ₀1 : σ₀ < 1)
    (he₀ : 0 < e₀)
    (hτpos₀ : ∀ δ : ℝ, 0 < δ → δ ≤ e₀ → 0 < τ δ)
    (hτle₀ : ∀ δ : ℝ, 0 < δ → δ ≤ e₀ → τ δ ≤ τmax₀)
    (hroot₀ : ∀ δ : ℝ, 0 < δ → δ ≤ e₀ → ∀ a ∈ sfun₀ δ,
      (ftDen Q r ((z δ : ℝ) : ℂ)).eval a = 0)
    (hsimple₀ : ∀ δ : ℝ, 0 < δ → δ ≤ e₀ → ∀ a ∈ sfun₀ δ,
      (derivative (ftDen Q r ((z δ : ℝ) : ℂ))).eval a ≠ 0)
    (haR₀ : ∀ δ : ℝ, 0 < δ → δ ≤ e₀ → ∀ a ∈ sfun₀ δ, ‖a‖ < R₀)
    (huniq₀ : ∀ δ : ℝ, 0 < δ → δ ≤ e₀ → ∀ t : ℂ, ‖t‖ ≤ R₀ →
      (ftDen Q r ((z δ : ℝ) : ℂ)).eval t = 0 → t ∈ sfun₀ δ)
    (hrootplus₀ : ∀ δ : ℝ, 0 < δ → δ ≤ e₀ →
      (ftDen Q r ((z δ : ℝ) : ℂ)).eval (ftPrincipal τ δ) = 0)
    (hne₀ : ∀ δ : ℝ, 0 < δ → δ ≤ e₀ →
      ftPrincipal τ δ ≠ ((τ δ : ℝ) : ℂ) * Complex.exp (-((δ : ℝ) : ℂ) * I))
    (hginj₀ : ∀ δ : ℝ, 0 < δ → δ ≤ e₀ → Function.Injective (g₀ δ))
    (hgmem₀ : ∀ δ : ℝ, 0 < δ → δ ≤ e₀ → ∀ i, g₀ δ i ∈
      ((sfun₀ δ).erase (ftPrincipal τ δ)).erase
        (((τ δ : ℝ) : ℂ) * Complex.exp (-((δ : ℝ) : ℂ) * I)))
    (hgcard₀ : ∀ δ : ℝ, 0 < δ → δ ≤ e₀ →
      (((sfun₀ δ).erase (ftPrincipal τ δ)).erase
        (((τ δ : ℝ) : ℂ) * Complex.exp (-((δ : ℝ) : ℂ) * I))).card = n₀)
    -- the separating circle, zero-free across the closed window, and the branch
    -- parameter continuous on it: `eq:contour-remainder-bound`'s constant is
    -- produced from these two by compactness, not assumed uniform
    -- the contour bound enters as the punctured statement the proof uses, not as
    -- the closed-window data one route happens to derive it from.  Taken here at
    -- the lower endpoint too, where the closed form IS meetable: a theorem whose
    -- two endpoints take different kinds of input is what lets an upper binder be
    -- built by symmetry with a lower one and come out false.
    {C₀ : ℝ} (hC₀ : 0 ≤ C₀)
    (hCbd₀ : ∀ δ : ℝ, 0 < δ → δ ≤ e₀ → ∀ t ∈ Metric.sphere (0 : ℂ) R₀,
      ‖B.eval t / (ftDen Q r ((z δ : ℝ) : ℂ)).eval t‖ ≤ C₀)

include hQ hB hB0 hr hQ0 hx₁ hρ hte₀ hγe₀ hγ0₀ hγd₀ hk₀ hrootev₀ hcB₀ hcQ₀ hBj₀ hBp₀ hEj₀ hEp₀
  hR₀ hσ₀ hσ₀1 he₀ hτpos₀ hτle₀ hroot₀ hsimple₀ haR₀ huniq₀ hrootplus₀ hne₀ hginj₀ hgmem₀
  hgcard₀ hC₀ hCbd₀

section SuppliedGeometryForms

/-! The two forms below are stated against the same upper-endpoint block, the
same interior gap and the same cluster sums; they differ in whether the
threshold `h` is an input.  Declared once. -/

variable
    -- upper endpoint: the same, through the chart `η ↦ b - η`
    -- the upper endpoint enters as the amplitude bound itself, not as a route to
    -- it: `weighted_dominance_ftCoeffPoly` already takes `p₁` abstractly, and the
    -- endpoint group's only use here was to obtain this.  Which route proves it
    -- depends on `r` — the finite one at `r = 1`, where `γ(0) ≠ 0`, and the origin
    -- one at `r ≥ 2`, where `FTBranchUpperRefutation` proves `γ(0) = 0`.
    {p₁ : ℕ} {A₁ : ℝ} (hA₁ : 0 < A₁)
    (hamp₁ : ∃ e > (0 : ℝ), ∀ η : ℝ, 0 < η → η ≤ e →
      A₁ * η ^ p₁ ≤ ftPrincipalAmp Q B r z τ (b - η))
    -- `eq:lower-residue-ratio` is *not* assumed either: what is taken is the
    -- leading behavior of `B` and of `∂_tD` along each branch, which Taylor at
    -- `x_1` reads off Prop. 3's expansion; the ratio is `Cluster`'s theorem
    -- `eq:upper-residue-ratio`.  At the upper endpoint the amplitude ratio is a
    -- ratio of NORMALIZED ROOTS, `W_j/W = ζ_j/ζ_+(1+O(τ))`, and its limit has
    -- modulus one because the `ζ` tend to the `r`th roots of `-1`.  This is NOT
    -- the lower endpoint's cluster ratio: `B(0) ≠ 0`, so `B` does not vanish on
    -- this cluster, and no `clusterAlpha`, no `ν_B` and no `ρ-1` enters.  The
    -- cluster is empty unless `r ≥ 2`, which the supplied gap carries.
    {L₁ : Fin n₁ → ℂ}
    (hL₁ : ∀ i : Fin n₁, ‖L₁ i‖ = 1)
    (hratio₁ : ∀ i : Fin n₁, Filter.Tendsto
      (fun δ : ℝ => ftAmp Q B r ((z (b - δ) : ℝ) : ℂ) (g₁ (b - δ) i)
        / ftAmp Q B r ((z (b - δ) : ℝ) : ℂ) (ftPrincipal τ (b - δ)))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (L₁ i)))
    {R₁ τmax₁ σ₁ e₁ : ℝ} (hR₁ : 0 < R₁) (hσ₁ : τmax₁ / R₁ ≤ σ₁) (hσ₁1 : σ₁ < 1)
    (he₁ : 0 < e₁)
    (hτpos₁ : ∀ δ : ℝ, 0 < δ → δ ≤ e₁ → 0 < τ (b - δ))
    (hτle₁ : ∀ δ : ℝ, 0 < δ → δ ≤ e₁ → τ (b - δ) ≤ τmax₁)
    (hroot₁ : ∀ δ : ℝ, 0 < δ → δ ≤ e₁ → ∀ a ∈ sfun₁ δ,
      (ftDen Q r ((z (b - δ) : ℝ) : ℂ)).eval a = 0)
    (hsimple₁ : ∀ δ : ℝ, 0 < δ → δ ≤ e₁ → ∀ a ∈ sfun₁ δ,
      (derivative (ftDen Q r ((z (b - δ) : ℝ) : ℂ))).eval a ≠ 0)
    (haR₁ : ∀ δ : ℝ, 0 < δ → δ ≤ e₁ → ∀ a ∈ sfun₁ δ, ‖a‖ < R₁)
    (huniq₁ : ∀ δ : ℝ, 0 < δ → δ ≤ e₁ → ∀ t : ℂ, ‖t‖ ≤ R₁ →
      (ftDen Q r ((z (b - δ) : ℝ) : ℂ)).eval t = 0 → t ∈ sfun₁ δ)
    (hrootplus₁ : ∀ δ : ℝ, 0 < δ → δ ≤ e₁ →
      (ftDen Q r ((z (b - δ) : ℝ) : ℂ)).eval (ftPrincipal τ (b - δ)) = 0)
    (hne₁ : ∀ δ : ℝ, 0 < δ → δ ≤ e₁ →
      ftPrincipal τ (b - δ) ≠ ((τ (b - δ) : ℝ) : ℂ) * Complex.exp (-((b - δ : ℝ) : ℂ) * I))
    (hginj₁ : ∀ δ : ℝ, 0 < δ → δ ≤ e₁ → Function.Injective (g₁ (b - δ)))
    (hgmem₁ : ∀ δ : ℝ, 0 < δ → δ ≤ e₁ → ∀ i, g₁ (b - δ) i ∈
      ((sfun₁ δ).erase (ftPrincipal τ (b - δ))).erase
        (((τ (b - δ) : ℝ) : ℂ) * Complex.exp (-((b - δ : ℝ) : ℂ) * I)))
    (hgcard₁ : ∀ δ : ℝ, 0 < δ → δ ≤ e₁ →
      (((sfun₁ δ).erase (ftPrincipal τ (b - δ))).erase
        (((τ (b - δ) : ℝ) : ℂ) * Complex.exp (-((b - δ : ℝ) : ℂ) * I))).card = n₁)
    -- the contour bound enters as the punctured statement the proof uses.  The
    -- closed-window form is not merely stronger than needed here: at `r ≥ 2` it is
    -- unmeetable, because `z` is unbounded as `δ → 0` and a continuous function on
    -- a compact set is bounded; and at the one pencil where it IS discharged, it
    -- passes without probing the endpoint at all — at `δ = 0` the junk value of `z`
    -- leaves `Q` alone, whose zero misses the sphere, so it holds by Lean's
    -- division-by-zero convention rather than by the geometry.  A binder that holds
    -- for a reason unrelated to what it was written to test is not evidence, and
    -- looks exactly like evidence.
    {C₁ : ℝ} (hC₁ : 0 ≤ C₁)
    (hCbd₁ : ∀ δ : ℝ, 0 < δ → δ ≤ e₁ → ∀ t ∈ Metric.sphere (0 : ℂ) R₁,
      ‖B.eval t / (ftDen Q r ((z (b - δ) : ℝ) : ℂ)).eval t‖ ≤ C₁)
    -- `eq:endpoint-linear-gap` at both endpoints, and the threshold it feeds.
    -- The bundled form extracts the two gap rates from the expansion of
    -- `[Prop.~3]` and then produces `h` from them; here all three are inputs.
    -- None of the four hypotheses names `B`, the amplitude, or the remainder, so
    -- one threshold serves every numerator over a fixed denominator.
    {c₀ c₁ h : ℝ} (hhpos : 0 < h)
    (hgapin₀ : ∃ e > (0 : ℝ), ∀ δ : ℝ, 0 < δ → δ ≤ e → ∀ i,
      1 + c₀ * δ ≤ ‖g₀ δ i‖ / τ δ)
    (hgapin₁ : ∃ e > (0 : ℝ), ∀ δ : ℝ, 0 < δ → δ ≤ e → ∀ i,
      1 + c₁ * δ ≤ ‖g₁ (b - δ) i‖ / τ (b - δ))
    (hcl₀ : ∃ e > (0 : ℝ), ∀ (A ζ' : Fin n₀ → ℝ) (θ W : ℝ), 0 < θ → θ ≤ e →
      0 ≤ W → (∀ i ∈ (Finset.univ : Finset (Fin n₀)), |A i| ≤ 2 * W) →
      (∀ i ∈ (Finset.univ : Finset (Fin n₀)), 1 + c₀ * θ ≤ ζ' i) →
        ∀ M : ℕ, h ≤ (M : ℝ) * θ →
          ∑ i ∈ (Finset.univ : Finset (Fin n₀)), |A i| * (ζ' i ^ (M + 1))⁻¹ ≤ 1 / 4 * W)
    (hcl₁ : ∃ e > (0 : ℝ), ∀ (A ζ' : Fin n₁ → ℝ) (η W : ℝ), 0 < η → η ≤ e →
      0 ≤ W → (∀ i ∈ (Finset.univ : Finset (Fin n₁)), |A i| ≤ 2 * W) →
      (∀ i ∈ (Finset.univ : Finset (Fin n₁)), 1 + c₁ * η ≤ ζ' i) →
        ∀ M : ℕ, h ≤ (M : ℝ) * η →
          ∑ i ∈ (Finset.univ : Finset (Fin n₁)), |A i| * (ζ' i ^ (M + 1))⁻¹ ≤ 1 / 4 * W)

include hA₁ hamp₁ hL₁ hratio₁ hR₁ hσ₁ hσ₁1 he₁ hτpos₁ hτle₁ hroot₁ hsimple₁ haR₁ huniq₁
  hrootplus₁ hne₁ hginj₁ hgmem₁ hgcard₁ hC₁ hCbd₁ hhpos hgapin₀ hgapin₁ hcl₀ hcl₁

/-- **`thm:weighted-dominance` against the interior *data* rather than the geometry
that would produce it.**  Every endpoint binder is unchanged; what moves is the
interior antecedent, which is now `hdata_entry_of_interior`'s conclusion — the
remainder bound, the amplitude floor over a divisor, and the deleted-window
clause — in place of the fixed-circle block that theorem consumes.

The distinction is not presentational, and from `3 ≤ r` it is the difference
between a satisfiable antecedent and an unsatisfiable one.  The block asks for
**one** separating radius across the whole compact interior,
`sup τ < R_0 < inf(third modulus)`, while `thm:FT-geometry` gives only the
pointwise ratio `third(θ) ≥ (1+c)τ(θ)`, at one angle at a time.

Whether the two agree is decided by `n_1 = r - 2`, the count of **non-principal**
members of the cluster that collapses into the origin at the upper endpoint.  At
`r = 2` that count is zero: the principal pair is the whole collapsing set,
nothing non-principal runs into the origin with `τ`, the third modulus stays
`O(1)`, and `sup τ` and `inf third` are attained at the *same* angle — so the
fixed form reduces to the pointwise ratio and asks nothing extra.  From `r = 3` a
non-principal member collapses too, `inf third → 0` at the upper end while
`sup τ` sits at the lower one, and no radius separates them.

`check_interior_fixed_radius_higher_r.py` asserts that split rather than
describing it, over pencils with the smallest zero repeated: above `1` in every
row at `r = 2`, below `1` in every row at `r ≥ 3`, with the pointwise ratio
holding throughout.

So the data form is the one a caller can meet at every `r`.  Its constants
reassemble over a finite cover through
`InteriorSeparation.interior_data_of_pieces`, and one radius per piece is what the
geometry does supply. -/
theorem weighted_dominance_of_branch_any_multiplicity_at_of_threshold_of_data :
    ∃ ε > (0 : ℝ), ∀ Θ : ℕ → Set ℝ,
      (∃ (CI σI AI : ℝ) (Sd : Finset ℝ) (νd : ℝ → ℕ),
        0 < σI ∧ σI < 1 ∧ 0 < AI ∧ (∀ θj ∈ Sd, 1 ≤ νd θj) ∧
        (∀ (M : ℕ) (θ : ℝ), ε ≤ θ → θ ≤ b - ε →
          |ftRemainder Q B r z τ M θ| ≤ CI * σI ^ M) ∧
        (∀ θ : ℝ, ε ≤ θ → θ ≤ b - ε →
          AI * ∏ θj ∈ Sd, |θ - θj| ^ νd θj ≤ ftPrincipalAmp Q B r z τ θ) ∧
        (∀ (M : ℕ) (θ : ℝ), θ ∉ Θ M → ∀ θj ∈ Sd,
          Real.exp (-((-Real.log σI) / (2 * Sd.card) * M / νd θj)) ≤ |θ - θj|)) →
      ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M → ∀ θ : ℝ,
        h / M ≤ θ → θ ≤ b - h / M → θ ∉ Θ M →
          ftRemainder Q B r z τ M θ ≤ ftPrincipalAmp Q B r z τ θ / 2 := by
  -- Four binders the others already force, constructed rather than carried.
  -- `0` is not a denominator zero, because `D(0,z) = Q(0) ≠ 0` once `r ≥ 1`;
  -- and `τ` stays inside the separating circle because `τmax/R ≤ σ < 1`.
  have hzero_not_root : ∀ zz : ℝ, (ftDen Q r ((zz : ℝ) : ℂ)).eval 0 ≠ 0 := by
    intro zz hev
    rw [ftDen_eval, zero_pow (by omega : r ≠ 0), mul_zero, add_zero] at hev
    exact hQ0 hev
  have hP₀ : ftDen Q r ((z 0 : ℝ) : ℂ) ≠ 0 := by
    intro h
    exact hzero_not_root (z 0) (by rw [h]; simp)
  have hP₁ : ftDen Q r ((z (b - 0) : ℝ) : ℂ) ≠ 0 := by
    intro h
    exact hzero_not_root (z (b - 0)) (by rw [h]; simp)
  have ha0₀ : ∀ δ : ℝ, 0 < δ → δ ≤ e₀ → ∀ a ∈ sfun₀ δ, a ≠ 0 := by
    intro δ hδ hδe a haS h0
    exact hzero_not_root (z δ) (h0 ▸ hroot₀ δ hδ hδe a haS)
  have ha0₁ : ∀ δ : ℝ, 0 < δ → δ ≤ e₁ → ∀ a ∈ sfun₁ δ, a ≠ 0 := by
    intro δ hδ hδe a haS h0
    exact hzero_not_root (z (b - δ)) (h0 ▸ hroot₁ δ hδ hδe a haS)
  have hτmR₀ : τmax₀ ≤ R₀ := by
    have h1 : τmax₀ / R₀ < 1 := lt_of_le_of_lt hσ₀ hσ₀1
    rw [div_lt_one hR₀] at h1
    linarith
  have hτmR₁ : τmax₁ ≤ R₁ := by
    have h1 : τmax₁ / R₁ < 1 := lt_of_le_of_lt hσ₁ hσ₁1
    rw [div_lt_one hR₁] at h1
    linarith
  have hτR₀ : ∀ δ : ℝ, 0 < δ → δ ≤ e₀ → τ δ ≤ R₀ :=
    fun δ hδ hδe => le_trans (hτle₀ δ hδ hδe) hτmR₀
  have hτR₁ : ∀ δ : ℝ, 0 < δ → δ ≤ e₁ → τ (b - δ) ≤ R₁ :=
    fun δ hδ hδe => le_trans (hτle₁ δ hδ hδe) hτmR₁
  -- the amplitude floors
  obtain ⟨A₀, hA₀, ea₀, hea₀, hamp₀⟩ :=
    ftPrincipalAmp_lower_bound (w := id) hB0 hr hte₀ hγe₀ hγ0₀ hγd₀ hP₀ hk₀ hrootev₀
  obtain ⟨ea₁, hea₁, hamp₁⟩ := hamp₁
  -- six sign conditions the other binders already force
  have hτmax₀ : 0 ≤ τmax₀ :=
    le_trans (hτpos₀ e₀ he₀ le_rfl).le (hτle₀ e₀ he₀ le_rfl)
  have hτmax₁ : 0 ≤ τmax₁ :=
    le_trans (hτpos₁ e₁ he₁ le_rfl).le (hτle₁ e₁ he₁ le_rfl)
  have hσ₀0 : 0 ≤ σ₀ := le_trans (by positivity) hσ₀
  have hσ₁0 : 0 ≤ σ₁ := le_trans (by positivity) hσ₁
  -- `eq:contour-remainder-bound`'s constant, produced on each closed endpoint
  -- window rather than assumed uniform there
  -- `eq:lower-residue-ratio`, from `Cluster.tendsto_residue_ratio_cluster`
  have hδne : ∀ᶠ δ : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0), ((δ : ℝ) : ℂ) ≠ 0 := by
    filter_upwards [eventually_mem_nhdsWithin] with δ hδ
    exact_mod_cast ne_of_gt hδ
  have hamp_eq : ∀ (zz : ℝ) (t : ℂ), (ftDen Q r ((zz : ℝ) : ℂ)).eval t = 0 →
      ftAmp Q B r ((zz : ℝ) : ℂ) t
        = -B.eval t / (derivative (ftDen Q r ((zz : ℝ) : ℂ))).eval t := by
    intro zz t ht
    rw [ftAmp_eq_derivative ht, neg_div]
  have hratio₀ : ∀ i : Fin n₀, Filter.Tendsto
      (fun δ => ftAmp Q B r ((z δ : ℝ) : ℂ) (g₀ δ i)
        / ftAmp Q B r ((z δ : ℝ) : ℂ) (ftPrincipal τ δ))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds ((clusterAlpha x₁ ρ (idx₀ i) / clusterAlpha x₁ ρ jp₀)
        ^ ((νB₀ : ℤ) - ((ρ - 1 : ℕ) : ℤ)))) := by
    intro i
    have hn₀ : 0 < n₀ := lt_of_le_of_lt (Nat.zero_le _) i.isLt
    have hρi : 2 ≤ ρ := hρ hn₀
    have hcore := tendsto_residue_ratio_cluster (ν := νB₀) (k := ρ - 1)
      (aj := clusterAlpha x₁ ρ (idx₀ i)) (ap := clusterAlpha x₁ ρ jp₀)
      (hcB₀ hn₀) (hcQ₀ hn₀) (clusterAlpha_ne_zero hx₁ hρi _)
      (clusterAlpha_ne_zero hx₁ hρi _) hδne (hBj₀ i) (hBp₀ hn₀) (hEj₀ i) (hEp₀ hn₀)
    refine hcore.congr' ?_
    have hmem : ∀ᶠ δ : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0), 0 < δ ∧ δ ≤ e₀ := by
      have h1 : ∀ᶠ δ : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0), δ ≤ e₀ :=
        eventually_nhdsWithin_of_eventually_nhds
          ((continuousAt_id (x := (0 : ℝ))).eventually_le_const he₀)
      filter_upwards [eventually_mem_nhdsWithin, h1] with δ h2 h3
      exact ⟨h2, h3⟩
    filter_upwards [hmem] with δ hδ
    have hgm := hgmem₀ δ hδ.1 hδ.2 i
    have hgs : g₀ δ i ∈ sfun₀ δ :=
      Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hgm)
    rw [hamp_eq (z δ) (g₀ δ i) (hroot₀ δ hδ.1 hδ.2 _ hgs),
      hamp_eq (z δ) (ftPrincipal τ δ) (hrootplus₀ δ hδ.1 hδ.2)]
  -- the residue comparisons
  obtain ⟨ec₀, hec₀, hCW₀⟩ :=
    ftCluster_amplitude_le_two (w := id) (g := g₀)
      (L := fun i => (clusterAlpha x₁ ρ (idx₀ i) / clusterAlpha x₁ ρ jp₀)
        ^ ((νB₀ : ℤ) - ((ρ - 1 : ℕ) : ℤ)))
      (fun i => norm_clusterAlpha_zpow_ratio hx₁
        (hρ (lt_of_le_of_lt (Nat.zero_le _) i.isLt)) (idx₀ i) jp₀ _) hratio₀
      (ftPrincipalAmp_ne_zero_of_lower_bound (w := id) hA₀ hea₀ hamp₀)
  obtain ⟨ec₁, hec₁, hCW₁⟩ :=
    ftCluster_amplitude_le_two (w := fun δ => b - δ) (g := fun δ => g₁ (b - δ))
      (L := L₁) hL₁ hratio₁
      (ftPrincipalAmp_ne_zero_of_lower_bound (w := fun δ => b - δ) hA₁ hea₁ hamp₁)
  -- `eq:endpoint-linear-gap`, supplied rather than extracted, and the cluster
  -- threshold at those two rates
  obtain ⟨eg₀, heg₀, hgap₀'⟩ := hgapin₀
  obtain ⟨eg₁, heg₁, hgap₁'⟩ := hgapin₁
  obtain ⟨ecl₀, hecl₀, hcl₀'⟩ := hcl₀
  obtain ⟨ecl₁, hecl₁, hcl₁'⟩ := hcl₁
  -- the endpoint splits
  have hsp₀ := ftSplit_of_branch (w := id) (g := g₀) (sfun := sfun₀) hQ hB hr hQ0 hR₀ hσ₀
    hC₀ hτpos₀ hτle₀ hτR₀ hroot₀ hsimple₀ ha0₀ haR₀ huniq₀ hrootplus₀ hne₀ hginj₀ hgmem₀
    hgcard₀ hCbd₀
  have hsp₁ := ftSplit_of_branch (w := fun δ => b - δ) (g := fun δ => g₁ (b - δ))
    (sfun := sfun₁) hQ hB hr
    hQ0 hR₁ hσ₁ hC₁ hτpos₁ hτle₁ hτR₁ hroot₁ hsimple₁ ha0₁ haR₁ huniq₁ hrootplus₁ hne₁ hginj₁
    hgmem₁ hgcard₁ hCbd₁
  -- the eight endpoint windows, reconciled once; `ε` is what the theorem hands
  -- back, so a caller learns the interior parameter BEFORE choosing `Θ`.
  set εA : ℝ :=
    min (min (min (min ea₀ ec₀) (min eg₀ e₀)) (min (min ea₁ ec₁) (min eg₁ e₁)))
      (min ecl₀ ecl₁) with hεA
  have hεApos : 0 < εA := by
    rw [hεA]; repeat' apply lt_min
    all_goals assumption
  have kP : εA ≤ min (min (min ea₀ ec₀) (min eg₀ e₀)) (min (min ea₁ ec₁) (min eg₁ e₁)) :=
    min_le_left _ _
  have k1 : εA ≤ ea₀ :=
    le_trans kP (le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_left _ _)))
  have k2 : εA ≤ ec₀ :=
    le_trans kP (le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_right _ _)))
  have k3 : εA ≤ eg₀ :=
    le_trans kP (le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
  have k4 : εA ≤ e₀ :=
    le_trans kP (le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))
  have k5 : εA ≤ ea₁ :=
    le_trans kP (le_trans (min_le_right _ _) (le_trans (min_le_left _ _) (min_le_left _ _)))
  have k6 : εA ≤ ec₁ :=
    le_trans kP (le_trans (min_le_right _ _) (le_trans (min_le_left _ _) (min_le_right _ _)))
  have k7 : εA ≤ eg₁ :=
    le_trans kP (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
  have k8 : εA ≤ e₁ :=
    le_trans kP (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))
  have k9 : εA ≤ ecl₀ := le_trans (min_le_right _ _) (min_le_left _ _)
  have k10 : εA ≤ ecl₁ := le_trans (min_le_right _ _) (min_le_right _ _)
  refine ⟨εA, hεApos, fun Θ hdata => ?_⟩
  exact weighted_dominance_ftCoeffPoly_at_of_threshold (e := εA) (h := h) hεApos hhpos
    (Wf₀ := fun δ i => ‖ftAmp Q B r ((z δ : ℝ) : ℂ) (g₀ δ i)‖)
    (ζ₀ := fun δ i => ‖g₀ δ i‖ / τ δ)
    (Wf₁ := fun θ i => ‖ftAmp Q B r ((z θ : ℝ) : ℂ) (g₁ θ i)‖)
    (ζ₁ := fun θ i => ‖g₁ θ i‖ / τ θ)
    hA₀ (mul_nonneg hτmax₀ hC₀) hσ₀0 hσ₀1
    hA₁ (mul_nonneg hτmax₁ hC₁) hσ₁0 hσ₁1
    (fun θ hθ hθe => hamp₀ θ hθ (le_trans hθe k1))
    (fun θ hθ hθe i => by
      have := hCW₀ θ hθ (le_trans hθe k2) i
      rwa [abs_of_nonneg (norm_nonneg _)])
    (fun θ hθ hθe => hgap₀' θ hθ (le_trans hθe k3))
    (fun A ζ' θ W hθ hθe => hcl₀' A ζ' θ W hθ (le_trans hθe k9))
    (fun M θ hθ hθe => hsp₀ M θ hθ (le_trans hθe k4))
    (fun η hη hηe => hamp₁ η hη (le_trans hηe k5))
    (fun η hη hηe i => by
      have := hCW₁ η hη (le_trans hηe k6) i
      rwa [abs_of_nonneg (norm_nonneg _)])
    (fun η hη hηe => hgap₁' η hη (le_trans hηe k7))
    (fun A ζ' η W hη hηe => hcl₁' A ζ' η W hη (le_trans hηe k10))
    (fun M η hη hηe => hsp₁ M η hη (le_trans hηe k8))
    (hint_of_interior_data_at hdata)

/-- **`weighted_dominance_of_branch_any_multiplicity_at` with the threshold an
input.**  The gap rates of `eq:endpoint-linear-gap` and the threshold `h` they
feed are parameters here, not constants manufactured inside.  That is the
paper's own order: `h` is a function of the denominator and `r` alone, and the
numerator enters only at `M_0`.  With `h` produced under the numerator's binder
the statement cannot say so, and a caller reading a numerator-uniform constant
off it is reading something the type does not carry.

Four hypotheses replace the two expansion groups the bundled form carries: the
two linear gaps, which `exists_endpoint_linear_gap_of_expansion_on` and
`exists_endpoint_linear_gap_of_norm_on` supply from those same expansions, and
the two cluster bounds, which are
`Dominance.exists_cluster_threshold`'s conclusion at those rates.  None
of the four names `B`, `ftAmp`, `ftPrincipalAmp` or `ftRemainder`.

**Containment.**  As in the bundled form, no binder names `ftRemainder`, so no
binder relates the two sides of the conclusion.  The four new ones name only the

This is now the data form above, composed with `hdata_entry_of_interior`.  The
statement is unchanged, so every consumer of it is unchanged; what the derivation
records is that the fixed-circle block is *sufficient* for the interior input and
not necessary — and at `2 ≤ r` it is not available, which is why the data form is
the one the branch composition uses.
cluster moduli `‖g₀ δ i‖ / τ δ` and abstract amplitude-gap data. -/
theorem weighted_dominance_of_branch_any_multiplicity_at_of_threshold :
    ∃ ε > (0 : ℝ), ∀ Θ : ℕ → Set ℝ,
      (∃ (Ri τmi σi : ℝ) (S : Finset ℝ),
      0 < Ri ∧ τmi / Ri ≤ σi ∧ 0 < σi ∧ σi < 1 ∧
      (∀ θ : ℝ, ε ≤ θ → θ ≤ b - ε → 0 < τ θ) ∧
      (∀ θ : ℝ, ε ≤ θ → θ ≤ b - ε → τ θ ≤ τmi) ∧
      (∀ θ : ℝ, ε ≤ θ → θ ≤ b - ε → τ θ < Ri) ∧
      (∀ θ : ℝ, ε ≤ θ → θ ≤ b - ε →
        (ftDen Q r ((z θ : ℝ) : ℂ)).eval (ftPrincipal τ θ) = 0) ∧
      (∀ θ : ℝ, ε ≤ θ → θ ≤ b - ε →
        (derivative (ftDen Q r ((z θ : ℝ) : ℂ))).eval (ftPrincipal τ θ) ≠ 0) ∧
      (∀ θ : ℝ, ε ≤ θ → θ ≤ b - ε →
        (derivative (ftDen Q r ((z θ : ℝ) : ℂ))).eval
          (((τ θ : ℝ) : ℂ) * Complex.exp (-((θ : ℝ) : ℂ) * I)) ≠ 0) ∧
      (∀ θ : ℝ, ε ≤ θ → θ ≤ b - ε →
        ftPrincipal τ θ ≠ ((τ θ : ℝ) : ℂ) * Complex.exp (-((θ : ℝ) : ℂ) * I)) ∧
      (∀ θ : ℝ, ε ≤ θ → θ ≤ b - ε → ∀ t : ℂ, ‖t‖ ≤ Ri →
        (ftDen Q r ((z θ : ℝ) : ℂ)).eval t = 0 →
        t = ftPrincipal τ θ ∨ t = ((τ θ : ℝ) : ℂ) * Complex.exp (-((θ : ℝ) : ℂ) * I)) ∧
      (↑S ⊆ Set.Icc ε (b - ε)) ∧
      (∀ θj ∈ S, ftAmp Q B r ((z θj : ℝ) : ℂ) (ftPrincipal τ θj) = 0) ∧
      (∀ θ ∈ Set.Icc ε (b - ε),
        ftAmp Q B r ((z θ : ℝ) : ℂ) (ftPrincipal τ θ) = 0 → θ ∈ S) ∧
      (∀ θ ∈ Set.Icc ε (b - ε), ∃ γ' : ℂ, γ' ≠ 0 ∧ HasDerivAt (ftPrincipal τ) γ' θ) ∧
      (∀ θ ∈ Set.Icc ε (b - ε), ContinuousAt (fun θ' => ((z θ' : ℝ) : ℂ)) θ) ∧
      (∀ (M : ℕ) (θ : ℝ), θ ∉ Θ M → ∀ θj ∈ S,
        Real.exp (-((-Real.log σi) / (2 * S.card) * M
          / (B.rootMultiplicity (ftPrincipal τ θj)))) ≤ |θ - θj|)) →
      ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M → ∀ θ : ℝ,
        h / M ≤ θ → θ ≤ b - h / M → θ ∉ Θ M →
          ftRemainder Q B r z τ M θ ≤ ftPrincipalAmp Q B r z τ θ / 2 := by
  obtain ⟨ε, hε, H⟩ :=
    weighted_dominance_of_branch_any_multiplicity_at_of_threshold_of_data (h := h)
      hQ hB hB0 hr hQ0 hx₁ hρ hte₀ hγe₀ hγ0₀ hγd₀ hk₀ hrootev₀ hcB₀ hcQ₀ hBj₀ hBp₀ hEj₀ hEp₀ hR₀
      hσ₀ hσ₀1 he₀ hτpos₀ hτle₀ hroot₀ hsimple₀ haR₀ huniq₀ hrootplus₀ hne₀ hginj₀ hgmem₀ hgcard₀
      hC₀ hCbd₀ hA₁ hamp₁ hL₁ hratio₁ hR₁ hσ₁ hσ₁1 he₁ hτpos₁ hτle₁ hroot₁ hsimple₁ haR₁ huniq₁
      hrootplus₁ hne₁ hginj₁ hgmem₁ hgcard₁ hC₁ hCbd₁ hhpos hgapin₀ hgapin₁ hcl₀ hcl₁
  refine ⟨ε, hε, fun Θ hinterior => ?_⟩
  obtain ⟨Ri, τmi, σi, S, hRi, hσi, hσi0, hσi1, hτposI, hτleI,
    hτRI, hrpI, hspI, hsmI, hneeI, hpairI, hSsubI, hSzeroI, hzerosI, hγdI, hzcI,
    hwinI⟩ := hinterior
  exact H Θ (hdata_entry_of_interior hQ hB hr hQ0 hB0 hRi hσi hσi0 hσi1 hτposI
    hτleI hτRI hrpI hspI hsmI hneeI hpairI hSsubI hSzeroI hzerosI hγdI hzcI hwinI)

end SuppliedGeometryForms

section ExtractedGapForms

/-! The two forms below extract `eq:endpoint-linear-gap` instead of assuming it,
so each carries the expansion group at both endpoints.  That group is why this
block cannot join the outer one: here it precedes the upper endpoint and in
`SuppliedGeometryForms` there is none, so hoisting further would reorder
binders, which is a different statement. -/

variable
    -- `eq:endpoint-linear-gap` is *not* assumed: Prop. 3 supplies the expansion
    -- `ζ_j(δ) = 1 + c_jδ + O(δ²)`, and the uniform gap is our extraction from it
    {Cexp₀ : ℝ} (hCexp₀ : 0 ≤ Cexp₀)
    (hωne₀ : ∀ i : Fin n₀, clusterOmega ρ (idx₀ i)
      ≠ Complex.exp (((Real.pi / ρ : ℝ) : ℂ) * I))
    (hωne'₀ : ∀ i : Fin n₀, clusterOmega ρ (idx₀ i)
      ≠ Complex.exp (((-(Real.pi / ρ) : ℝ) : ℂ) * I))
    (hexp₀ : ∀ i : Fin n₀, ∀ δ : ℝ, 0 < δ → δ ≤ e₀ →
      ‖g₀ δ i / ((τ δ : ℝ) : ℂ)
        - (1 + ((((Real.cos (Real.pi / ρ) : ℝ) : ℂ) - clusterOmega ρ (idx₀ i))
            / ((Real.sin (Real.pi / ρ) : ℝ) : ℂ)) * (δ : ℂ))‖ ≤ Cexp₀ * δ ^ 2)
    -- upper endpoint: the same, through the chart `η ↦ b - η`
    -- the upper endpoint enters as the amplitude bound itself, not as a route to
    -- it: `weighted_dominance_ftCoeffPoly` already takes `p₁` abstractly, and the
    -- endpoint group's only use here was to obtain this.  Which route proves it
    -- depends on `r` — the finite one at `r = 1`, where `γ(0) ≠ 0`, and the origin
    -- one at `r ≥ 2`, where `FTBranchUpperRefutation` proves `γ(0) = 0`.
    {p₁ : ℕ} {A₁ : ℝ} (hA₁ : 0 < A₁)
    (hamp₁ : ∃ e > (0 : ℝ), ∀ η : ℝ, 0 < η → η ≤ e →
      A₁ * η ^ p₁ ≤ ftPrincipalAmp Q B r z τ (b - η))
    -- `eq:lower-residue-ratio` is *not* assumed either: what is taken is the
    -- leading behavior of `B` and of `∂_tD` along each branch, which Taylor at
    -- `x_1` reads off Prop. 3's expansion; the ratio is `Cluster`'s theorem
    -- `eq:upper-residue-ratio`.  At the upper endpoint the amplitude ratio is a
    -- ratio of NORMALIZED ROOTS, `W_j/W = ζ_j/ζ_+(1+O(τ))`, and its limit has
    -- modulus one because the `ζ` tend to the `r`th roots of `-1`.  This is NOT
    -- the lower endpoint's cluster ratio: `B(0) ≠ 0`, so `B` does not vanish on
    -- this cluster, and no `clusterAlpha`, no `ν_B` and no `ρ-1` enters.  The
    -- cluster is empty unless `r ≥ 2`, which is `hn₁r`.
    {idx₁ : Fin n₁ → ℕ} {L₁ : Fin n₁ → ℂ}
    (hn₁r : 0 < n₁ → 2 ≤ r)
    (hL₁ : ∀ i : Fin n₁, ‖L₁ i‖ = 1)
    (hratio₁ : ∀ i : Fin n₁, Filter.Tendsto
      (fun δ : ℝ => ftAmp Q B r ((z (b - δ) : ℝ) : ℂ) (g₁ (b - δ) i)
        / ftAmp Q B r ((z (b - δ) : ℝ) : ℂ) (ftPrincipal τ (b - δ)))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (L₁ i)))
    {R₁ τmax₁ σ₁ e₁ : ℝ} (hR₁ : 0 < R₁) (hσ₁ : τmax₁ / R₁ ≤ σ₁) (hσ₁1 : σ₁ < 1)
    (he₁ : 0 < e₁)
    (hτpos₁ : ∀ δ : ℝ, 0 < δ → δ ≤ e₁ → 0 < τ (b - δ))
    (hτle₁ : ∀ δ : ℝ, 0 < δ → δ ≤ e₁ → τ (b - δ) ≤ τmax₁)
    (hroot₁ : ∀ δ : ℝ, 0 < δ → δ ≤ e₁ → ∀ a ∈ sfun₁ δ,
      (ftDen Q r ((z (b - δ) : ℝ) : ℂ)).eval a = 0)
    (hsimple₁ : ∀ δ : ℝ, 0 < δ → δ ≤ e₁ → ∀ a ∈ sfun₁ δ,
      (derivative (ftDen Q r ((z (b - δ) : ℝ) : ℂ))).eval a ≠ 0)
    (haR₁ : ∀ δ : ℝ, 0 < δ → δ ≤ e₁ → ∀ a ∈ sfun₁ δ, ‖a‖ < R₁)
    (huniq₁ : ∀ δ : ℝ, 0 < δ → δ ≤ e₁ → ∀ t : ℂ, ‖t‖ ≤ R₁ →
      (ftDen Q r ((z (b - δ) : ℝ) : ℂ)).eval t = 0 → t ∈ sfun₁ δ)
    (hrootplus₁ : ∀ δ : ℝ, 0 < δ → δ ≤ e₁ →
      (ftDen Q r ((z (b - δ) : ℝ) : ℂ)).eval (ftPrincipal τ (b - δ)) = 0)
    (hne₁ : ∀ δ : ℝ, 0 < δ → δ ≤ e₁ →
      ftPrincipal τ (b - δ) ≠ ((τ (b - δ) : ℝ) : ℂ) * Complex.exp (-((b - δ : ℝ) : ℂ) * I))
    (hginj₁ : ∀ δ : ℝ, 0 < δ → δ ≤ e₁ → Function.Injective (g₁ (b - δ)))
    (hgmem₁ : ∀ δ : ℝ, 0 < δ → δ ≤ e₁ → ∀ i, g₁ (b - δ) i ∈
      ((sfun₁ δ).erase (ftPrincipal τ (b - δ))).erase
        (((τ (b - δ) : ℝ) : ℂ) * Complex.exp (-((b - δ : ℝ) : ℂ) * I)))
    (hgcard₁ : ∀ δ : ℝ, 0 < δ → δ ≤ e₁ →
      (((sfun₁ δ).erase (ftPrincipal τ (b - δ))).erase
        (((τ (b - δ) : ℝ) : ℂ) * Complex.exp (-((b - δ : ℝ) : ℂ) * I))).card = n₁)
    -- the contour bound enters as the punctured statement the proof uses.  The
    -- closed-window form is not merely stronger than needed here: at `r ≥ 2` it is
    -- unmeetable, because `z` is unbounded as `δ → 0` and a continuous function on
    -- a compact set is bounded; and at the one pencil where it IS discharged, it
    -- passes without probing the endpoint at all — at `δ = 0` the junk value of `z`
    -- leaves `Q` alone, whose zero misses the sphere, so it holds by Lean's
    -- division-by-zero convention rather than by the geometry.  A binder that holds
    -- for a reason unrelated to what it was written to test is not evidence, and
    -- looks exactly like evidence.
    {C₁ : ℝ} (hC₁ : 0 ≤ C₁)
    (hCbd₁ : ∀ δ : ℝ, 0 < δ → δ ≤ e₁ → ∀ t ∈ Metric.sphere (0 : ℂ) R₁,
      ‖B.eval t / (ftDen Q r ((z (b - δ) : ℝ) : ℂ)).eval t‖ ≤ C₁)
    -- `eq:endpoint-linear-gap` is *not* assumed: Prop. 3 supplies the expansion
    -- `ζ_j(δ) = 1 + c_jδ + O(δ²)`, and the uniform gap is our extraction from it
    {Cexp₁ : ℝ} (hCexp₁ : 0 ≤ Cexp₁)
    (hωne₁ : ∀ i : Fin n₁, clusterOmega r (idx₁ i)
      ≠ Complex.exp (((Real.pi / r : ℝ) : ℂ) * I))
    (hωne'₁ : ∀ i : Fin n₁, clusterOmega r (idx₁ i)
      ≠ Complex.exp (((-(Real.pi / r) : ℝ) : ℂ) * I))
    -- the MODULUS form: at the upper endpoint `ζ_j → ω_j`, an `r`th root of `-1`,
    -- not to `1`, so only `‖ζ_j‖` expands about `1`.  `eq:endpoint-linear-gap`'s
    -- upper display is a modulus in the manuscript and the two endpoints do not
    -- share expansion shape any more than they share residue geometry.
    (hexp₁ : ∀ i : Fin n₁, ∀ δ : ℝ, 0 < δ → δ ≤ e₁ →
      |‖g₁ (b - δ) i / ((τ (b - δ) : ℝ) : ℂ)‖
        - (1 + ((Real.cos (Real.pi / r) - (clusterOmega r (idx₁ i)).re)
            / Real.sin (Real.pi / r)) * δ)| ≤ Cexp₁ * δ ^ 2)

include hCexp₀ hωne₀ hωne'₀ hexp₀ hA₁ hamp₁ hn₁r hL₁ hratio₁ hR₁ hσ₁ hσ₁1 he₁ hτpos₁ hτle₁
  hroot₁ hsimple₁ haR₁ huniq₁ hrootplus₁ hne₁ hginj₁ hgmem₁ hgcard₁ hC₁ hCbd₁ hCexp₁ hωne₁
  hωne'₁ hexp₁

/-- **`thm:weighted-dominance` with the interior parameter handed back.**  The
theorem produces the `ε` it will use — the reconciliation of the eight endpoint
windows — and only then asks for the interior data, at that one `ε`, for a
deleted family `Θ` chosen afterwards.

That order is `subsec:proof`'s and it is what BANK-37's residue asks for.  In
`weighted_dominance_of_branch_any_multiplicity` the deleted family is bound
*before* `hinterior`'s `∀ e`, so one `Θ` has to serve every interior parameter,
and at a pencil whose branch radius climbs to `1` that forces it
`M`-independent.  Here `Θ` is quantified inside, after `ε` is known, so it has to
serve one interior parameter and the caller may build it out of that `ε`'s own
`σ`.  Nothing in the endpoint group mentions `Θ`, which is why `ε` can be
produced before it.

`weighted_dominance_of_branch_any_multiplicity` is this theorem applied at the
`ε` it returns, and its signature is unchanged. -/
theorem weighted_dominance_of_branch_any_multiplicity_at :
    ∃ ε > (0 : ℝ), ∀ Θ : ℕ → Set ℝ,
      (∃ (Ri τmi σi : ℝ) (S : Finset ℝ),
      0 < Ri ∧ τmi / Ri ≤ σi ∧ 0 < σi ∧ σi < 1 ∧
      (∀ θ : ℝ, ε ≤ θ → θ ≤ b - ε → 0 < τ θ) ∧
      (∀ θ : ℝ, ε ≤ θ → θ ≤ b - ε → τ θ ≤ τmi) ∧
      (∀ θ : ℝ, ε ≤ θ → θ ≤ b - ε → τ θ < Ri) ∧
      (∀ θ : ℝ, ε ≤ θ → θ ≤ b - ε →
        (ftDen Q r ((z θ : ℝ) : ℂ)).eval (ftPrincipal τ θ) = 0) ∧
      (∀ θ : ℝ, ε ≤ θ → θ ≤ b - ε →
        (derivative (ftDen Q r ((z θ : ℝ) : ℂ))).eval (ftPrincipal τ θ) ≠ 0) ∧
      (∀ θ : ℝ, ε ≤ θ → θ ≤ b - ε →
        (derivative (ftDen Q r ((z θ : ℝ) : ℂ))).eval
          (((τ θ : ℝ) : ℂ) * Complex.exp (-((θ : ℝ) : ℂ) * I)) ≠ 0) ∧
      (∀ θ : ℝ, ε ≤ θ → θ ≤ b - ε →
        ftPrincipal τ θ ≠ ((τ θ : ℝ) : ℂ) * Complex.exp (-((θ : ℝ) : ℂ) * I)) ∧
      (∀ θ : ℝ, ε ≤ θ → θ ≤ b - ε → ∀ t : ℂ, ‖t‖ ≤ Ri →
        (ftDen Q r ((z θ : ℝ) : ℂ)).eval t = 0 →
        t = ftPrincipal τ θ ∨ t = ((τ θ : ℝ) : ℂ) * Complex.exp (-((θ : ℝ) : ℂ) * I)) ∧
      (↑S ⊆ Set.Icc ε (b - ε)) ∧
      (∀ θj ∈ S, ftAmp Q B r ((z θj : ℝ) : ℂ) (ftPrincipal τ θj) = 0) ∧
      (∀ θ ∈ Set.Icc ε (b - ε),
        ftAmp Q B r ((z θ : ℝ) : ℂ) (ftPrincipal τ θ) = 0 → θ ∈ S) ∧
      (∀ θ ∈ Set.Icc ε (b - ε), ∃ γ' : ℂ, γ' ≠ 0 ∧ HasDerivAt (ftPrincipal τ) γ' θ) ∧
      (∀ θ ∈ Set.Icc ε (b - ε), ContinuousAt (fun θ' => ((z θ' : ℝ) : ℂ)) θ) ∧
      (∀ (M : ℕ) (θ : ℝ), θ ∉ Θ M → ∀ θj ∈ S,
        Real.exp (-((-Real.log σi) / (2 * S.card) * M
          / (B.rootMultiplicity (ftPrincipal τ θj)))) ≤ |θ - θj|)) →
      ∃ h > (0 : ℝ), ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M → ∀ θ : ℝ,
        h / M ≤ θ → θ ≤ b - h / M → θ ∉ Θ M →
          ftRemainder Q B r z τ M θ ≤ ftPrincipalAmp Q B r z τ θ / 2 := by
  -- `eq:endpoint-linear-gap`, extracted from the expansion of `[Prop.~3]`
  obtain ⟨c₀, hc₀, δg₀, hδg₀, hgapraw₀⟩ :=
    exists_endpoint_linear_gap_of_expansion_on (J := (Finset.univ : Finset (Fin n₀)))
      (ζ := fun i δ => g₀ δ i / ((τ δ : ℝ) : ℂ))
      (c := fun i => (((Real.cos (Real.pi / ρ) : ℝ) : ℂ) - clusterOmega ρ (idx₀ i))
        / ((Real.sin (Real.pi / ρ) : ℝ) : ℂ))
      hCexp₀ he₀ (fun i _ => by
        have hρi : 2 ≤ ρ := hρ (lt_of_le_of_lt (Nat.zero_le _) i.isLt)
        rw [endpoint_expansion_coeff_re]
        exact endpoint_linear_coeff_pos hρi (clusterOmega_pow (by omega : 1 ≤ ρ) _)
          (hωne₀ i) (hωne'₀ i)) (fun i _ => hexp₀ i)
  obtain ⟨c₁, hc₁, δg₁, hδg₁, hgapraw₁⟩ :=
    exists_endpoint_linear_gap_of_norm_on (J := (Finset.univ : Finset (Fin n₁)))
      (ζ := fun i δ => g₁ (b - δ) i / ((τ (b - δ) : ℝ) : ℂ))
      (cf := fun i => (Real.cos (Real.pi / r) - (clusterOmega r (idx₁ i)).re)
        / Real.sin (Real.pi / r))
      hCexp₁ he₁ (fun i _ =>
        endpoint_linear_coeff_pos (hn₁r (lt_of_le_of_lt (Nat.zero_le _) i.isLt))
          (clusterOmega_pow hr _) (hωne₁ i) (hωne'₁ i)) (fun i _ => hexp₁ i)
  have hgap₀ : ∃ e > (0 : ℝ), ∀ δ : ℝ, 0 < δ → δ ≤ e → ∀ i,
      1 + c₀ * δ ≤ ‖g₀ δ i‖ / τ δ := by
    refine ⟨min (δg₀ / 2) e₀, lt_min (by linarith) he₀, fun δ hδ hδe i => ?_⟩
    have hτδ : 0 < τ δ := hτpos₀ δ hδ (le_trans hδe (min_le_right _ _))
    have hx := hgapraw₀ i (Finset.mem_univ i) δ hδ
      (lt_of_le_of_lt (le_trans hδe (min_le_left _ _)) (by linarith))
    rwa [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hτδ] at hx
  have hgap₁ : ∃ e > (0 : ℝ), ∀ δ : ℝ, 0 < δ → δ ≤ e → ∀ i,
      1 + c₁ * δ ≤ ‖g₁ (b - δ) i‖ / τ (b - δ) := by
    refine ⟨min (δg₁ / 2) e₁, lt_min (by linarith) he₁, fun δ hδ hδe i => ?_⟩
    have hτδ : 0 < τ (b - δ) := hτpos₁ δ hδ (le_trans hδe (min_le_right _ _))
    have hx := hgapraw₁ i (Finset.mem_univ i) δ hδ
      (lt_of_le_of_lt (le_trans hδe (min_le_left _ _)) (by linarith))
    rwa [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hτδ] at hx
  -- one threshold for both endpoints: the larger of the two the cluster bound
  -- allows, since `h ≤ Mθ` only gets harder as `h` grows
  obtain ⟨t₀, ht₀, hcl₀⟩ := exists_cluster_threshold (ι := Fin n₀) Finset.univ
    (C_W := 2) (δ := 1 / 4) (c := c₀) (ε := 1) hc₀ zero_le_one (by norm_num) (by norm_num)
  obtain ⟨t₁, ht₁, hcl₁⟩ := exists_cluster_threshold (ι := Fin n₁) Finset.univ
    (C_W := 2) (δ := 1 / 4) (c := c₁) (ε := 1) hc₁ zero_le_one (by norm_num) (by norm_num)
  have hthrpos : 0 < max t₀ t₁ := lt_of_lt_of_le ht₀ (le_max_left _ _)
  have hclu₀ : ∃ e > (0 : ℝ), ∀ (A ζ' : Fin n₀ → ℝ) (θ W : ℝ), 0 < θ → θ ≤ e →
      0 ≤ W → (∀ i ∈ (Finset.univ : Finset (Fin n₀)), |A i| ≤ 2 * W) →
      (∀ i ∈ (Finset.univ : Finset (Fin n₀)), 1 + c₀ * θ ≤ ζ' i) →
        ∀ M : ℕ, max t₀ t₁ ≤ (M : ℝ) * θ →
          ∑ i ∈ (Finset.univ : Finset (Fin n₀)), |A i| * (ζ' i ^ (M + 1))⁻¹ ≤ 1 / 4 * W :=
    ⟨1, one_pos, fun A ζ' θ W hθ hθe hW hA hg M hM =>
      hcl₀ A ζ' θ W hθ hθe hW hA hg M (le_trans (le_max_left _ _) hM)⟩
  have hclu₁ : ∃ e > (0 : ℝ), ∀ (A ζ' : Fin n₁ → ℝ) (η W : ℝ), 0 < η → η ≤ e →
      0 ≤ W → (∀ i ∈ (Finset.univ : Finset (Fin n₁)), |A i| ≤ 2 * W) →
      (∀ i ∈ (Finset.univ : Finset (Fin n₁)), 1 + c₁ * η ≤ ζ' i) →
        ∀ M : ℕ, max t₀ t₁ ≤ (M : ℝ) * η →
          ∑ i ∈ (Finset.univ : Finset (Fin n₁)), |A i| * (ζ' i ^ (M + 1))⁻¹ ≤ 1 / 4 * W :=
    ⟨1, one_pos, fun A ζ' η W hη hηe hW hA hg M hM =>
      hcl₁ A ζ' η W hη hηe hW hA hg M (le_trans (le_max_right _ _) hM)⟩
  obtain ⟨ε, hε, H⟩ :=
    weighted_dominance_of_branch_any_multiplicity_at_of_threshold (h := max t₀ t₁)
    hQ hB hB0 hr hQ0 hx₁ hρ hte₀ hγe₀ hγ0₀ hγd₀ hk₀ hrootev₀ hcB₀ hcQ₀ hBj₀ hBp₀ hEj₀ hEp₀
    hR₀ hσ₀ hσ₀1 he₀ hτpos₀ hτle₀ hroot₀ hsimple₀ haR₀ huniq₀ hrootplus₀ hne₀ hginj₀ hgmem₀
    hgcard₀ hC₀ hCbd₀ hA₁ hamp₁ hL₁ hratio₁ hR₁ hσ₁ hσ₁1 he₁ hτpos₁ hτle₁ hroot₁ hsimple₁
    haR₁ huniq₁ hrootplus₁ hne₁ hginj₁ hgmem₁ hgcard₁ hC₁ hCbd₁ hthrpos hgap₀ hgap₁ hclu₀
    hclu₁
  exact ⟨ε, hε, fun Θ hinterior => ⟨max t₀ t₁, hthrpos, H Θ hinterior⟩⟩

/-- **Paper `thm:weighted-dominance`, on the cited branch and its modulus gap.**
`eq:dominance-bound` on `eq:retained-range` for `F_M`, with the amplitude floor,
the residue comparison and the endpoint split all *applied* rather than assumed:
`hamp` comes from `ftPrincipalAmp_lower_bound`, `hCW` from
`ftCluster_amplitude_le_two` (so `C_W = 2` stays derived from
`eq:lower-residue-ratio`), and `hsplit` from `ftSplit_of_branch`.

What survives in the binder list is the Forgács–Tran branch — the endpoint
factorization data `te`, `γe`, the retained cluster and its enumeration — the
endpoint expansion `ζ_j(δ) = 1 + c_jδ + O(δ^2)` of `[Prop.~3]`
and the leading behavior of `B` and `∂_tD` along each branch, the
separating circle (zero-free, with the retained cluster strictly inside it) and
continuity of the spectral parameter across each closed window, and the interior
supply.  `eq:endpoint-linear-gap`, `eq:lower-residue-ratio` and the uniform
contour constant of `eq:contour-remainder-bound` are **not** binders: the first
two are the manuscript's own extractions from that expansion, the third its own
uniformity sentence, and all three are derived here.  No binder names `poleRem`
or `poleCofactor`, and **none names `ftRemainder`**, so no binder relates the two
sides of the conclusion and none of them can contain it.  Exactly one binder
names `ftPrincipalAmp` -- `hamp₁`, the upper-endpoint amplitude floor -- and it
names only that side.  Its lower counterpart `hamp₀` is not a binder at all:
`ftPrincipalAmp_lower_bound` produces it from the endpoint factorization.  The
asymmetry is the upper endpoint's, not the statement's.  The two endpoints
share one statement through the chart `w`: `id` below, `fun η => b - η` above.

**The two endpoints do not share their residue data, and must not.**  Below,
`eq:lower-residue-ratio` compares amplitudes through `clusterAlpha x_1 ρ`, the
direction into the smallest zero of `Q`, with the orders `ν_B` and `ρ-1`.
Above, `eq:upper-residue-ratio` gives `W_j/W = ζ_j/ζ_+(1+O(τ))`, a ratio
of *normalized roots* whose limit has modulus one — no `clusterAlpha`, no
`ν_B`, no `ρ-1`, because `B(0) ≠ 0` means `B` does not vanish on the upper
cluster at all.  Stating the upper endpoint as a second copy of the lower one is
not merely inexact: `∂_tD ≍ 1/τ` diverges there for `r > 1`, so a
binder dividing it by `δ^{ρ-1}` cannot be satisfied and the theorem goes
vacuous over most of its range.  `hratio₁` and `hL₁` are the upper endpoint in
its own terms; `hexp₁` and the `hωne₁` pair carry `r`, since the upper
cluster tends to the `r`th roots of `-1` with principal pair `e^{± iπ/r}`,
not to the `ρ`th roots.

At `r = 2` those two roots are `e^{± iπ/2}`, both principal, so `n_1 = 0` and
the upper cluster binders are empty.  That is the manuscript's own "the cluster
is the principal pair alone", and the conclusion does not lean on them there:
the upper remainder is then the contour error, bounded by `hσ₁` and the
contour constant. -/
theorem weighted_dominance_of_branch_any_multiplicity
    -- the compact interior: the remainder bound derived, the amplitude's lower
    -- bound by its own zero divisor, and the definition of the deleted windows
    (hinterior : ∀ e : ℝ, 0 < e →
      ∃ (Ri τmi σi : ℝ) (S : Finset ℝ),
        0 < Ri ∧ τmi / Ri ≤ σi ∧ 0 < σi ∧ σi < 1 ∧
        (∀ θ : ℝ, e ≤ θ → θ ≤ b - e → 0 < τ θ) ∧
        (∀ θ : ℝ, e ≤ θ → θ ≤ b - e → τ θ ≤ τmi) ∧
        (∀ θ : ℝ, e ≤ θ → θ ≤ b - e → τ θ < Ri) ∧
        (∀ θ : ℝ, e ≤ θ → θ ≤ b - e →
          (ftDen Q r ((z θ : ℝ) : ℂ)).eval (ftPrincipal τ θ) = 0) ∧
        (∀ θ : ℝ, e ≤ θ → θ ≤ b - e →
          (derivative (ftDen Q r ((z θ : ℝ) : ℂ))).eval (ftPrincipal τ θ) ≠ 0) ∧
        (∀ θ : ℝ, e ≤ θ → θ ≤ b - e →
          (derivative (ftDen Q r ((z θ : ℝ) : ℂ))).eval
            (((τ θ : ℝ) : ℂ) * Complex.exp (-((θ : ℝ) : ℂ) * I)) ≠ 0) ∧
        (∀ θ : ℝ, e ≤ θ → θ ≤ b - e →
          ftPrincipal τ θ ≠ ((τ θ : ℝ) : ℂ) * Complex.exp (-((θ : ℝ) : ℂ) * I)) ∧
        (∀ θ : ℝ, e ≤ θ → θ ≤ b - e → ∀ t : ℂ, ‖t‖ ≤ Ri →
          (ftDen Q r ((z θ : ℝ) : ℂ)).eval t = 0 →
          t = ftPrincipal τ θ ∨ t = ((τ θ : ℝ) : ℂ) * Complex.exp (-((θ : ℝ) : ℂ) * I)) ∧
        (↑S ⊆ Set.Icc e (b - e)) ∧
        (∀ θj ∈ S, ftAmp Q B r ((z θj : ℝ) : ℂ) (ftPrincipal τ θj) = 0) ∧
        (∀ θ ∈ Set.Icc e (b - e),
          ftAmp Q B r ((z θ : ℝ) : ℂ) (ftPrincipal τ θ) = 0 → θ ∈ S) ∧
        (∀ θ ∈ Set.Icc e (b - e), ∃ γ' : ℂ, γ' ≠ 0 ∧ HasDerivAt (ftPrincipal τ) γ' θ) ∧
        (∀ θ ∈ Set.Icc e (b - e), ContinuousAt (fun θ' => ((z θ' : ℝ) : ℂ)) θ) ∧
        (∀ (M : ℕ) (θ : ℝ), θ ∉ Θ M → ∀ θj ∈ S,
          Real.exp (-((-Real.log σi) / (2 * S.card) * M
            / (B.rootMultiplicity (ftPrincipal τ θj)))) ≤ |θ - θj|)) :
    ∃ h > (0 : ℝ), ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M → ∀ θ : ℝ,
      h / M ≤ θ → θ ≤ b - h / M → θ ∉ Θ M →
        ftRemainder Q B r z τ M θ ≤ ftPrincipalAmp Q B r z τ θ / 2 := by
  obtain ⟨ε, hε, H⟩ :=
    weighted_dominance_of_branch_any_multiplicity_at hQ hB hB0 hr hQ0 hx₁ hρ
      hte₀ hγe₀ hγ0₀ hγd₀ hk₀ hrootev₀ hcB₀ hcQ₀ hBj₀ hBp₀ hEj₀ hEp₀
      hR₀ hσ₀ hσ₀1 he₀ hτpos₀ hτle₀ hroot₀ hsimple₀ haR₀ huniq₀ hrootplus₀ hne₀
      hginj₀ hgmem₀ hgcard₀ hC₀ hCbd₀ hCexp₀ hωne₀ hωne'₀ hexp₀
      hA₁ hamp₁ hn₁r hL₁ hratio₁
      hR₁ hσ₁ hσ₁1 he₁ hτpos₁ hτle₁ hroot₁ hsimple₁ haR₁ huniq₁ hrootplus₁ hne₁
      hginj₁ hgmem₁ hgcard₁ hC₁ hCbd₁ hCexp₁ hωne₁ hωne'₁ hexp₁
  exact H Θ (hinterior ε hε)

end ExtractedGapForms

end BranchDominance

end ForgacsTran
