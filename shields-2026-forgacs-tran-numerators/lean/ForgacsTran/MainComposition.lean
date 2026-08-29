/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib
import ForgacsTran.MainClauses

/-!
# `thm:main` over the Forgács–Tran branch, composed

## References

Formalizes `../shields-2026-forgacs-tran-numerators.tex`, «Principal-pair
dominance and the fixed-numerator theorem» (`sec:dominance`, `subsec:proof`,
`thm:weighted-dominance`, `eq:retained-range`, `thm:main`).

## Tags

main theorem, Forgacs-Tran branch, composition
-/

namespace ForgacsTran

open Set Polynomial Complex

/-- **One retained component of `eq:Omega-M`, at one index.**  What a caller has to
exhibit about the subarc the phase count is run on: it sits inside the retained
range `h/M ≤ θ ≤ bb - h/M` and off the amplitude windows `Θ M`, the branch data of
`thm:FT-geometry` holds on it, `eq:phase-derivative-bound` gives the `κ`, the phase
turns by at least `π`, and the degree sits below that turning plus the defect.

**This is `MainClauses.FTBranchData` with one clause traded for another.**  The two
lists are the same twelve conditions except that `FTBranchData` carries
`eq:dominance-bound` on the component while this carries the window membership that
puts the component inside the range where `thm:weighted-dominance` already proved it.
Trading the second for the first is the whole of `ftBranchData_of_dominance`, and
naming both sides is what makes that one line rather than two walls of binders. -/
def FTRetainedComponent (Q B : Polynomial ℂ) (r : ℕ) (z τ : ℝ → ℝ) (P : Polynomial ℝ)
    (M : ℕ) (aI bI : ℝ) (C : ℕ) (h bb : ℝ) (Θ : ℕ → Set ℝ) : Prop :=
  ∃ (a b' L : ℝ) (ψ Φ : ℝ → ℝ),
    a ≤ b' ∧
    (∀ θ ∈ Icc a b', h / M ≤ θ ∧ θ ≤ bb - h / M ∧ θ ∉ Θ M) ∧
    (∀ θ ∈ Icc a b', 0 < τ θ) ∧
    StrictMonoOn z (Icc a b') ∧
    (∀ θ ∈ Icc a b', z θ ∈ Ioo aI bI) ∧
    (∀ θ ∈ Icc a b', ftAmp Q B r ((z θ : ℝ) : ℂ) (ftPrincipal τ θ) ≠ 0) ∧
    (∀ θ ∈ Icc a b', ftAmp Q B r ((z θ : ℝ) : ℂ) (ftPrincipal τ θ)
      = ((ftPrincipalAmp Q B r z τ θ : ℝ) : ℂ) * Complex.exp ((ψ θ : ℂ) * Complex.I)) ∧
    (∀ θ ∈ Icc a b', Φ θ = ((M : ℝ) + 1) * θ - ψ θ) ∧
    (∃ dψ : ℝ → ℝ, ∃ κ : ℝ, (∀ θ ∈ Icc a b', HasDerivAt ψ (dψ θ) θ) ∧
      (∀ θ ∈ Icc a b', |dψ θ| ≤ κ) ∧ κ < (M : ℝ) + 1) ∧
    Real.pi ≤ L ∧ L ≤ Φ b' - Φ a ∧
    ((P.map (algebraMap ℝ ℂ)).natDegree : ℝ) ≤ L / Real.pi - 2 + C

/-- **The retained range meets the component.**  `thm:weighted-dominance` concludes
`eq:dominance-bound` on the whole retained range `h/M ≤ θ ≤ b - h/M` off
the amplitude windows, at every index past `M₀`; `FTBranchData` wants it on one
component `[a,b']` at one index.  A component contained in the retained range is
what bridges them, and that containment is the only new hypothesis.

Every other field of `FTBranchData` is `thm:FT-geometry` on the component
(`τ > 0`, `z` strictly increasing into `I_{Q,r}`, the amplitude nonvanishing
with an argument branch `ψ`), `eq:phase-derivative-bound` (the `κ` with
`κ < M+1`, which is why the threshold in `M` sits in the statement), the
turning `π ≤ L ≤ Φ(b') - Φ(a)`, and the degree comparison of
`prop:angular-discrepancy`.  **No dominance hypothesis remains**: the field is
filled from `hdom`. -/
theorem ftBranchData_of_dominance {Q B : Polynomial ℂ} {r : ℕ} {z τ : ℝ → ℝ}
    {P : ℕ → Polynomial ℝ} {aI bI : ℝ} {C m0 M₀ : ℕ} {Θ : ℕ → Set ℝ} {bb h : ℝ}
    (hm0 : M₀ ≤ m0)
    (hdom : ∀ M : ℕ, M₀ ≤ M → ∀ θ : ℝ, h / M ≤ θ → θ ≤ bb - h / M → θ ∉ Θ M →
      ftRemainder Q B r z τ M θ ≤ ftPrincipalAmp Q B r z τ θ / 2)
    (hcomp : ∀ M : ℕ, m0 ≤ M →
      FTRetainedComponent Q B r z τ (P M) M aI bI C h bb Θ) :
    ∀ M : ℕ, m0 ≤ M → FTBranchData Q B r z τ (P M) M aI bI C := by
  intro M hM
  obtain ⟨a, b', L, ψ, Φ, hab, hsub, hτ, hzmono, hzS, hWne, hpolar, hΦdef, hderiv,
    hL, hLΦ, hdeg⟩ := hcomp M hM
  exact ⟨a, b', L, ψ, Φ, hab, hτ, hzmono, hzS, hWne, hpolar, hΦdef, hderiv, hL, hLΦ,
    fun θ hθ => hdom M (le_trans hm0 hM) θ (hsub θ hθ).1 (hsub θ hθ).2.1 (hsub θ hθ).2.2,
    hdeg⟩

/-- **Paper `thm:main` clauses 1 and 2, over the branch, with no dominance
hypothesis anywhere in the chain.**  `DominanceFT.weighted_dominance_of_branch`
supplies `eq:dominance-bound` on the retained range;
`ftBranchData_of_dominance` restricts it to a component;
`MainClauses.main_of_ftBranch` runs the phase count, builds the interior zero set
and both `exceptionalRoots` bounds off it.

What is left is the Forgács--Tran branch of `thm:FT-geometry` — which the
manuscript cites from `Forgacs2017RationalDenominator` rather than proving —
together with the endpoint expansion `ζ_j(δ) = 1 + c_jδ + O(δ^2)`
of `[Prop.~3]`, the separating circle, the definition of the deleted windows,
and, per component, the phase-derivative bound and the turning.
`eq:endpoint-linear-gap` is **not** among them, and neither is the contour
supremum `C_Γ`: the first is the manuscript's own extraction from that
expansion, the second is produced by compactness, and both are derived. -/
theorem main_of_ftDominance {Q B : Polynomial ℂ} {r : ℕ} {z τ : ℝ → ℝ}
    {P : ℕ → Polynomial ℝ} {aI bI : ℝ} {C m0 M₀ : ℕ} {Θ : ℕ → Set ℝ} {bb h : ℝ}
    (hP : ∀ M, (P M).map (algebraMap ℝ ℂ) = ftCoeffPoly Q B r M)
    (hne : ∀ M, m0 ≤ M → (P M).map (algebraMap ℝ ℂ) ≠ 0)
    (haI : 0 ≤ aI) (hm0 : M₀ ≤ m0)
    (hdom : ∀ M : ℕ, M₀ ≤ M → ∀ θ : ℝ, h / M ≤ θ → θ ≤ bb - h / M → θ ∉ Θ M →
      ftRemainder Q B r z τ M θ ≤ ftPrincipalAmp Q B r z τ θ / 2)
    (hcomp : ∀ M : ℕ, m0 ≤ M →
      FTRetainedComponent Q B r z τ (P M) M aI bI C h bb Θ) :
    ∀ M, m0 ≤ M →
      (∃ Z : Finset ℂ, ((P M).map (algebraMap ℝ ℂ)).natDegree - C ≤ Z.card ∧
          (∀ w ∈ Z, ((P M).map (algebraMap ℝ ℂ)).IsRoot w) ∧
          (∀ w ∈ Z, w ∈ ftInterval aI bI))
        ∧ (exceptionalRoots ((P M).map (algebraMap ℝ ℂ)) (ftInterval aI bI)).card ≤ C
        ∧ (exceptionalRoots ((P M).map (algebraMap ℝ ℂ)) posRay).card ≤ C :=
  main_of_ftBranch hP hne haI (ftBranchData_of_dominance hm0 hdom hcomp)

/-- **Paper `thm:main`, clauses 1 and 2, over the Forgács--Tran branch alone.**
The whole chain in one statement: `weighted_dominance_of_branch` proves
`eq:dominance-bound` on `eq:retained-range`, `ftBranchData_of_dominance` restricts
it to a retained component, and `MainClauses.main_of_ftBranch` runs the phase
count off it, building the interior zero set and both `exceptionalRoots` bounds.

**No dominance hypothesis appears anywhere.**  What is assumed is the Forgács--Tran
branch of `thm:FT-geometry` — which the manuscript imports from
`Forgacs2017RationalDenominator` rather than proving — the endpoint expansion
`ζ_j(δ) = 1 + c_jδ + O(δ^2)` of `[Prop.~3]` and the leading
behavior of `B` and `∂_tD` along each branch, the separating circle with
the retained cluster strictly inside it and the spectral parameter continuous
across each closed window, the definition of the deleted windows, and, per
component, `eq:phase-derivative-bound` and the turning
`π ≤ L ≤ Φ(b') - Φ(a)`.  None of `eq:endpoint-linear-gap`,
`eq:lower-residue-ratio` and the uniform contour constant `C_Γ` is assumed:
the first two are the manuscript's own extractions from that expansion, the third
its own uniformity sentence, and all three are derived.

`hcomp` is quantified over `h` and the threshold because
`weighted_dominance_of_branch` produces both: the retained range is not known
until the constants are, which is the order `thm:weighted-dominance` fixes them
in.

**Containment.**  The conclusion produces a `Finset ℂ` of interior zeros and
bounds `exceptionalRoots` off `I_{Q,r}` and off `(0,∞)`.  No binder mentions
`exceptionalRoots`, `IsRoot`, `Finset ℂ`, `ftInterval` or `posRay`, so no zero set
and no exceptional count is carried in.  Two binders touch the coefficient
sequence and neither says anything about its zeros: `hPmap` identifies `P_m` with
`ftCoeffPoly`, and `hcomp` compares `deg P_m` with the phase count. -/
theorem main_of_ftBranch_of_geometry {Q B : Polynomial ℂ}
    (hQ : HasRealCoeffs Q) (hB : HasRealCoeffs B) (hB0 : B ≠ 0)
    {r : ℕ} (hr : 1 ≤ r) (hQ0 : Q.eval 0 ≠ 0)
    {b : ℝ} {z τ : ℝ → ℝ} {Θ : ℕ → Set ℝ}
    {n₀ n₁ : ℕ} {g₀ : ℝ → Fin n₀ → ℂ} {g₁ : ℝ → Fin n₁ → ℂ}
    {sfun₀ sfun₁ : ℝ → Finset ℂ}
    {x₁ : ℝ} (hx₁ : 0 < x₁) {ρ : ℕ} (hρ : 2 ≤ ρ)
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
    (hcB₀ : cB₀ ≠ 0) (hcQ₀ : cQ₀ ≠ 0)
    (hBj₀ : ∀ i : Fin n₀, Filter.Tendsto
      (fun δ : ℝ => B.eval (g₀ δ i) / ((δ : ℝ) : ℂ) ^ (νB₀ : ℤ))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (cB₀ * clusterAlpha x₁ ρ (idx₀ i) ^ νB₀)))
    (hBp₀ : Filter.Tendsto
      (fun δ : ℝ => B.eval (ftPrincipal τ δ) / ((δ : ℝ) : ℂ) ^ (νB₀ : ℤ))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (cB₀ * clusterAlpha x₁ ρ jp₀ ^ νB₀)))
    (hEj₀ : ∀ i : Fin n₀, Filter.Tendsto
      (fun δ : ℝ => (derivative (ftDen Q r ((z δ : ℝ) : ℂ))).eval (g₀ δ i)
        / ((δ : ℝ) : ℂ) ^ ((ρ - 1 : ℕ) : ℤ))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (cQ₀ * clusterAlpha x₁ ρ (idx₀ i) ^ (ρ - 1))))
    (hEp₀ : Filter.Tendsto
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
    {C₀ : ℝ} (hC₀ : 0 ≤ C₀)
    (hCbd₀ : ∀ δ : ℝ, 0 < δ → δ ≤ e₀ → ∀ t ∈ Metric.sphere (0 : ℂ) R₀,
      ‖B.eval t / (ftDen Q r ((z δ : ℝ) : ℂ)).eval t‖ ≤ C₀)
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
    {p₁ : ℕ} {A₁ : ℝ} (hA₁ : 0 < A₁)
    (hamp₁ : ∃ e > (0 : ℝ), ∀ η : ℝ, 0 < η → η ≤ e →
      A₁ * η ^ p₁ ≤ ftPrincipalAmp Q B r z τ (b - η))
    -- `eq:lower-residue-ratio` is *not* assumed either: what is taken is the
    -- leading behavior of `B` and of `∂_tD` along each branch, which Taylor at
    -- `x_1` reads off Prop. 3's expansion; the ratio is `Cluster`'s theorem
    -- `eq:upper-residue-ratio`, not a second copy of the lower cluster
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
            / (B.rootMultiplicity (ftPrincipal τ θj)))) ≤ |θ - θj|))
    {Pr : ℕ → Polynomial ℝ} {aI bI : ℝ} {C : ℕ}
    (hPmap : ∀ M, (Pr M).map (algebraMap ℝ ℂ) = ftCoeffPoly Q B r M)
    (haI : 0 ≤ aI)
    (hcomp : ∀ (hh : ℝ) (Mz : ℕ), 0 < hh → ∃ m0 : ℕ, Mz ≤ m0 ∧
      (∀ M, m0 ≤ M → (Pr M).map (algebraMap ℝ ℂ) ≠ 0) ∧
      (∀ M : ℕ, m0 ≤ M →
        FTRetainedComponent Q B r z τ (Pr M) M aI bI C hh b Θ)) :
    ∃ m0 : ℕ, ∀ M, m0 ≤ M →
      (∃ Z : Finset ℂ, ((Pr M).map (algebraMap ℝ ℂ)).natDegree - C ≤ Z.card ∧
          (∀ w ∈ Z, ((Pr M).map (algebraMap ℝ ℂ)).IsRoot w) ∧
          (∀ w ∈ Z, w ∈ ftInterval aI bI))
        ∧ (exceptionalRoots ((Pr M).map (algebraMap ℝ ℂ)) (ftInterval aI bI)).card ≤ C
        ∧ (exceptionalRoots ((Pr M).map (algebraMap ℝ ℂ)) posRay).card ≤ C := by
  obtain ⟨hh, hhpos, Mz, hdomM⟩ :=
    weighted_dominance_of_branch hQ hB hB0 hr hQ0 hx₁ hρ hte₀ hγe₀ hγ0₀ hγd₀ hk₀
      hrootev₀ hcB₀ hcQ₀ hBj₀ hBp₀ hEj₀ hEp₀ hR₀ hσ₀ hσ₀1 he₀ hτpos₀ hτle₀ hroot₀
      hsimple₀ haR₀ huniq₀ hrootplus₀ hne₀ hginj₀ hgmem₀ hgcard₀ hC₀ hCbd₀
      hCexp₀ hωne₀ hωne'₀
      hexp₀ hA₁ hamp₁ hn₁r hL₁ hratio₁ hR₁ hσ₁ hσ₁1
      he₁ hτpos₁ hτle₁ hroot₁ hsimple₁ haR₁ huniq₁ hrootplus₁ hne₁ hginj₁ hgmem₁
      hgcard₁ hC₁ hCbd₁ hCexp₁ hωne₁ hωne'₁ hexp₁ hinterior
  obtain ⟨m0, hm0, hnePr, hcomp'⟩ := hcomp hh Mz hhpos
  exact ⟨m0, main_of_ftDominance hPmap hnePr haI hm0 hdomM hcomp'⟩




end ForgacsTran
