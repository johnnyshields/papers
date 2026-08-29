/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import ForgacsTran.DominanceFTBranch

/-!
# `thm:weighted-dominance` with the smallest zero multiple

The two `ρ ≥ 2` forms of `DominanceFTBranch`'s theorem, in the shape the
composition layer supplies `hρ`.  Nothing is proved here that is not proved
there: each is that theorem with the four `0 < n₀ →` guards discharged from
`2 ≤ ρ` alone, and the pair exists because the two callers differ in the order
they fix `ε` and `Θ`.

## Main statements

* `weighted_dominance_of_branch` — the `ρ ≥ 2` specialization of
  `weighted_dominance_of_branch_any_multiplicity`, with `Θ` fixed first and the
  interior data demanded at every `e`.
* `weighted_dominance_of_branch_at` — the specialization of
  `weighted_dominance_of_branch_any_multiplicity_at`, which hands the interior
  parameter back: `ε` is produced before `Θ` is chosen, so the deleted family may
  be built from that `ε`'s own `σ`.  `weighted_dominance_of_branch` cannot offer
  that, because there `Θ` is fixed first.

## Implementation notes

`hamp`, `hCW`, `hsplit` and `hint` are absent from both binder lists: they are
applied, not assumed, and so are `eq:endpoint-linear-gap` and
`eq:lower-residue-ratio` — both are our paper's extractions from Prop. 3, not
Prop. 3 itself, so what is assumed in their place is the endpoint *expansion*
`ζ_j(δ) = 1 + c_jδ + O(δ²)` and the leading behavior of `B` and of `∂_tD` along
each branch.  What survives is the Forgács--Tran branch data, the uniform contour
bounds, and the definition of the deleted windows.

Sorry-free.

## References

Formalizes `../shields-2026-forgacs-tran-numerators.tex`, «Principal-pair
dominance and the fixed-numerator theorem» (`sec:dominance`,
`subsec:weighted-dominance`, `thm:weighted-dominance`).

## Tags

weighted dominance, multiple smallest zero, Forgacs-Tran branch
-/

namespace ForgacsTran

open Polynomial Complex

/-- **`thm:weighted-dominance` with the smallest zero assumed multiple.**  The
`ρ ≥ 2` specialization of `weighted_dominance_of_branch_any_multiplicity`, kept
because the composition layer supplies `hρ` in this form. -/
theorem weighted_dominance_of_branch {Q B : Polynomial ℂ}
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
        ftRemainder Q B r z τ M θ ≤ ftPrincipalAmp Q B r z τ θ / 2 :=
  weighted_dominance_of_branch_any_multiplicity (hρ := fun _ => hρ)
      (hcB₀ := fun _ => hcB₀) (hcQ₀ := fun _ => hcQ₀) (hBp₀ := fun _ => hBp₀)
      (hEp₀ := fun _ => hEp₀) (hQ := hQ) (hB := hB)
      (hB0 := hB0) (hr := hr) (hQ0 := hQ0) (n₀ := n₀) (n₁ := n₁) (g₀ := g₀) (g₁ := g₁)
      (sfun₀ := sfun₀) (sfun₁ := sfun₁) (x₁ := x₁) (hx₁ := hx₁) (ρ := ρ) (te₀ := te₀)
      (γe₀ := γe₀) (hte₀ := hte₀) (hγe₀ := hγe₀) (hγ0₀ := hγ0₀) (hγd₀ := hγd₀) (hk₀ := hk₀)
      (hrootev₀ := hrootev₀) (idx₀ := idx₀) (jp₀ := jp₀) (νB₀ := νB₀) (cB₀ := cB₀) (cQ₀ := cQ₀)
      (hBj₀ := hBj₀) (hEj₀ := hEj₀)
      (R₀ := R₀) (τmax₀ := τmax₀) (σ₀ := σ₀) (e₀ := e₀) (hR₀ := hR₀) (hσ₀ := hσ₀) (hσ₀1 := hσ₀1)
      (he₀ := he₀) (hτpos₀ := hτpos₀) (hτle₀ := hτle₀) (hroot₀ := hroot₀) (hsimple₀ := hsimple₀)
      (haR₀ := haR₀) (huniq₀ := huniq₀) (hrootplus₀ := hrootplus₀) (hne₀ := hne₀)
      (hginj₀ := hginj₀) (hgmem₀ := hgmem₀) (hgcard₀ := hgcard₀) (C₀ := C₀) (hC₀ := hC₀)
      (hCbd₀ := hCbd₀) (Cexp₀ := Cexp₀) (hCexp₀ := hCexp₀) (hωne₀ := hωne₀) (hωne'₀ := hωne'₀)
      (hexp₀ := hexp₀) (p₁ := p₁) (A₁ := A₁) (hA₁ := hA₁) (hamp₁ := hamp₁) (idx₁ := idx₁)
      (L₁ := L₁) (hn₁r := hn₁r) (hL₁ := hL₁) (hratio₁ := hratio₁) (R₁ := R₁) (τmax₁ := τmax₁)
      (σ₁ := σ₁) (e₁ := e₁) (hR₁ := hR₁) (hσ₁ := hσ₁) (hσ₁1 := hσ₁1) (he₁ := he₁)
      (hτpos₁ := hτpos₁) (hτle₁ := hτle₁) (hroot₁ := hroot₁) (hsimple₁ := hsimple₁)
      (haR₁ := haR₁) (huniq₁ := huniq₁) (hrootplus₁ := hrootplus₁) (hne₁ := hne₁)
      (hginj₁ := hginj₁) (hgmem₁ := hgmem₁) (hgcard₁ := hgcard₁) (C₁ := C₁) (hC₁ := hC₁)
      (hCbd₁ := hCbd₁) (Cexp₁ := Cexp₁) (hCexp₁ := hCexp₁) (hωne₁ := hωne₁) (hωne'₁ := hωne'₁)
      (hexp₁ := hexp₁) (hinterior := hinterior)


/-- **`thm:weighted-dominance` with the smallest zero assumed multiple, and the
interior parameter handed back.**  The `ρ ≥ 2` specialization of
`weighted_dominance_of_branch_any_multiplicity_at`, in the shape the composition
layer supplies `hρ`.

`ε` is produced before `Θ` is chosen, so the deleted family may be built from
that `ε`'s own `σ` — which `weighted_dominance_of_branch` cannot offer, because
there `Θ` is fixed first and the interior data is demanded at every `e`. -/
theorem weighted_dominance_of_branch_at {Q B : Polynomial ℂ}
    (hQ : HasRealCoeffs Q) (hB : HasRealCoeffs B) (hB0 : B ≠ 0)
    {r : ℕ} (hr : 1 ≤ r) (hQ0 : Q.eval 0 ≠ 0)
    {b : ℝ} {z τ : ℝ → ℝ}
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
    :
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
          ftRemainder Q B r z τ M θ ≤ ftPrincipalAmp Q B r z τ θ / 2 :=
  weighted_dominance_of_branch_any_multiplicity_at (hρ := fun _ => hρ)
      (hcB₀ := fun _ => hcB₀) (hcQ₀ := fun _ => hcQ₀) (hBp₀ := fun _ => hBp₀)
      (hEp₀ := fun _ => hEp₀) (hQ := hQ) (hB := hB)
      (hB0 := hB0) (hr := hr) (hQ0 := hQ0) (n₀ := n₀) (n₁ := n₁) (g₀ := g₀) (g₁ := g₁)
      (sfun₀ := sfun₀) (sfun₁ := sfun₁) (x₁ := x₁) (hx₁ := hx₁) (ρ := ρ) (te₀ := te₀)
      (γe₀ := γe₀) (hte₀ := hte₀) (hγe₀ := hγe₀) (hγ0₀ := hγ0₀) (hγd₀ := hγd₀) (hk₀ := hk₀)
      (hrootev₀ := hrootev₀) (idx₀ := idx₀) (jp₀ := jp₀) (νB₀ := νB₀) (cB₀ := cB₀) (cQ₀ := cQ₀)
      (hBj₀ := hBj₀) (hEj₀ := hEj₀)
      (R₀ := R₀) (τmax₀ := τmax₀) (σ₀ := σ₀) (e₀ := e₀) (hR₀ := hR₀) (hσ₀ := hσ₀) (hσ₀1 := hσ₀1)
      (he₀ := he₀) (hτpos₀ := hτpos₀) (hτle₀ := hτle₀) (hroot₀ := hroot₀) (hsimple₀ := hsimple₀)
      (haR₀ := haR₀) (huniq₀ := huniq₀) (hrootplus₀ := hrootplus₀) (hne₀ := hne₀)
      (hginj₀ := hginj₀) (hgmem₀ := hgmem₀) (hgcard₀ := hgcard₀) (C₀ := C₀) (hC₀ := hC₀)
      (hCbd₀ := hCbd₀) (Cexp₀ := Cexp₀) (hCexp₀ := hCexp₀) (hωne₀ := hωne₀) (hωne'₀ := hωne'₀)
      (hexp₀ := hexp₀) (p₁ := p₁) (A₁ := A₁) (hA₁ := hA₁) (hamp₁ := hamp₁) (idx₁ := idx₁)
      (L₁ := L₁) (hn₁r := hn₁r) (hL₁ := hL₁) (hratio₁ := hratio₁) (R₁ := R₁) (τmax₁ := τmax₁)
      (σ₁ := σ₁) (e₁ := e₁) (hR₁ := hR₁) (hσ₁ := hσ₁) (hσ₁1 := hσ₁1) (he₁ := he₁)
      (hτpos₁ := hτpos₁) (hτle₁ := hτle₁) (hroot₁ := hroot₁) (hsimple₁ := hsimple₁)
      (haR₁ := haR₁) (huniq₁ := huniq₁) (hrootplus₁ := hrootplus₁) (hne₁ := hne₁)
      (hginj₁ := hginj₁) (hgmem₁ := hgmem₁) (hgcard₁ := hgcard₁) (C₁ := C₁) (hC₁ := hC₁)
      (hCbd₁ := hCbd₁) (Cexp₁ := Cexp₁) (hCexp₁ := hCexp₁) (hωne₁ := hωne₁) (hωne'₁ := hωne'₁)
      (hexp₁ := hexp₁)

end ForgacsTran
