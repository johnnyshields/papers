/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib
import ForgacsTran.EndpointDominance

/-!
# Weighted principal-pair dominance, assembled at the paper's objects

## References

Formalizes `../shields-2026-forgacs-tran-numerators.tex`, «Principal-pair
dominance and the fixed-numerator theorem» (`sec:dominance`,
`subsec:weighted-dominance`, `thm:weighted-dominance`, `eq:dominance-bound`,
`eq:retained-range`, `eq:interior-relative-remainder`).

## Tags

principal-pair dominance, assembly, weight polynomial
-/

namespace ForgacsTran

/-! ### The compact interior -/

/-- **Paper `eq:interior-relative-remainder`, packaged.**  On the retained
interior — the compact subinterval with the amplitude windows
`eq:amplitude-deletion` removed — the contour remainder `Cσ^M` sits below
half the amplitude for all large `M`.  The conclusion is exactly the `hmid`
hypothesis of `WeightedDominance.exists_dominance_threshold`.

`hbd` is supplied at the paper's objects by
`EndpointDominance.interior_remainder_bound`, whose retained cluster is the
principal pair alone; `hamp` is `lem:amplitude-divisor`'s local form together
with the deletion `eq:amplitude-deletion`, which is what makes the exponent
`c = \tfrac12log(1/σ)` admissible. -/
theorem exists_interior_dominance_of_bound {ε b σ Ccont Amin : ℝ} {Θ : ℕ → Set ℝ}
    {Rrem : ℕ → ℝ → ℝ} {Wamp : ℝ → ℝ}
    (hσ0 : 0 < σ) (hσ1 : σ < 1) (hAmin : 0 < Amin)
    (hbd : ∀ (M : ℕ) (θ : ℝ), ε ≤ θ → θ ≤ b - ε → θ ∉ Θ M → |Rrem M θ| ≤ Ccont * σ ^ M)
    (hamp : ∀ (M : ℕ) (θ : ℝ), ε ≤ θ → θ ≤ b - ε → θ ∉ Θ M →
      Amin * Real.exp (-((-Real.log σ) / 2) * M) ≤ Wamp θ) :
    ∃ M₃ : ℕ, ∀ M : ℕ, M₃ ≤ M → ∀ θ : ℝ,
      ε ≤ θ → θ ≤ b - ε → θ ∉ Θ M → |Rrem M θ| ≤ Wamp θ / 2 := by
  obtain ⟨M₃, hM₃⟩ := exists_interior_dominance (C := Ccont) hσ0 hσ1 hAmin
  exact ⟨M₃, fun M hM θ h1 h2 h3 =>
    hM₃ (Wamp θ) (Rrem M θ) M hM (hbd M θ h1 h2 h3) (hamp M θ h1 h2 h3)⟩

/-! ### The theorem -/

/-- **Paper `thm:weighted-dominance`, with the threshold `h` an input.**  The
paper's `h` depends on the denominator alone, so it cannot be chosen after the
weight: a threshold produced inside the statement sits under the weight's binder
and the resulting `M₀` is no longer the paper's `M_0(Q,r,B)` against a
`B`-independent `h`.  Here `h` is a parameter, constrained only by the two
cluster hypotheses `hcl₀` and `hcl₁`, whose statements mention no weight data —
they are `WeightedDominance.exists_cluster_threshold`'s conclusion at the two
endpoint gap rates.

`weighted_dominance` is this with `h` produced from those two, and is what
consumers written against the bundled form keep using.

**Containment.**  No hypothesis mentions both `Rrem` and `Θ` together with the
cluster data: `hcl₀`, `hcl₁` are about sums over `Fin n₀`, `Fin n₁` at abstract
amplitudes and gaps, and the regional supplies are about `Rrem` alone. -/
theorem weighted_dominance_of_threshold {n₀ n₁ : ℕ} {p₀ p₁ : ℕ}
    {b ε h : ℝ} {Θ : ℕ → Set ℝ} {Rrem : ℕ → ℝ → ℝ} {Wamp : ℝ → ℝ}
    {A₀ c₀ C₀ σ₀ : ℝ} {Wf₀ ζ₀ : ℝ → Fin n₀ → ℝ}
    {A₁ c₁ C₁ σ₁ : ℝ} {Wf₁ ζ₁ : ℝ → Fin n₁ → ℝ}
    {AI CI σI : ℝ}
    (hε : 0 < ε) (hhpos : 0 < h)
    -- the lower endpoint
    (hcl₀ : ∀ (A ζ' : Fin n₀ → ℝ) (θ W : ℝ), 0 < θ → θ ≤ ε → 0 ≤ W →
      (∀ i ∈ (Finset.univ : Finset (Fin n₀)), |A i| ≤ 2 * W) →
      (∀ i ∈ (Finset.univ : Finset (Fin n₀)), 1 + c₀ * θ ≤ ζ' i) →
        ∀ M : ℕ, h ≤ (M : ℝ) * θ →
          ∑ i ∈ (Finset.univ : Finset (Fin n₀)), |A i| * (ζ' i ^ (M + 1))⁻¹ ≤ 1 / 4 * W)
    (hA₀ : 0 < A₀) (hC₀ : 0 ≤ C₀) (hσ₀0 : 0 ≤ σ₀) (hσ₀1 : σ₀ < 1)
    (hamp₀ : ∀ θ : ℝ, 0 < θ → θ ≤ ε → A₀ * θ ^ p₀ ≤ Wamp θ)
    (hCW₀ : ∀ θ : ℝ, 0 < θ → θ ≤ ε → ∀ i, |Wf₀ θ i| ≤ 2 * Wamp θ)
    (hgap₀ : ∀ θ : ℝ, 0 < θ → θ ≤ ε → ∀ i, 1 + c₀ * θ ≤ ζ₀ θ i)
    (hsplit₀ : ∀ (M : ℕ) (θ : ℝ), 0 < θ → θ ≤ ε →
      |Rrem M θ| ≤ (∑ i, |Wf₀ θ i| * (ζ₀ θ i ^ (M + 1))⁻¹) + C₀ * σ₀ ^ M)
    -- the upper endpoint, in `η = b - θ`
    (hcl₁ : ∀ (A ζ' : Fin n₁ → ℝ) (η W : ℝ), 0 < η → η ≤ ε → 0 ≤ W →
      (∀ i ∈ (Finset.univ : Finset (Fin n₁)), |A i| ≤ 2 * W) →
      (∀ i ∈ (Finset.univ : Finset (Fin n₁)), 1 + c₁ * η ≤ ζ' i) →
        ∀ M : ℕ, h ≤ (M : ℝ) * η →
          ∑ i ∈ (Finset.univ : Finset (Fin n₁)), |A i| * (ζ' i ^ (M + 1))⁻¹ ≤ 1 / 4 * W)
    (hA₁ : 0 < A₁) (hC₁ : 0 ≤ C₁) (hσ₁0 : 0 ≤ σ₁) (hσ₁1 : σ₁ < 1)
    (hamp₁ : ∀ η : ℝ, 0 < η → η ≤ ε → A₁ * η ^ p₁ ≤ Wamp (b - η))
    (hCW₁ : ∀ η : ℝ, 0 < η → η ≤ ε → ∀ i, |Wf₁ (b - η) i| ≤ 2 * Wamp (b - η))
    (hgap₁ : ∀ η : ℝ, 0 < η → η ≤ ε → ∀ i, 1 + c₁ * η ≤ ζ₁ (b - η) i)
    (hsplit₁ : ∀ (M : ℕ) (η : ℝ), 0 < η → η ≤ ε →
      |Rrem M (b - η)| ≤ (∑ i, |Wf₁ (b - η) i| * (ζ₁ (b - η) i ^ (M + 1))⁻¹) + C₁ * σ₁ ^ M)
    -- the compact interior
    (hσI0 : 0 < σI) (hσI1 : σI < 1) (hAI : 0 < AI)
    (hbdI : ∀ (M : ℕ) (θ : ℝ), ε ≤ θ → θ ≤ b - ε → θ ∉ Θ M → |Rrem M θ| ≤ CI * σI ^ M)
    (hampI : ∀ (M : ℕ) (θ : ℝ), ε ≤ θ → θ ≤ b - ε → θ ∉ Θ M →
      AI * Real.exp (-((-Real.log σI) / 2) * M) ≤ Wamp θ) :
    ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M → ∀ θ : ℝ,
      h / M ≤ θ → θ ≤ b - h / M → θ ∉ Θ M → |Rrem M θ| ≤ Wamp θ / 2 :=
  exists_dominance_threshold_of_threshold hε hhpos
    (exists_endpoint_dominance_of_split_of_threshold hA₀ hC₀ hσ₀0 hσ₀1 hhpos hcl₀
      hamp₀ hCW₀ hgap₀ hsplit₀)
    (exists_upper_endpoint_dominance_of_split_of_threshold hA₁ hC₁ hσ₁0 hσ₁1 hhpos hcl₁
      hamp₁ hCW₁ hgap₁ hsplit₁)
    (exists_interior_dominance_of_bound hσI0 hσI1 hAI hbdI hampI)


/-- **Paper `thm:weighted-dominance`.**  There is an `h > 0` and, for the fixed
weight, an `M₀`, such that `|R_M(θ)| ≤ \tfrac12|W(θ)|` throughout the
retained range `h/M ≤ θ ≤ π/r - h/M` off the amplitude windows
`⋃_jΘ_{j,M}` — `eq:dominance-bound` on `eq:retained-range`.

The three regional supplies are the paper's own three: the lower endpoint with
its `ρ - 2` nonprincipal cluster members, the upper endpoint with its `r - 2`,
and the compact interior where the retained cluster is the principal pair alone.
Each is stated with its own constants, because the paper's are different
(`c_0` against `c_1`, and different rates `σ`).

At the paper's objects the four endpoint supplies come from
`Cluster.eventually_cluster_amplitude_le` (`C_W = 2`, derived),
`Amplitude.amplitude_endpoint_form` (`Aθ^p ≤ |W|`),
`thm:FT-geometry`'s `eq:endpoint-linear-gap` (cited), and
`EndpointDominance.endpoint_remainder_split` (derived); the interior's two come
from `EndpointDominance.interior_remainder_bound` (derived) and the local
amplitude bound off the deleted windows.

`h` is the larger of the two endpoint thresholds and `M₀` is large enough that
`h/M ≤ ε`, which is what makes the three regions cover the range.  Because the
threshold is chosen here, it sits under the weight's binder; callers needing the
paper's `h = h(Q,r)` take `weighted_dominance_of_threshold` instead. -/
theorem weighted_dominance {n₀ n₁ : ℕ} {p₀ p₁ : ℕ}
    {b ε : ℝ} {Θ : ℕ → Set ℝ} {Rrem : ℕ → ℝ → ℝ} {Wamp : ℝ → ℝ}
    {A₀ c₀ C₀ σ₀ : ℝ} {Wf₀ ζ₀ : ℝ → Fin n₀ → ℝ}
    {A₁ c₁ C₁ σ₁ : ℝ} {Wf₁ ζ₁ : ℝ → Fin n₁ → ℝ}
    {AI CI σI : ℝ}
    (hε : 0 < ε)
    -- the lower endpoint
    (hc₀ : 0 < c₀) (hA₀ : 0 < A₀) (hC₀ : 0 ≤ C₀) (hσ₀0 : 0 ≤ σ₀) (hσ₀1 : σ₀ < 1)
    (hamp₀ : ∀ θ : ℝ, 0 < θ → θ ≤ ε → A₀ * θ ^ p₀ ≤ Wamp θ)
    (hCW₀ : ∀ θ : ℝ, 0 < θ → θ ≤ ε → ∀ i, |Wf₀ θ i| ≤ 2 * Wamp θ)
    (hgap₀ : ∀ θ : ℝ, 0 < θ → θ ≤ ε → ∀ i, 1 + c₀ * θ ≤ ζ₀ θ i)
    (hsplit₀ : ∀ (M : ℕ) (θ : ℝ), 0 < θ → θ ≤ ε →
      |Rrem M θ| ≤ (∑ i, |Wf₀ θ i| * (ζ₀ θ i ^ (M + 1))⁻¹) + C₀ * σ₀ ^ M)
    -- the upper endpoint, in `η = b - θ`
    (hc₁ : 0 < c₁) (hA₁ : 0 < A₁) (hC₁ : 0 ≤ C₁) (hσ₁0 : 0 ≤ σ₁) (hσ₁1 : σ₁ < 1)
    (hamp₁ : ∀ η : ℝ, 0 < η → η ≤ ε → A₁ * η ^ p₁ ≤ Wamp (b - η))
    (hCW₁ : ∀ η : ℝ, 0 < η → η ≤ ε → ∀ i, |Wf₁ (b - η) i| ≤ 2 * Wamp (b - η))
    (hgap₁ : ∀ η : ℝ, 0 < η → η ≤ ε → ∀ i, 1 + c₁ * η ≤ ζ₁ (b - η) i)
    (hsplit₁ : ∀ (M : ℕ) (η : ℝ), 0 < η → η ≤ ε →
      |Rrem M (b - η)| ≤ (∑ i, |Wf₁ (b - η) i| * (ζ₁ (b - η) i ^ (M + 1))⁻¹) + C₁ * σ₁ ^ M)
    -- the compact interior
    (hσI0 : 0 < σI) (hσI1 : σI < 1) (hAI : 0 < AI)
    (hbdI : ∀ (M : ℕ) (θ : ℝ), ε ≤ θ → θ ≤ b - ε → θ ∉ Θ M → |Rrem M θ| ≤ CI * σI ^ M)
    (hampI : ∀ (M : ℕ) (θ : ℝ), ε ≤ θ → θ ≤ b - ε → θ ∉ Θ M →
      AI * Real.exp (-((-Real.log σI) / 2) * M) ≤ Wamp θ) :
    ∃ h > (0 : ℝ), ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M → ∀ θ : ℝ,
      h / M ≤ θ → θ ≤ b - h / M → θ ∉ Θ M → |Rrem M θ| ≤ Wamp θ / 2 :=
  exists_dominance_threshold hε
    (exists_endpoint_dominance_of_split hc₀ hε.le hA₀ hC₀ hσ₀0 hσ₀1 hamp₀ hCW₀ hgap₀ hsplit₀)
    (exists_upper_endpoint_dominance_of_split hc₁ hε.le hA₁ hC₁ hσ₁0 hσ₁1 hamp₁ hCW₁ hgap₁
      hsplit₁)
    (exists_interior_dominance_of_bound hσI0 hσI1 hAI hbdI hampI)


end ForgacsTran
