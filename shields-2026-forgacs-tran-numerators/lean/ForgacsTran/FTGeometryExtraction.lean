/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib
import ForgacsTran.Geometry
import ForgacsTran.Cluster

/-!
# `thm:FT-geometry` — the half our paper proves

`thm:FT-geometry` is two things joined.  Its proof reads: "The existence, strict
monotonicity, and endpoint limits of `τ` and `z` are established in
Lemmas~2--6 of `\cite{Forgacs2017RationalDenominator}`.  The minimum-modulus
assertion is `\cite[Props.~1--2]{Forgacs2017RationalDenominator}`. ... The
endpoint expansions are the second and third cases in the proof of
`\cite[Prop.~3]{Forgacs2017RationalDenominator}`.  **We extract the uniform
separation asserted above.**"

So the parametrization, the minimum-modulus property and the endpoint expansions
are the cited work's; the **uniform separation is ours**, and it is what this
module proves.  The cited half is stated here as named hypotheses in
Forgács--Tran's own vocabulary, so that the modules formalizing them plug in
without a shim.

## Main statements

* `ft_endpoint_linear_gap` — **`eq:endpoint-linear-gap`.**  From Prop. 3's
  endpoint expansion `ζ_j(δ) = 1 + c_jδ + O(δ^2)` with
  `c_j = (cos(π/ρ) - Reω_j)/sin(π/ρ)` and
  `ω_j = e^{(2j-1)π i/ρ}`, the single uniform gap
  `|ζ_j(δ)| ≥ 1 + c_0δ` over the whole nonprincipal cluster and
  all small `δ`.  The positivity of each `c_j` is
  `Geometry.endpoint_linear_coeff_pos`, which needs only `ω_j^ρ = -1`
  and `ω_j ≠ e^{± iπ/ρ}`; the passage from pointwise positivity to
  one constant is `Geometry.exists_endpoint_linear_gap`, and finiteness of the
  cluster is what makes it possible.
* `ft_endpoint_fixed_gap_of_pointwise` — **`eq:endpoint-fixed-gap`.**  The same
  step for the zeros *outside* the cluster, where the gap does not close: a
  strict pointwise gap at every member of a finite family is a single fixed
  `c_*`.

## Implementation notes

Sorry-free.

## References

Formalizes `../shields-2026-forgacs-tran-numerators.tex`, «Spectral geometry,
residues, and the principal amplitude» (`sec:geometry`, `subsec:FT-geometry`,
`thm:FT-geometry`, `eq:endpoint-linear-gap`, `eq:endpoint-fixed-gap`).

## Tags

Forgacs-Tran geometry, minimum modulus, denominator pencil
-/

namespace ForgacsTran

open Complex

/-- **Paper `eq:endpoint-linear-gap`, our extraction from `[Prop.~3]`.**  The
nonprincipal members of the endpoint cluster obey one linear modulus gap,
uniformly in the member and in `δ` small.

The hypothesis is Prop. 3's expansion and nothing else: `hexp` says the
normalized root `ζ_j` is `1 + c_jδ` to within `Cδ^2`, with `c_j`
built from `ω_j = e^{(2j-1)π i/ρ}`, and `hωne`/`hωne'` say the index is
nonprincipal.  `ω_j^ρ = -1` is not a hypothesis — `Cluster.clusterOmega_pow`
proves it. -/
theorem ft_endpoint_linear_gap {ρ n : ℕ} (hρ : 2 ≤ ρ) {idx : Fin n → ℕ}
    {ζ : Fin n → ℝ → ℂ} {Cexp : ℝ} (hCexp : 0 ≤ Cexp)
    (hωne : ∀ i : Fin n, clusterOmega ρ (idx i)
      ≠ Complex.exp (((Real.pi / ρ : ℝ) : ℂ) * I))
    (hωne' : ∀ i : Fin n, clusterOmega ρ (idx i)
      ≠ Complex.exp (((-(Real.pi / ρ) : ℝ) : ℂ) * I))
    (hexp : ∀ i : Fin n, ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      ‖ζ i δ - ((1 + ((Real.cos (Real.pi / ρ) - (clusterOmega ρ (idx i)).re)
        / Real.sin (Real.pi / ρ)) * δ : ℝ) : ℂ)‖ ≤ Cexp * δ ^ 2) :
    ∃ c₀ > (0 : ℝ), ∃ δ₀ > (0 : ℝ), ∀ i : Fin n, ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      1 + c₀ * δ ≤ ‖ζ i δ‖ := by
  have hρ1 : 1 ≤ ρ := by omega
  obtain ⟨c₀, hc₀, δ₀, hδ₀, hgap⟩ :=
    exists_endpoint_linear_gap (J := (Finset.univ : Finset (Fin n))) (ζ := ζ)
      (cf := fun i => (Real.cos (Real.pi / ρ) - (clusterOmega ρ (idx i)).re)
        / Real.sin (Real.pi / ρ))
      hCexp (fun i _ => endpoint_linear_coeff_pos hρ (clusterOmega_pow hρ1 _)
        (hωne i) (hωne' i)) (fun i _ => hexp i)
  exact ⟨c₀, hc₀, δ₀, hδ₀, fun i δ hδ hδ₀' => hgap i (Finset.mem_univ i) δ hδ hδ₀'⟩

/-- **Paper `eq:endpoint-fixed-gap`, our extraction.**  Outside the retained
cluster the modulus gap does not close at the endpoint, and a strict gap at every
member of a finite family is one fixed constant.  Finiteness is what makes the
minimum positive; nothing else is used. -/
theorem ft_endpoint_fixed_gap_of_pointwise {ι : Type*} {J : Finset ι} {m : ι → ℝ}
    (hm : ∀ j ∈ J, 1 < m j) :
    ∃ cstar > (0 : ℝ), ∀ j ∈ J, 1 + cstar ≤ m j := by
  classical
  rcases J.eq_empty_or_nonempty with rfl | hJ
  · exact ⟨1, one_pos, by simp⟩
  · refine ⟨J.inf' hJ m - 1, ?_, fun j hj => ?_⟩
    · have : 1 < J.inf' hJ m := (Finset.lt_inf'_iff hJ).2 hm
      linarith
    · have : J.inf' hJ m ≤ m j := Finset.inf'_le _ hj
      linarith


end ForgacsTran
