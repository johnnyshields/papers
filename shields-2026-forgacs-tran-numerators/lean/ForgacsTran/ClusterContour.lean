/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import ForgacsTran.ZeroCount
import Shields.Analysis.Complex.CircleDeformation

/-!
# The cluster contour is immaterial

`lem:contour-separation` retains the denominator zeros inside a chosen contour
and integrates every other pole out into `E_M`.  For that to be well defined the
contour must be redrawable: individual residues blow up as two enclosed zeros
collide, and only the grouped contribution stays finite.  That invariance is the
property the whole `sec:dominance` argument leans on.

Stated precisely, it says the contour may be redrawn: any two circles that
enclose the cluster and lie in the same annulus of analyticity give the same
integral, whatever the nodes are doing inside — including repeated nodes, which
is exactly a collision.  That follows from `Shields.circleIntegral_cluster_deform`
applied twice, since both small circles equal the same difference of concentric
integrals.

## Main statements

* `analyticOnNhd_clusterIntegrand` — the paper's integrand
  `B(t)/(c t^(M+1))` is analytic off the origin, which is the analyticity
  hypothesis the lemma needs on an annulus `ρ ≤ |t| ≤ R` with `ρ > 0`.
* `circleIntegral_cluster_indep` — contour independence for a general analytic
  numerator.
* `circleIntegral_cluster_indep_poly` — the two combined, at the paper's own
  integrand `B(t)/(c t^(M+1) ∏ (t - a i))`.

## Implementation notes

**Scope.**  `lem:contour-separation` has a second half — the `O(σ^M)` bound of
`eq:contour-remainder-bound`, in force once `ρ(z) ≤ σ R_Γ` — and that half is *not*
here: the paper applies it through the Forgács–Tran branch `τ(z)`, which the paper takes from
`Forgacs2017RationalDenominator` rather than constructing, so it belongs with the
geometry in `Bridge`.  Nor is the passage from `Q(t) + z t^r` to the node product
`c ∏ (t - a i)` formalized; the node family is a hypothesis here.  Sorry-free.

## References

Formalizes the invariance half of
`../shields-2026-forgacs-tran-numerators.tex`, «Spectral geometry, residues,
and the principal amplitude» (`sec:geometry`, `lem:contour-separation`,
`eq:contour-separated-expansion`).

## Tags

contour independence, cluster, residue
-/

open Complex Metric Set

namespace ForgacsTran

/-- Paper `sec:geometry`, `lem:contour-separation` — the numerator of the
`E_M` term of `eq:contour-separated-expansion`.  `B(t)/(c t^(M+1))` is analytic wherever `t ≠ 0`, so
it is
analytic on any annulus `ρ ≤ |t| ≤ R` with `ρ > 0`, which is the hypothesis the
lemma's contour estimate runs on. -/
theorem analyticOnNhd_clusterIntegrand (B : Polynomial ℂ) {c : ℂ} (hc : c ≠ 0) (M : ℕ) :
    AnalyticOnNhd ℂ (fun t : ℂ => B.eval t / (c * t ^ (M + 1))) {t : ℂ | t ≠ 0} := by
  have hopen : IsOpen {t : ℂ | t ≠ 0} := isOpen_ne
  refine DifferentiableOn.analyticOnNhd (fun t ht => ?_) hopen
  refine DifferentiableAt.differentiableWithinAt ?_
  exact (B.differentiable t).div
    (((differentiable_id.pow (M + 1)).const_mul c) t)
    (mul_ne_zero hc (pow_ne_zero _ ht))

/-- **Paper `sec:geometry`, `lem:contour-separation` — the contour is immaterial.**
Two circles enclosing the same cluster of nodes, both lying in an annulus on
which the numerator is analytic, give the same integral.  The nodes may repeat
in any pattern, so this is precisely the paper's *"invariant under the internal
splitting or collision of the roots"*: nothing here computes an individual
residue, and a collision is just two equal nodes. -/
theorem circleIntegral_cluster_indep {ρ R r₁ r₂ : ℝ} {τ₁ τ₂ : ℂ} {A : Set ℂ}
    (hA : IsOpen A) {h : ℂ → ℂ} (hh : AnalyticOnNhd ℂ h A) (k : ℕ) (a : ℕ → ℂ)
    (hρ : 0 < ρ) (hρR : ρ ≤ R)
    (hAann : closedBall (0 : ℂ) R \ ball (0 : ℂ) ρ ⊆ A)
    (hr₁ : 0 < r₁) (hnode₁ : ∀ i, a i ∈ ball τ₁ r₁)
    (hsmall₁ : closedBall τ₁ r₁ ⊆ ball (0 : ℂ) R \ closedBall (0 : ℂ) ρ)
    (hr₂ : 0 < r₂) (hnode₂ : ∀ i, a i ∈ ball τ₂ r₂)
    (hsmall₂ : closedBall τ₂ r₂ ⊆ ball (0 : ℂ) R \ closedBall (0 : ℂ) ρ) :
    (∮ t in C(τ₁, r₁), h t / ∏ i ∈ Finset.range k, (t - a i))
      = ∮ t in C(τ₂, r₂), h t / ∏ i ∈ Finset.range k, (t - a i) := by
  have h₁ := Shields.circleIntegral_cluster_deform hA hh k a hρ hρR hr₁ hnode₁ hAann hsmall₁
  have h₂ := Shields.circleIntegral_cluster_deform hA hh k a hρ hρR hr₂ hnode₂ hAann hsmall₂
  exact add_left_cancel (h₁.symm.trans h₂)

/-- **Paper `sec:geometry`, `eq:contour-separated-expansion` — contour independence at the
paper's own integrand.**  With the denominator written in root-product form
`Q(t) + z t^r = c ∏ (t - a i)`, the cluster contribution
`-(2πi)⁻¹ ∮ B(t)/(t^(M+1)(Q(t)+z t^r)) dt` does not depend on which circle around
the cluster is used.  The annulus `ρ ≤ |t| ≤ R` avoids the order-`M+1` pole at the
origin, which is what `ρ > 0` is doing. -/
theorem circleIntegral_cluster_indep_poly (B : Polynomial ℂ) {c : ℂ} (hc : c ≠ 0) (M k : ℕ)
    (a : ℕ → ℂ) {ρ R r₁ r₂ : ℝ} {τ₁ τ₂ : ℂ}
    (hρ : 0 < ρ) (hρR : ρ ≤ R)
    (hr₁ : 0 < r₁) (hnode₁ : ∀ i, a i ∈ ball τ₁ r₁)
    (hsmall₁ : closedBall τ₁ r₁ ⊆ ball (0 : ℂ) R \ closedBall (0 : ℂ) ρ)
    (hr₂ : 0 < r₂) (hnode₂ : ∀ i, a i ∈ ball τ₂ r₂)
    (hsmall₂ : closedBall τ₂ r₂ ⊆ ball (0 : ℂ) R \ closedBall (0 : ℂ) ρ) :
    (∮ t in C(τ₁, r₁),
        B.eval t / (c * t ^ (M + 1)) / ∏ i ∈ Finset.range k, (t - a i))
      = ∮ t in C(τ₂, r₂),
        B.eval t / (c * t ^ (M + 1)) / ∏ i ∈ Finset.range k, (t - a i) := by
  have hann : closedBall (0 : ℂ) R \ ball (0 : ℂ) ρ ⊆ {t : ℂ | t ≠ 0} := by
    rintro t ⟨-, ht⟩
    simp only [mem_ball, dist_zero_right, not_lt] at ht
    exact fun h0 => absurd (h0 ▸ ht) (by simpa using hρ)
  exact circleIntegral_cluster_indep isOpen_ne (analyticOnNhd_clusterIntegrand B hc M) k a
    hρ hρR hann hr₁ hnode₁ hsmall₁ hr₂ hnode₂ hsmall₂

/-! ### Non-vacuity -/

/-- The hypothesis set of `circleIntegral_cluster_indep` is satisfiable: two
concentric circles of different radii about a single node, inside the annulus
`1 ≤ |t| ≤ 4`.  Without this the contour-independence statement could be true
because no configuration meets it. -/
theorem cluster_indep_hypotheses_nonvacuous :
    (∀ _ : ℕ, (2 : ℂ) ∈ ball (2 : ℂ) (1/2)) ∧
      closedBall (2 : ℂ) (1/2) ⊆ ball (0 : ℂ) 4 \ closedBall (0 : ℂ) 1 ∧
      (∀ _ : ℕ, (2 : ℂ) ∈ ball (2 : ℂ) (3/4)) ∧
      closedBall (2 : ℂ) (3/4) ⊆ ball (0 : ℂ) 4 \ closedBall (0 : ℂ) 1 := by
  have key : ∀ s : ℝ, 0 ≤ s → s < 1 →
      closedBall (2 : ℂ) s ⊆ ball (0 : ℂ) 4 \ closedBall (0 : ℂ) 1 := by
    intro s hs0 hs t ht
    rw [mem_closedBall, dist_eq_norm] at ht
    have h2 : ‖(2 : ℂ)‖ = 2 := by simp
    have hub : ‖t‖ ≤ 2 + s := by
      have h := norm_add_le (t - 2) (2 : ℂ)
      rw [sub_add_cancel, h2] at h
      linarith
    have hlb : 2 - s ≤ ‖t‖ := by
      have h := norm_sub_norm_le (2 : ℂ) (2 - t)
      rw [sub_sub_cancel, h2, norm_sub_rev (2 : ℂ) t] at h
      linarith
    refine ⟨?_, ?_⟩
    · simp only [mem_ball, dist_zero_right]; linarith
    · simp only [mem_closedBall, dist_zero_right, not_le]; linarith
  refine ⟨fun _ => by simp, key _ (by norm_num) (by norm_num), fun _ => by simp,
    key _ (by norm_num) (by norm_num)⟩

end ForgacsTran
