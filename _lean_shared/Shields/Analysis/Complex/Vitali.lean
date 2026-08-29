/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Topology.MetricSpace.UniformConvergence
import Mathlib.Topology.UniformSpace.Ascoli
import Mathlib.Topology.UniformSpace.UniformConvergence

/-!
# Vitali's convergence theorem on a disc

A family of holomorphic functions that is **uniformly bounded** on a disc and converges
**pointwise** on a smaller closed disc converges **uniformly** there.  Pointwise convergence of
holomorphic functions is much stronger than it looks: a bound on the larger disc is all that has
to be added, and it comes for free wherever the family arises as ratios of quantities already
known to be bounded.

The proof is the textbook one, and every ingredient is already in Mathlib:

* **Cauchy's estimate** on a disc of radius `(R - r)/2` about each point of the smaller disc
  bounds every derivative by `2M/(R - r)`, with a constant independent of the point *and of the
  member of the family*.  This is the only place holomorphy is used.
* **The mean value inequality** on the convex closed disc turns that into a single Lipschitz
  constant for the whole family, so the family is equicontinuous on the closed disc.
* **Ascoli's theorem**, in the form `Equicontinuous.tendsto_uniformFun_iff_pi`, says that on a
  compact space an equicontinuous family converges uniformly exactly when it converges pointwise.
  That is the whole of the limit argument; no `\varepsilon/3` net is built by hand.

## Main results

* `Shields.norm_deriv_le_of_bddOn` — Cauchy's estimate at every point of the smaller disc.
* `Shields.norm_sub_le_of_bddOn` — one Lipschitz constant for the whole family.
* `Shields.tendstoUniformlyOn_of_bddOn_of_tendsto` — **Vitali**, on a closed disc.
* `Shields.tendstoUniformlyOn_sphere_of_bddOn_of_tendsto` — the same on a circle.

## Implementation notes

The hypothesis is pointwise convergence at **every** point of the closed disc.  The strong form
of the theorem asks only for a set with an accumulation point in the domain, and derives the rest
from normality (Montel, via Arzelà–Ascoli) together with the identity theorem; Mathlib carries
neither Montel for holomorphic families nor the Arzelà–Ascoli argument in that shape, so this
file proves the form whose ingredients are present.

The bound is stated on the open ball and the conclusion on a strictly smaller closed ball.  That
gap is what pays for Cauchy's estimate, and the constant it produces, `2M/(R - r)`, degrades as
the two radii approach each other, exactly as it must.

## References

* G. Vitali, *Sopra le serie di funzioni analitiche*, Rend. Ist. Lombardo (2) 36 (1903).
* J. B. Conway, *Functions of one complex variable I*, 2nd ed., Springer, 1978, VII.3.

## Tags

vitali, uniform convergence, holomorphic, normal family, cauchy estimate
-/

open Filter Topology Metric

namespace Shields

variable {g : ℂ → ℂ} {c : ℂ} {r R M : ℝ}

/-- The closed disc of radius `(R - r)/2` about a point of `closedBall c r` sits inside
`ball c R`. -/
theorem closedBall_subset_ball_of_mem_closedBall (hrR : r < R) {z : ℂ}
    (hz : z ∈ closedBall c r) : closedBall z ((R - r) / 2) ⊆ ball c R :=
  closedBall_subset_ball' (by have := mem_closedBall.mp hz; linarith)

/-- **Cauchy's estimate, at every point of the smaller disc.**  A bound `M` on `ball c R` bounds
every derivative on `closedBall c r` by `2M/(R - r)`, with a constant free of the point. -/
theorem norm_deriv_le_of_bddOn (hrR : r < R)
    (hg : DifferentiableOn ℂ g (ball c R)) (hgM : ∀ w ∈ ball c R, ‖g w‖ ≤ M)
    {z : ℂ} (hz : z ∈ closedBall c r) : ‖deriv g z‖ ≤ M / ((R - r) / 2) := by
  set ρ : ℝ := (R - r) / 2 with hρdef
  have hρ : 0 < ρ := by rw [hρdef]; linarith
  have hsub : closedBall z ρ ⊆ ball c R := closedBall_subset_ball_of_mem_closedBall hrR hz
  have hclos : closure (ball z ρ) ⊆ ball c R := by
    rw [closure_ball z hρ.ne']
    exact hsub
  have hdc : DiffContOnCl ℂ g (ball z ρ) := (hg.mono hclos).diffContOnCl
  refine Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hρ hdc fun w hw => ?_
  exact hgM w (hsub (sphere_subset_closedBall hw))

/-- **One Lipschitz constant for a bounded holomorphic function on the smaller disc.**  The mean
value inequality on the convex closed disc turns Cauchy's estimate into a modulus of continuity
that depends only on `M`, `r` and `R`. -/
theorem norm_sub_le_of_bddOn (hrR : r < R)
    (hg : DifferentiableOn ℂ g (ball c R)) (hgM : ∀ w ∈ ball c R, ‖g w‖ ≤ M)
    {a b : ℂ} (ha : a ∈ closedBall c r) (hb : b ∈ closedBall c r) :
    ‖g b - g a‖ ≤ (M / ((R - r) / 2)) * ‖b - a‖ := by
  have hopen : ∀ x ∈ closedBall c r, DifferentiableAt ℂ g x := by
    intro x hx
    have hxb : x ∈ ball c R := by
      rw [mem_ball]
      have := mem_closedBall.mp hx
      linarith
    exact hg.differentiableAt (isOpen_ball.mem_nhds hxb)
  exact (convex_closedBall c r).norm_image_sub_le_of_norm_deriv_le hopen
    (fun x hx => norm_deriv_le_of_bddOn hrR hg hgM hx) ha hb

variable {ι : Type*} {L : Filter ι} {F : ι → ℂ → ℂ} {f : ℂ → ℂ}

/-- **Vitali's convergence theorem**, on a closed disc.  A family holomorphic on `ball c R` and
bounded there by a single `M`, converging pointwise on `closedBall c r` with `r < R`, converges
uniformly on that closed disc.

The added hypothesis is a *bound*, not any form of uniformity. -/
theorem tendstoUniformlyOn_of_bddOn_of_tendsto [L.NeBot] (hrR : r < R) (hr : 0 ≤ r)
    (hFd : ∀ i, DifferentiableOn ℂ (F i) (ball c R))
    (hFM : ∀ i, ∀ w ∈ ball c R, ‖F i w‖ ≤ M)
    (hptw : ∀ z ∈ closedBall c r, Tendsto (fun i => F i z) L (𝓝 (f z))) :
    TendstoUniformlyOn F f L (closedBall c r) := by
  haveI : Nonempty ι := nonempty_of_neBot L
  haveI : CompactSpace (closedBall c r) := isCompact_iff_compactSpace.mp (isCompact_closedBall c r)
  have hM0 : 0 ≤ M :=
    le_trans (norm_nonneg _) (hFM (Classical.arbitrary ι) c (mem_ball_self (by linarith)))
  have hLipF : ∀ i,
      LipschitzOnWith (Real.toNNReal (M / ((R - r) / 2))) (F i) (closedBall c r) := by
    intro i
    refine LipschitzOnWith.of_dist_le_mul fun a ha b hb => ?_
    rw [Real.coe_toNNReal _ (by positivity), dist_eq_norm, dist_eq_norm]
    exact norm_sub_le_of_bddOn hrR (hFd i) (hFM i) hb ha
  have heqc : Equicontinuous ((closedBall c r).domRestrict ∘ F) :=
    (equicontinuous_restrict_iff F).mpr
      (LipschitzOnWith.uniformEquicontinuousOn F _ hLipF).equicontinuousOn
  rw [tendstoUniformlyOn_iff_tendstoUniformly_comp_coe]
  exact UniformFun.tendsto_iff_tendstoUniformly.mp
    ((Equicontinuous.tendsto_uniformFun_iff_pi heqc L (f ∘ (↑))).mpr
      (tendsto_pi_nhds.mpr fun x => hptw x x.2))

/-- Vitali on a circle, which is the shape a zero-counting argument consumes. -/
theorem tendstoUniformlyOn_sphere_of_bddOn_of_tendsto [L.NeBot] (hrR : r < R) (hr : 0 ≤ r)
    (hFd : ∀ i, DifferentiableOn ℂ (F i) (ball c R))
    (hFM : ∀ i, ∀ w ∈ ball c R, ‖F i w‖ ≤ M)
    (hptw : ∀ z ∈ closedBall c r, Tendsto (fun i => F i z) L (𝓝 (f z))) :
    TendstoUniformlyOn F f L (sphere c r) :=
  (tendstoUniformlyOn_of_bddOn_of_tendsto hrR hr hFd hFM hptw).mono sphere_subset_closedBall


/-! ### Axiom footprint -/

/-- info: 'Shields.tendstoUniformlyOn_sphere_of_bddOn_of_tendsto' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms tendstoUniformlyOn_sphere_of_bddOn_of_tendsto

end Shields
