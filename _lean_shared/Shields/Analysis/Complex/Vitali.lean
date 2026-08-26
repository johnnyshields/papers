/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.Liouville
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
  constant for the whole family, which the pointwise limit inherits.
* **Compactness** supplies a finite `\delta`-net, and equi-Lipschitz plus convergence at the
  finitely many net points is the usual `\varepsilon/3` argument.

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
    (hz : z ∈ closedBall c r) : closedBall z ((R - r) / 2) ⊆ ball c R := by
  intro w hw
  rw [mem_ball]
  have h1 : dist w z ≤ (R - r) / 2 := mem_closedBall.mp hw
  have h2 : dist z c ≤ r := mem_closedBall.mp hz
  calc dist w c ≤ dist w z + dist z c := dist_triangle w z c
    _ ≤ (R - r) / 2 + r := by linarith
    _ < R := by linarith

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
  set Lip : ℝ := M / ((R - r) / 2) with hLip
  have hM0 : 0 ≤ M := by
    have hcb : c ∈ ball c R := mem_ball_self (by linarith)
    exact le_trans (norm_nonneg _) (hFM (Classical.arbitrary ι) c hcb)
  have hLip0 : 0 ≤ Lip := by
    rw [hLip]
    have : (0 : ℝ) < (R - r) / 2 := by linarith
    positivity
  have hLipF : ∀ i, ∀ a ∈ closedBall c r, ∀ b ∈ closedBall c r,
      ‖F i b - F i a‖ ≤ Lip * ‖b - a‖ := fun i a ha b hb =>
    norm_sub_le_of_bddOn hrR (hFd i) (hFM i) ha hb
  have hLipf : ∀ a ∈ closedBall c r, ∀ b ∈ closedBall c r, ‖f b - f a‖ ≤ Lip * ‖b - a‖ := by
    intro a ha b hb
    have hten : Tendsto (fun i => ‖F i b - F i a‖) L (𝓝 ‖f b - f a‖) :=
      ((hptw b hb).sub (hptw a ha)).norm
    exact le_of_tendsto hten (Eventually.of_forall fun i => hLipF i a ha b hb)
  rw [tendstoUniformlyOn_iff]
  intro ε hε
  set δ : ℝ := ε / (3 * (Lip + 1)) with hδdef
  have hδ : 0 < δ := by
    rw [hδdef]
    have : (0 : ℝ) < 3 * (Lip + 1) := by linarith
    positivity
  have hK : IsCompact (closedBall c r) := isCompact_closedBall c r
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover
    (fun x : ↥(closedBall c r) => ball (x : ℂ) δ) (fun _ => isOpen_ball)
    (fun z hz => Set.mem_iUnion.2 ⟨⟨z, hz⟩, mem_ball_self hδ⟩)
  have hnet : ∀ᶠ i in L, ∀ x ∈ t, ‖F i (x : ℂ) - f (x : ℂ)‖ < ε / 3 := by
    rw [eventually_all_finset]
    intro x _
    have hsub : Tendsto (fun i => F i (x : ℂ) - f (x : ℂ)) L (𝓝 (f (x : ℂ) - f (x : ℂ))) :=
      (hptw (x : ℂ) x.2).sub (tendsto_const_nhds (x := f (x : ℂ)))
    have hnorm : Tendsto (fun i => ‖F i (x : ℂ) - f (x : ℂ)‖) L (𝓝 0) := by
      simpa using hsub.norm
    exact hnorm.eventually (eventually_lt_nhds (by linarith))
  filter_upwards [hnet] with i hi z hz
  obtain ⟨x, hxt, hxz⟩ : ∃ x ∈ t, z ∈ ball (x : ℂ) δ := by
    have := ht hz
    simpa using this
  have hxmem : (x : ℂ) ∈ closedBall c r := x.2
  have hdxz : ‖z - (x : ℂ)‖ < δ := by
    rw [← dist_eq_norm]
    exact mem_ball.mp hxz
  have hLd : Lip * ‖z - (x : ℂ)‖ ≤ ε / 3 := by
    have h1 : Lip * ‖z - (x : ℂ)‖ ≤ Lip * δ :=
      mul_le_mul_of_nonneg_left hdxz.le hLip0
    have h2 : Lip * δ ≤ ε / 3 := by
      rw [hδdef, mul_div_assoc',
        div_le_div_iff₀ (by linarith : (0 : ℝ) < 3 * (Lip + 1)) (by norm_num : (0 : ℝ) < 3)]
      nlinarith [hε.le, hLip0]
    linarith
  have h1 : ‖f z - f (x : ℂ)‖ ≤ ε / 3 := by
    have := hLipf (x : ℂ) hxmem z hz
    linarith
  have h2 : ‖F i (x : ℂ) - F i z‖ ≤ ε / 3 := by
    have := hLipF i z hz (x : ℂ) hxmem
    have hsym : ‖z - (x : ℂ)‖ = ‖(x : ℂ) - z‖ := by rw [norm_sub_rev]
    rw [← hsym] at this
    linarith
  have h3 : ‖F i (x : ℂ) - f (x : ℂ)‖ < ε / 3 := hi x hxt
  have htri : ‖f z - F i z‖
      ≤ ‖f z - f (x : ℂ)‖ + ‖f (x : ℂ) - F i (x : ℂ)‖ + ‖F i (x : ℂ) - F i z‖ := by
    have hc : f z - F i z
        = (f z - f (x : ℂ)) + (f (x : ℂ) - F i (x : ℂ)) + (F i (x : ℂ) - F i z) := by ring
    calc ‖f z - F i z‖
        = ‖(f z - f (x : ℂ)) + (f (x : ℂ) - F i (x : ℂ)) + (F i (x : ℂ) - F i z)‖ := by rw [hc]
      _ ≤ ‖(f z - f (x : ℂ)) + (f (x : ℂ) - F i (x : ℂ))‖ + ‖F i (x : ℂ) - F i z‖ :=
          norm_add_le _ _
      _ ≤ ‖f z - f (x : ℂ)‖ + ‖f (x : ℂ) - F i (x : ℂ)‖ + ‖F i (x : ℂ) - F i z‖ := by
          have := norm_add_le (f z - f (x : ℂ)) (f (x : ℂ) - F i (x : ℂ))
          linarith
  have h3' : ‖f (x : ℂ) - F i (x : ℂ)‖ < ε / 3 := by rwa [norm_sub_rev]
  have hd : dist (f z) (F i z) = ‖f z - F i z‖ := dist_eq_norm _ _
  rw [hd]
  linarith

/-- Vitali on a circle, which is the shape a zero-counting argument consumes. -/
theorem tendstoUniformlyOn_sphere_of_bddOn_of_tendsto [L.NeBot] (hrR : r < R) (hr : 0 ≤ r)
    (hFd : ∀ i, DifferentiableOn ℂ (F i) (ball c R))
    (hFM : ∀ i, ∀ w ∈ ball c R, ‖F i w‖ ≤ M)
    (hptw : ∀ z ∈ closedBall c r, Tendsto (fun i => F i z) L (𝓝 (f z))) :
    TendstoUniformlyOn F f L (sphere c r) :=
  (tendstoUniformlyOn_of_bddOn_of_tendsto hrR hr hFd hFM hptw).mono sphere_subset_closedBall

end Shields
