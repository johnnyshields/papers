/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities
import Mathlib.RingTheory.Polynomial.Vieta
import Shields.Analysis.Calculus.TaylorCoeff
import Shields.Analysis.Complex.ArgumentPrinciple.Analytic

/-!
# The weighted argument principle, and packets of zeros

A **packet** is a function together with a factorization `f = \prod_j (z - a_j) \cdot g` on a
disc, `g` analytic and zero-free there.  Two structures carry one: `Shields.PacketFactor`, whose
cofactor is entire, and `Shields.AnalyticPacket`, whose cofactor is analytic on a neighborhood of
the closed disc only.  Every function analytic on a neighborhood of a closed disc with no zero on
the bounding circle admits the latter.

## Main definitions

* `Shields.PacketFactor`, `Shields.AnalyticPacket`: the two packet structures.
* `Shields.esymmC`: the elementary symmetric functions of a tuple of complex numbers.
* `Shields.packetPoly`: the monic polynomial with the packet's roots.

## Main results

* `Shields.PacketFactor.weighted_argumentPrinciple`,
  `Shields.AnalyticPacket.weighted_argumentPrinciple`: **the weighted argument principle**.  For an
  analytic weight `\varphi`, `\oint \varphi \cdot f'/f = 2\pi i \sum_j \varphi(a_j)`.  At weight
  `1` this is the argument principle, at weight `z^m` the `m`-th power sum of the enclosed zeros.
* `Shields.AnalyticPacket.zeroCount_eq`: a packet's `k` is the multiplicity-counted zero count of
  `Shields.zeroCount`.
* `Shields.exists_analyticPacket`: existence of a packet.
* `Shields.card_eq_of_norm_circleIntegral_sub_lt`, `Shields.eventually_card_eq`,
  `Shields.AnalyticPacket.eventually_card_eq`: stability of the count under uniform convergence,
  obtained from the integral representation rather than from Rouché.
* `Shields.mul_esymmC_eq_sum`, `Shields.tendsto_esymmC_of_tendsto_psum`: **Newton's identities**
  over `\mathbb{C}` in the tuple-indexed form, and the resulting continuity of the elementary
  symmetric functions in the power sums.
* `Shields.exists_monic_analytic_preparation_packet`,
  `Shields.rootMultiplicity_packetPoly_eq_analyticOrderNatAt`: **analytic Weierstrass
  preparation** with a tuple-indexed root packet, and the pointwise multiplicity clause.

## Implementation notes

Every contour is a circle centered at the origin, matching the packet structures; the center-`c`
statements are in `Shields.Analysis.Complex.ArgumentPrinciple.Analytic`.  The generality traded
away is the center, and the generality gained is the weight.  A packet carries its factorization
as data: no result here produces one except `Shields.exists_analyticPacket`.  Poles are excluded
throughout, so the counts are of zeros, not of zeros minus poles.

## Tags

argument principle, weighted argument principle, Weierstrass preparation, Newton identities,
power sum, elementary symmetric function, zero count, Hurwitz
-/

open Complex Metric Filter

open scoped Topology

namespace Shields

open Complex Metric Filter

open scoped Topology

/-! ### Supporting lemmas -/

/-- Lower-bound clause: a positive lower bound for the limit passes to half that bound for all
sufficiently late members of the family. -/
theorem eventually_half_le_norm {ι α : Type*} {φ : Filter ι} {S : Set α}
    {F : ι → α → ℂ} {f : α → ℂ} (h : TendstoUniformlyOn F f φ S) {c : ℝ} (hc : 0 < c)
    (hf : ∀ x ∈ S, c ≤ ‖f x‖) : ∀ᶠ n in φ, ∀ x ∈ S, c / 2 ≤ ‖F n x‖ := by
  rw [Metric.tendstoUniformlyOn_iff] at h
  filter_upwards [h (c / 2) (by positivity)] with n hn x hx
  have hd := hn x hx
  rw [dist_eq_norm] at hd
  have h1 : ‖f x‖ - ‖F n x‖ ≤ ‖f x - F n x‖ := norm_sub_norm_le _ _
  have h2 := hf x hx
  linarith

/-- Quotients converge uniformly where the limit denominator is bounded away from zero and the
limit numerator is bounded. -/
theorem tendstoUniformlyOn_div {ι α : Type*} {φ : Filter ι} {S : Set α}
    {C H : ι → α → ℂ} {c h : α → ℂ} {κ Mc : ℝ}
    (hC : TendstoUniformlyOn C c φ S) (hH : TendstoUniformlyOn H h φ S)
    (hκ : 0 < κ) (hlow : ∀ x ∈ S, κ ≤ ‖h x‖) (hcb : ∀ x ∈ S, ‖c x‖ ≤ Mc) :
    TendstoUniformlyOn (fun n x ↦ C n x / H n x) (fun x ↦ c x / h x) φ S := by
  have hMc : 0 ≤ max Mc 0 := le_max_right _ _
  have hhalf := eventually_half_le_norm hH hκ hlow
  rw [Metric.tendstoUniformlyOn_iff] at hC hH ⊢
  intro ε hε
  have hd1 : 0 < ε * κ / 8 := by positivity
  have hd2 : 0 < ε * κ * κ / (8 * (max Mc 0 + 1)) := by positivity
  filter_upwards [hhalf, hC _ hd1, hH _ hd2] with n hn hh1 hh2 x hx
  have h1 := hh1 x hx
  have h2 := hh2 x hx
  have hHn : κ / 2 ≤ ‖H n x‖ := hn x hx
  have hHnpos : 0 < ‖H n x‖ := lt_of_lt_of_le (by positivity) hHn
  have hhpos : 0 < ‖h x‖ := lt_of_lt_of_le hκ (hlow x hx)
  have hHne : H n x ≠ 0 := by simpa [norm_pos_iff] using hHnpos
  have hhne : h x ≠ 0 := by simpa [norm_pos_iff] using hhpos
  rw [dist_eq_norm] at h1 h2 ⊢
  have expand : c x / h x - C n x / H n x
      = (c x - C n x) / H n x + c x * (H n x - h x) / (h x * H n x) := by
    field
  rw [expand]
  have e1 : ‖c x - C n x‖ ≤ ε * κ / 8 := h1.le
  have e2 : ‖H n x - h x‖ ≤ ε * κ * κ / (8 * (max Mc 0 + 1)) := by
    rw [← norm_neg]
    simpa using h2.le
  have ecb : ‖c x‖ ≤ max Mc 0 + 1 :=
    ((hcb x hx).trans (le_max_left _ _)).trans (by linarith)
  have elow : κ ≤ ‖h x‖ := hlow x hx
  have hκ2 : (0 : ℝ) < κ / 2 := by positivity
  have t1 : ‖(c x - C n x) / H n x‖ ≤ (ε * κ / 8) / (κ / 2) := by
    rw [norm_div]; gcongr
  have t2 : ‖c x * (H n x - h x) / (h x * H n x)‖
      ≤ (max Mc 0 + 1) * (ε * κ * κ / (8 * (max Mc 0 + 1))) / (κ * (κ / 2)) := by
    rw [norm_div, norm_mul, norm_mul]; gcongr
  refine lt_of_le_of_lt ((norm_add_le _ _).trans (add_le_add t1 t2)) ?_
  have r1 : (ε * κ / 8) / (κ / 2) = ε / 4 := by field_simp; ring
  have r2 : (max Mc 0 + 1) * (ε * κ * κ / (8 * (max Mc 0 + 1))) / (κ * (κ / 2)) = ε / 4 := by
    field
  rw [r1, r2]
  linarith

/-! ### The local Weierstrass factorization -/

/-- A factorization of `f` over its zeros in the closed disc `‖t‖ ≤ r`: `k` roots inside the
open disc and an entire cofactor with no zero on the closed disc.

Mathlib has no local factorization theorem, so this is carried as data.  The roots are listed with
multiplicity — `root` is a function on `Fin k`, not an injection — so the structure describes a
packet with internal collisions as readily as a separated one. -/
structure PacketFactor (f : ℂ → ℂ) (r : ℝ) (k : ℕ) where
  /-- The contour radius is positive. -/
  radius_pos : 0 < r
  /-- The enclosed zeros, listed with multiplicity. -/
  root : Fin k → ℂ
  /-- The zero-free cofactor. -/
  cofactor : ℂ → ℂ
  /-- Every root lies strictly inside the contour. -/
  root_mem_ball : ∀ j, ‖root j‖ < r
  /-- The cofactor is entire. -/
  cofactor_differentiable : Differentiable ℂ cofactor
  /-- The cofactor has no zero on the closed disc: the listed roots are all of them. -/
  cofactor_ne_zero : ∀ t : ℂ, ‖t‖ ≤ r → cofactor t ≠ 0
  /-- The factorization itself. -/
  eq_prod : ∀ t : ℂ, f t = (∏ j, (t - root j)) * cofactor t

namespace PacketFactor

variable {f : ℂ → ℂ} {r : ℝ} {k : ℕ}

theorem differentiable (F : PacketFactor f r k) : Differentiable ℂ f := by
  have hfe : f = fun t ↦ (∏ j, (t - F.root j)) * F.cofactor t := funext F.eq_prod
  rw [hfe]
  exact (Differentiable.fun_finsetProd fun j _ ↦ differentiable_id.sub_const _).mul
    F.cofactor_differentiable

theorem differentiable_deriv_cofactor (F : PacketFactor f r k) :
    Differentiable ℂ (deriv F.cofactor) := by
  have h := differentiable_iteratedDeriv F.cofactor_differentiable 1
  rwa [iteratedDeriv_one] at h

theorem sub_root_ne_zero (F : PacketFactor f r k) {t : ℂ} (ht : ‖t‖ = r) (j : Fin k) :
    t - F.root j ≠ 0 := by
  intro h
  rw [sub_eq_zero] at h
  exact absurd (h ▸ ht) (ne_of_lt (F.root_mem_ball j))

/-- The contour carries no zero. -/
theorem ne_zero_of_norm_eq (F : PacketFactor f r k) {t : ℂ} (ht : ‖t‖ = r) : f t ≠ 0 := by
  rw [F.eq_prod]
  exact mul_ne_zero (Finset.prod_ne_zero_iff.2 fun j _ ↦ F.sub_root_ne_zero ht j)
    (F.cofactor_ne_zero t ht.le)

/-- The logarithmic derivative splits over the packet and the cofactor. -/
theorem logDeriv_eq (F : PacketFactor f r k) {t : ℂ} (ht : ‖t‖ = r) :
    deriv f t / f t = (∑ j, (t - F.root j)⁻¹) + deriv F.cofactor t / F.cofactor t := by
  have hfe : f = fun s : ℂ ↦ (∏ j, (s - F.root j)) * F.cofactor s := funext F.eq_prod
  have hp : (∏ j, (t - F.root j)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun j _ ↦ F.sub_root_ne_zero ht j
  have hg : F.cofactor t ≠ 0 := F.cofactor_ne_zero t ht.le
  have hdp : DifferentiableAt ℂ (fun s : ℂ ↦ ∏ j, (s - F.root j)) t :=
    (Differentiable.fun_finsetProd fun j _ ↦ differentiable_id.sub_const _) t
  have h1 : logDeriv f t
      = logDeriv (fun s : ℂ ↦ (∏ j, (s - F.root j)) * F.cofactor s) t :=
    congrArg (fun u : ℂ → ℂ ↦ logDeriv u t) hfe
  have h2 : logDeriv (fun s : ℂ ↦ (∏ j, (s - F.root j)) * F.cofactor s) t
      = logDeriv (fun s : ℂ ↦ ∏ j, (s - F.root j)) t + logDeriv F.cofactor t :=
    logDeriv_mul t hp hg hdp (F.cofactor_differentiable t)
  have h3 : logDeriv (fun s : ℂ ↦ ∏ j, (s - F.root j)) t = ∑ j, (t - F.root j)⁻¹ := by
    rw [logDeriv_prod (f := fun (j : Fin k) (s : ℂ) ↦ s - F.root j)
      (fun j _ ↦ F.sub_root_ne_zero ht j) (fun j _ ↦ by fun_prop)]
    exact Finset.sum_congr rfl fun j _ ↦ by
      simp [logDeriv_apply, one_div]
  rw [show deriv f t / f t = logDeriv f t from rfl, h1, h2, h3, logDeriv_apply]

/-! ### The weighted argument principle -/

/-- `∮_{|t| = r} φ(t) f'(t)/f(t) dt = 2πi ∑_j φ(aⱼ)` for entire `φ`, assembled from Cauchy's
integral formula on each root factor and Cauchy–Goursat on the cofactor's logarithmic
derivative, which is holomorphic on the closed disc. -/
theorem weighted_argumentPrinciple (F : PacketFactor f r k) {φ : ℂ → ℂ}
    (hφ : Differentiable ℂ φ) :
    (∮ t in C((0 : ℂ), r), φ t * (deriv f t / f t))
      = (2 * (Real.pi : ℂ) * Complex.I) * ∑ j, φ (F.root j) := by
  have hr := F.radius_pos
  have hdc := F.differentiable_deriv_cofactor
  set g : ℂ → ℂ := fun t ↦ φ t * (deriv F.cofactor t / F.cofactor t) with hgdef
  have hgdiff : ∀ t : ℂ, ‖t‖ ≤ r → DifferentiableAt ℂ g t := fun t ht ↦
    (hφ t).mul ((hdc t).div (F.cofactor_differentiable t) (F.cofactor_ne_zero t ht))
  have hgcont : ContinuousOn g (Metric.closedBall (0 : ℂ) r) := fun t ht ↦
    ((hgdiff t (mem_closedBall_zero_iff.1 ht)).continuousAt).continuousWithinAt
  have hrootcont : ∀ j : Fin k,
      ContinuousOn (fun t : ℂ ↦ φ t / (t - F.root j)) (Metric.sphere (0 : ℂ) r) := by
    intro j t ht
    have hne : t - F.root j ≠ 0 := F.sub_root_ne_zero (mem_sphere_zero_iff_norm.1 ht) j
    exact (((hφ t).continuousAt).div (by fun_prop) hne).continuousWithinAt
  have hrootint : ∀ j ∈ (Finset.univ : Finset (Fin k)),
      CircleIntegrable (fun t : ℂ ↦ φ t / (t - F.root j)) 0 r :=
    fun j _ ↦ (hrootcont j).circleIntegrable hr.le
  have hsumint : CircleIntegrable (fun t : ℂ ↦ ∑ j, φ t / (t - F.root j)) 0 r :=
    (continuousOn_finsetSum _ fun j _ ↦ hrootcont j).circleIntegrable hr.le
  have hgint : CircleIntegrable g 0 r :=
    (hgcont.mono Metric.sphere_subset_closedBall).circleIntegrable hr.le
  have hEq : Set.EqOn (fun t ↦ φ t * (deriv f t / f t))
      (fun t ↦ (∑ j, φ t / (t - F.root j)) + g t) (Metric.sphere (0 : ℂ) r) := by
    intro t ht
    have hn := mem_sphere_zero_iff_norm.1 ht
    simp only [hgdef]
    rw [F.logDeriv_eq hn, mul_add, Finset.mul_sum]
    congr 1
  have hzero : (∮ t in C((0 : ℂ), r), g t) = 0 :=
    Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable hr.le Set.countable_empty
      hgcont fun t ht ↦ hgdiff t (le_of_lt (mem_ball_zero_iff.1 ht.1))
  have hroot : ∀ j : Fin k, (∮ t in C((0 : ℂ), r), φ t / (t - F.root j))
      = 2 * (Real.pi : ℂ) * Complex.I * φ (F.root j) := fun j ↦
    Complex.circleIntegral_div_sub_of_differentiable_on_off_countable Set.countable_empty
      (mem_ball_zero_iff.2 (F.root_mem_ball j)) hφ.continuous.continuousOn fun t _ ↦ hφ t
  rw [circleIntegral.integral_congr hr.le hEq, circleIntegral.integral_add hsumint hgint,
    circleIntegral.integral_fun_sum hrootint, hzero, add_zero,
    Finset.sum_congr rfl fun j (_ : j ∈ Finset.univ) ↦ hroot j, Finset.mul_sum]

/-- The count: `(2πi)^{-1} ∮ f'/f = k`. -/
theorem circleIntegral_logDeriv (F : PacketFactor f r k) :
    (∮ t in C((0 : ℂ), r), deriv f t / f t) = (2 * (Real.pi : ℂ) * Complex.I) * k := by
  have h := F.weighted_argumentPrinciple (φ := fun _ ↦ (1 : ℂ)) (differentiable_const 1)
  simpa using h

/-- The power sums of the packet. -/
theorem circleIntegral_pow_logDeriv (F : PacketFactor f r k) (m : ℕ) :
    (∮ t in C((0 : ℂ), r), t ^ m * (deriv f t / f t))
      = (2 * (Real.pi : ℂ) * Complex.I) * ∑ j, F.root j ^ m :=
  F.weighted_argumentPrinciple (φ := fun t ↦ t ^ m) (differentiable_pow m)

end PacketFactor

/-! ### Count stability without Rouché -/

theorem norm_two_pi_I : ‖(2 * (Real.pi : ℂ) * Complex.I)‖ = 2 * Real.pi := by
  simp [abs_of_pos Real.pi_pos]

/-- Two packets on the same contour whose counting integrals lie within `2π` have the same
cardinality: integers at distance below one are equal.  This replaces the Rouché homotopy. -/
theorem card_eq_of_norm_circleIntegral_sub_lt {f g : ℂ → ℂ} {r : ℝ} {k l : ℕ}
    (F : PacketFactor f r k) (G : PacketFactor g r l)
    (h : ‖(∮ t in C((0 : ℂ), r), deriv f t / f t) - ∮ t in C((0 : ℂ), r), deriv g t / g t‖
        < 2 * Real.pi) : k = l := by
  rw [F.circleIntegral_logDeriv, G.circleIntegral_logDeriv, ← mul_sub, norm_mul,
    norm_two_pi_I] at h
  by_contra hne
  have hnorm : ‖(k : ℂ) - (l : ℂ)‖ = |(k : ℝ) - (l : ℝ)| := by
    rw [show ((k : ℂ) - (l : ℂ)) = ((((k : ℝ) - (l : ℝ)) : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs]
  have h1 : (1 : ℝ) ≤ |(k : ℝ) - (l : ℝ)| := by
    rcases lt_or_gt_of_ne hne with hc | hc
    · have hkl : ((k : ℝ) + 1) ≤ (l : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hc
      rw [abs_sub_comm, abs_of_nonneg (by linarith)]
      linarith
    · have hkl : ((l : ℝ) + 1) ≤ (k : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hc
      rw [abs_of_nonneg (by linarith)]
      linarith
  rw [hnorm] at h
  nlinarith [Real.pi_pos]

/-- Multiplying by `t^m` preserves uniform convergence on a circle, where `‖t^m‖` is the
constant `r^m`. -/
theorem tendstoUniformlyOn_pow_mul {ι : Type*} {φ : Filter ι} {r : ℝ} (hr : 0 < r) (m : ℕ)
    {u : ι → ℂ → ℂ} {v : ℂ → ℂ}
    (h : TendstoUniformlyOn u v φ (Metric.sphere (0 : ℂ) r)) :
    TendstoUniformlyOn (fun i t ↦ t ^ m * u i t) (fun t ↦ t ^ m * v t) φ
      (Metric.sphere (0 : ℂ) r) := by
  rw [Metric.tendstoUniformlyOn_iff] at h ⊢
  intro ε hε
  have hrm : (0 : ℝ) < r ^ m := pow_pos hr m
  filter_upwards [h (ε / r ^ m) (by positivity)] with i hi t ht
  have hnt : ‖t‖ = r := mem_sphere_zero_iff_norm.1 ht
  have hd : dist (t ^ m * v t) (t ^ m * u i t) = r ^ m * dist (v t) (u i t) := by
    rw [dist_eq_norm, dist_eq_norm, ← mul_sub, norm_mul, norm_pow, hnt]
  rw [hd]
  calc r ^ m * dist (v t) (u i t) < r ^ m * (ε / r ^ m) :=
        mul_lt_mul_of_pos_left (hi t ht) hrm
    _ = ε := by field_simp

/-- Logarithmic derivatives converge uniformly on a contour where the limit is bounded away
from zero and both the functions and their derivatives converge uniformly. -/
theorem tendstoUniformlyOn_logDeriv {ι : Type*} {φ : Filter ι} {r : ℝ}
    {f : ℂ → ℂ} {fN : ι → ℂ → ℂ} {κ : ℝ} (hκ : 0 < κ) (hf : Differentiable ℂ f)
    (hlow : ∀ t : ℂ, ‖t‖ = r → κ ≤ ‖f t‖)
    (h0 : TendstoUniformlyOn fN f φ (Metric.sphere (0 : ℂ) r))
    (h1 : TendstoUniformlyOn (fun i ↦ deriv (fN i)) (deriv f) φ (Metric.sphere (0 : ℂ) r)) :
    TendstoUniformlyOn (fun i t ↦ deriv (fN i) t / fN i t) (fun t ↦ deriv f t / f t) φ
      (Metric.sphere (0 : ℂ) r) := by
  have hdf : Differentiable ℂ (deriv f) := by
    have h := differentiable_iteratedDeriv hf 1
    rwa [iteratedDeriv_one] at h
  obtain ⟨M, hM⟩ := (isCompact_sphere (0 : ℂ) r).exists_bound_of_continuousOn
    hdf.continuous.continuousOn
  exact tendstoUniformlyOn_div h1 h0 hκ (fun t ht ↦ hlow t (mem_sphere_zero_iff_norm.1 ht)) hM

/-- Count stability: the packet cardinalities of a uniformly convergent family are
eventually those of the limit. -/
theorem eventually_card_eq {ι : Type*} {φ : Filter ι} [φ.IsCountablyGenerated] {r : ℝ}
    {k : ℕ} {kN : ι → ℕ} {f : ℂ → ℂ} {fN : ι → ℂ → ℂ}
    (F : PacketFactor f r k) (FN : ∀ i, PacketFactor (fN i) r (kN i))
    (hcont : ∀ᶠ i in φ,
      ContinuousOn (fun t ↦ deriv (fN i) t / fN i t) (Metric.sphere (0 : ℂ) r))
    (huc : TendstoUniformlyOn (fun i t ↦ deriv (fN i) t / fN i t)
      (fun t ↦ deriv f t / f t) φ (Metric.sphere (0 : ℂ) r)) :
    ∀ᶠ i in φ, kN i = k := by
  have hten := huc.tendsto_circleIntegral_of_continuousOn F.radius_pos.le hcont
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  filter_upwards [(Metric.tendsto_nhds.1 hten) (2 * Real.pi) hpi] with i hi
  refine card_eq_of_norm_circleIntegral_sub_lt (FN i) F ?_
  rwa [← dist_eq_norm]

/-! ### Newton's identities over the complex numbers -/

/-- The `m`-th elementary symmetric function of a tuple of complex numbers. -/
noncomputable def esymmC {k : ℕ} (a : Fin k → ℂ) (m : ℕ) : ℂ :=
  MvPolynomial.aeval a (MvPolynomial.esymm (Fin k) ℂ m)

@[simp] theorem esymmC_zero {k : ℕ} (a : Fin k → ℂ) : esymmC a 0 = 1 := by
  simp [esymmC, MvPolynomial.esymm_zero]

theorem eval_psum {k : ℕ} (a : Fin k → ℂ) (m : ℕ) :
    MvPolynomial.eval a (MvPolynomial.psum (Fin k) ℂ m) = ∑ j, a j ^ m := by
  simp [MvPolynomial.psum]

/-- **Newton's identities** over `ℂ`, transported from `MvPolynomial.mul_esymm_eq_sum`. -/
theorem mul_esymmC_eq_sum {k : ℕ} (a : Fin k → ℂ) (m : ℕ) :
    (m : ℂ) * esymmC a m
      = (-1) ^ (m + 1) * ∑ x ∈ Finset.HasAntidiagonal.antidiagonal m with x.1 < m,
          (-1) ^ x.1 * esymmC a x.1 * ∑ j, a j ^ x.2 := by
  have h := congrArg (MvPolynomial.aeval (R := ℂ) a)
    (MvPolynomial.mul_esymm_eq_sum (Fin k) ℂ m)
  simpa [esymmC, eval_psum, map_sum] using h

/-- Solving Newton's identities forward: the division by `m` is why the coefficient field
must have characteristic zero.  Convergence of every power sum forces convergence of every
elementary symmetric function, which is what survives internal collisions of the packet. -/
theorem tendsto_esymmC_of_tendsto_psum {ι : Type*} {φ : Filter ι} {k : ℕ}
    {a : ι → Fin k → ℂ} {b : Fin k → ℂ}
    (h : ∀ m, 1 ≤ m → Tendsto (fun i ↦ ∑ j, a i j ^ m) φ (𝓝 (∑ j, b j ^ m))) (m : ℕ) :
    Tendsto (fun i ↦ esymmC (a i) m) φ (𝓝 (esymmC b m)) := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simpa using tendsto_const_nhds
    have hm0 : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
    have key : ∀ c : Fin k → ℂ, esymmC c m
        = (m : ℂ)⁻¹ * ((-1) ^ (m + 1)
            * ∑ x ∈ Finset.HasAntidiagonal.antidiagonal m with x.1 < m,
                (-1) ^ x.1 * esymmC c x.1 * ∑ j, c j ^ x.2) := by
      intro c
      rw [← mul_esymmC_eq_sum, inv_mul_cancel_left₀ hm0]
    simp only [key]
    refine Tendsto.const_mul _ (Tendsto.const_mul _ (tendsto_finsetSum _ fun x hx ↦ ?_))
    have hx1 : x.1 < m := (Finset.mem_filter.1 hx).2
    have hx2 : 1 ≤ x.2 := by
      have hxa := Finset.HasAntidiagonal.mem_antidiagonal.1 (Finset.mem_filter.1 hx).1
      omega
    exact (tendsto_const_nhds.mul (ih x.1 hx1)).mul (h x.2 hx2)

/-! ### The packet polynomial -/

/-- The monic packet polynomial `W(t) = ∏_j (t - aⱼ)`. -/
noncomputable def packetPoly {k : ℕ} (ζ : Fin k → ℂ) : Polynomial ℂ :=
  ∏ b, (Polynomial.X - Polynomial.C (ζ b))

theorem packetPoly_monic {k : ℕ} (a : Fin k → ℂ) : (packetPoly a).Monic :=
  Polynomial.monic_prod_of_monic _ _ fun j _ ↦ Polynomial.monic_X_sub_C (a j)

theorem packetPoly_natDegree {k : ℕ} (a : Fin k → ℂ) : (packetPoly a).natDegree = k := by
  rw [packetPoly,
    Polynomial.natDegree_prod_of_monic _ _ fun j _ ↦ Polynomial.monic_X_sub_C (a j)]
  simp

/-- Vieta: the coefficients of the packet polynomial are, up to sign, the elementary
symmetric functions of the packet. -/
theorem packetPoly_coeff {k m : ℕ} (a : Fin k → ℂ) (hm : m ≤ k) :
    (packetPoly a).coeff m = (-1) ^ (k - m) * esymmC a (k - m) := by
  have hcard : Multiset.card (Multiset.map a (Finset.univ : Finset (Fin k)).val) = k := by simp
  have hprod : packetPoly a
      = (Multiset.map (fun t ↦ Polynomial.X - Polynomial.C t)
          (Multiset.map a (Finset.univ : Finset (Fin k)).val)).prod := by
    rw [packetPoly, Finset.prod_eq_multiset_prod, Multiset.map_map]
    rfl
  rw [hprod, Multiset.prod_X_sub_C_coeff _ (by rw [hcard]; exact hm), hcard, esymmC,
    MvPolynomial.aeval_esymm_eq_multiset_esymm]

theorem packetPoly_coeff_of_lt {k m : ℕ} (a : Fin k → ℂ) (hm : k < m) :
    (packetPoly a).coeff m = 0 :=
  Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [packetPoly_natDegree]; exact hm)

/-- `(-1)^k W(0) = ∏_j aⱼ`. -/
theorem neg_one_pow_mul_packetPoly_coeff_zero {k : ℕ} (a : Fin k → ℂ) :
    (-1 : ℂ) ^ k * (packetPoly a).coeff 0 = ∏ j, a j := by
  have h1 : ∀ j : Fin k,
      (Polynomial.X - Polynomial.C (a j)).eval (0 : ℂ) = (-1 : ℂ) * a j := by
    intro j
    rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    ring
  have hev : (packetPoly a).coeff 0 = (-1 : ℂ) ^ k * ∏ j, a j := by
    rw [Polynomial.coeff_zero_eq_eval_zero, packetPoly, Polynomial.eval_prod,
      Finset.prod_congr rfl fun j (_ : j ∈ Finset.univ) ↦ h1 j, Finset.prod_mul_distrib,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [hev, ← mul_assoc, ← mul_pow]
  norm_num

/-! ### Coefficientwise convergence of the packet polynomial -/

section Convergence

variable {ι : Type*} {φ : Filter ι} {r : ℝ} {k : ℕ} {f : ℂ → ℂ} {fN : ι → ℂ → ℂ}

/-- Every power sum of the packet converges: both sides are circle integrals of `t^m f'/f`,
and the integrands converge uniformly on the contour. -/
theorem tendsto_psum_root [φ.IsCountablyGenerated]
    (F : PacketFactor f r k) (FN : ∀ i, PacketFactor (fN i) r k)
    (hcont : ∀ᶠ i in φ,
      ContinuousOn (fun t ↦ deriv (fN i) t / fN i t) (Metric.sphere (0 : ℂ) r))
    (huc : TendstoUniformlyOn (fun i t ↦ deriv (fN i) t / fN i t)
      (fun t ↦ deriv f t / f t) φ (Metric.sphere (0 : ℂ) r)) (m : ℕ) :
    Tendsto (fun i ↦ ∑ j, (FN i).root j ^ m) φ (𝓝 (∑ j, F.root j ^ m)) := by
  have hcont' : ∀ᶠ i in φ,
      ContinuousOn (fun t ↦ t ^ m * (deriv (fN i) t / fN i t)) (Metric.sphere (0 : ℂ) r) :=
    hcont.mono fun i hi ↦ (continuous_pow m).continuousOn.mul hi
  have hten :=
    (tendstoUniformlyOn_pow_mul F.radius_pos m huc).tendsto_circleIntegral_of_continuousOn
      F.radius_pos.le hcont'
  have hL : ∀ i, (∮ t in C((0 : ℂ), r), t ^ m * (deriv (fN i) t / fN i t))
      = (2 * (Real.pi : ℂ) * Complex.I) * ∑ j, (FN i).root j ^ m :=
    fun i ↦ (FN i).circleIntegral_pow_logDeriv m
  rw [F.circleIntegral_pow_logDeriv m] at hten
  simp only [hL] at hten
  have hmul := hten.const_mul (2 * (Real.pi : ℂ) * Complex.I)⁻¹
  simp only [inv_mul_cancel_left₀ Complex.two_pi_I_ne_zero] at hmul
  exact hmul

/-- The packet polynomials converge coefficient by coefficient. -/
theorem tendsto_packetPoly_coeff [φ.IsCountablyGenerated]
    (F : PacketFactor f r k) (FN : ∀ i, PacketFactor (fN i) r k)
    (hcont : ∀ᶠ i in φ,
      ContinuousOn (fun t ↦ deriv (fN i) t / fN i t) (Metric.sphere (0 : ℂ) r))
    (huc : TendstoUniformlyOn (fun i t ↦ deriv (fN i) t / fN i t)
      (fun t ↦ deriv f t / f t) φ (Metric.sphere (0 : ℂ) r)) (m : ℕ) :
    Tendsto (fun i ↦ (packetPoly (FN i).root).coeff m) φ
      (𝓝 ((packetPoly F.root).coeff m)) := by
  rcases le_or_gt m k with hm | hm
  · have e1 : ∀ i, (packetPoly (FN i).root).coeff m
        = (-1) ^ (k - m) * esymmC ((FN i).root) (k - m) := fun i ↦ packetPoly_coeff _ hm
    have e2 : (packetPoly F.root).coeff m = (-1) ^ (k - m) * esymmC F.root (k - m) :=
      packetPoly_coeff _ hm
    rw [e2]
    simp only [e1]
    exact Tendsto.const_mul _
      (tendsto_esymmC_of_tendsto_psum (fun n _ ↦ tendsto_psum_root F FN hcont huc n) (k - m))
  · have e1 : ∀ i, (packetPoly (FN i).root).coeff m = 0 := fun i ↦ packetPoly_coeff_of_lt _ hm
    have e2 : (packetPoly F.root).coeff m = 0 := packetPoly_coeff_of_lt _ hm
    rw [e2]
    simp only [e1]
    exact tendsto_const_nhds

/-- The product of the packet converges. -/
theorem tendsto_root_prod [φ.IsCountablyGenerated]
    (F : PacketFactor f r k) (FN : ∀ i, PacketFactor (fN i) r k)
    (hcont : ∀ᶠ i in φ,
      ContinuousOn (fun t ↦ deriv (fN i) t / fN i t) (Metric.sphere (0 : ℂ) r))
    (huc : TendstoUniformlyOn (fun i t ↦ deriv (fN i) t / fN i t)
      (fun t ↦ deriv f t / f t) φ (Metric.sphere (0 : ℂ) r)) :
    Tendsto (fun i ↦ ∏ j, (FN i).root j) φ (𝓝 (∏ j, F.root j)) := by
  have h := (tendsto_packetPoly_coeff F FN hcont huc 0).const_mul ((-1 : ℂ) ^ k)
  simpa only [neg_one_pow_mul_packetPoly_coeff_zero] using h

end Convergence

/-! ### The bridge to `RoucheAnalytic` -/

/-- The packet product is `Shields.zeroFactor` of the packet's root multiset. -/
theorem zeroFactor_map_univ {k : ℕ} (a : Fin k → ℂ) (t : ℂ) :
    zeroFactor (Multiset.map a Finset.univ.val) t = ∏ j, (t - a j) := by
  rw [zeroFactor, Multiset.map_map, Finset.prod_eq_multiset_prod]
  rfl

/-- The packet polynomial evaluates to the packet product. -/
theorem eval_packetPoly {k : ℕ} (a : Fin k → ℂ) (t : ℂ) :
    (packetPoly a).eval t = ∏ j, (t - a j) := by
  simp [packetPoly, Polynomial.eval_prod]

/-- The roots of the packet polynomial are the packet, with multiplicity. -/
theorem roots_packetPoly {k : ℕ} (a : Fin k → ℂ) :
    (packetPoly a).roots = Multiset.map a Finset.univ.val := by
  have hprod : packetPoly a
      = (Multiset.map (fun t ↦ Polynomial.X - Polynomial.C t)
          (Multiset.map a (Finset.univ : Finset (Fin k)).val)).prod := by
    rw [packetPoly, Finset.prod_eq_multiset_prod, Multiset.map_map]
    rfl
  rw [hprod, Polynomial.roots_multiset_prod_X_sub_C]

/-- **The bridge.**  The `k` carried by a `PacketFactor` is `RoucheAnalytic`'s zero count: the
number of zeros of `f` in the open disc, counted by `analyticOrderNatAt`.  Nothing beyond the
structure's own hypotheses is needed, so the copied count `PacketFactor.circleIntegral_logDeriv`
and `Shields.circleIntegral_logDeriv` compute the same integer. -/
theorem PacketFactor.zeroCount_eq {f : ℂ → ℂ} {r : ℝ} {k : ℕ} (F : PacketFactor f r k) :
    zeroCount f 0 r = k := by
  have hg : AnalyticOnNhd ℂ F.cofactor (closedBall (0 : ℂ) r) :=
    (F.cofactor_differentiable.differentiableOn.analyticOnNhd isOpen_univ).mono
      (Set.subset_univ _)
  have hcard := zeroCount_eq_card (f := f) (g := F.cofactor) (c := (0 : ℂ)) (R := r)
    (s := Multiset.map F.root Finset.univ.val)
    (fun u hu ↦ by
      obtain ⟨j, _, rfl⟩ := Multiset.mem_map.1 hu
      exact mem_ball_zero_iff.2 (F.root_mem_ball j))
    hg (fun z hz ↦ F.cofactor_ne_zero z (mem_closedBall_zero_iff.1 hz))
    (fun z ↦ by rw [zeroFactor_map_univ]; exact F.eq_prod z)
  simpa using hcard

/-- The copied count and `RoucheAnalytic`'s argument principle agree.  Deriving
`PacketFactor.circleIntegral_logDeriv` a second time, through `PacketFactor.zeroCount_eq` and
`Shields.circleIntegral_logDeriv`, checks the two routes against each other on the one
statement they both make. -/
theorem PacketFactor.circleIntegral_logDeriv_via_zeroCount {f : ℂ → ℂ} {r : ℝ} {k : ℕ}
    (F : PacketFactor f r k) :
    (∮ t in C((0 : ℂ), r), deriv f t / f t) = (2 * (Real.pi : ℂ) * Complex.I) * k := by
  have hf : AnalyticOnNhd ℂ f (closedBall (0 : ℂ) r) :=
    (F.differentiable.differentiableOn.analyticOnNhd isOpen_univ).mono (Set.subset_univ _)
  rw [Shields.circleIntegral_logDeriv F.radius_pos hf
      (fun z hz ↦ F.ne_zero_of_norm_eq (mem_sphere_zero_iff_norm.1 hz)),
    F.zeroCount_eq]
  ring

/-! ### Packets of a merely analytic function -/

/-- A `PacketFactor` whose cofactor is only analytic on the closed disc.  This is the weakest
hypothesis under which the argument principle argument runs, and — unlike `PacketFactor`, whose
cofactor is entire — it is available for **every** function analytic on a neighborhood of the
closed disc with no zero on the circle: see `exists_analyticPacket`.  A function analytic only on a
disc need not extend to an entire function, so the entire cofactor of `PacketFactor` is a genuine
restriction and not a normalization. -/
structure AnalyticPacket (f : ℂ → ℂ) (r : ℝ) (k : ℕ) where
  /-- The contour radius is positive. -/
  radius_pos : 0 < r
  /-- The enclosed zeros, listed with multiplicity. -/
  root : Fin k → ℂ
  /-- The zero-free cofactor. -/
  cofactor : ℂ → ℂ
  /-- Every root lies strictly inside the contour. -/
  root_mem_ball : ∀ j, ‖root j‖ < r
  /-- The cofactor is analytic on a neighborhood of the closed disc. -/
  cofactor_analyticOnNhd : AnalyticOnNhd ℂ cofactor (closedBall (0 : ℂ) r)
  /-- The cofactor has no zero on the closed disc: the listed roots are all of them. -/
  cofactor_ne_zero : ∀ t : ℂ, ‖t‖ ≤ r → cofactor t ≠ 0
  /-- The factorization itself. -/
  eq_prod : ∀ t : ℂ, f t = (∏ j, (t - root j)) * cofactor t

/-- The copied structure is a special case: an entire cofactor is analytic on the closed disc. -/
def PacketFactor.toAnalyticPacket {f : ℂ → ℂ} {r : ℝ} {k : ℕ} (F : PacketFactor f r k) :
    AnalyticPacket f r k where
  radius_pos := F.radius_pos
  root := F.root
  cofactor := F.cofactor
  root_mem_ball := F.root_mem_ball
  cofactor_analyticOnNhd :=
    (F.cofactor_differentiable.differentiableOn.analyticOnNhd isOpen_univ).mono (Set.subset_univ _)
  cofactor_ne_zero := F.cofactor_ne_zero
  eq_prod := F.eq_prod

namespace AnalyticPacket

variable {f : ℂ → ℂ} {r : ℝ} {k : ℕ}

/-- The root multiset of the packet. -/
noncomputable def rootMultiset (F : AnalyticPacket f r k) : Multiset ℂ :=
  Multiset.map F.root Finset.univ.val

theorem card_rootMultiset (F : AnalyticPacket f r k) :
    Multiset.card F.rootMultiset = k := by simp [rootMultiset]

theorem rootMultiset_mem_ball (F : AnalyticPacket f r k) {u : ℂ} (hu : u ∈ F.rootMultiset) :
    u ∈ ball (0 : ℂ) r := by
  obtain ⟨j, _, rfl⟩ := Multiset.mem_map.1 hu
  exact mem_ball_zero_iff.2 (F.root_mem_ball j)

theorem eq_zeroFactor_mul (F : AnalyticPacket f r k) (t : ℂ) :
    f t = zeroFactor F.rootMultiset t * F.cofactor t := by
  rw [rootMultiset, zeroFactor_map_univ]; exact F.eq_prod t

/-- The function of an analytic packet is analytic on a neighborhood of the closed disc. -/
theorem analyticOnNhd (F : AnalyticPacket f r k) :
    AnalyticOnNhd ℂ f (closedBall (0 : ℂ) r) := by
  have hfe : f = fun t ↦ zeroFactor F.rootMultiset t * F.cofactor t :=
    funext F.eq_zeroFactor_mul
  rw [hfe]
  exact fun t ht ↦ (analyticAt_zeroFactor _ t).mul (F.cofactor_analyticOnNhd t ht)

theorem sub_root_ne_zero (F : AnalyticPacket f r k) {t : ℂ} (ht : ‖t‖ = r) (j : Fin k) :
    t - F.root j ≠ 0 := by
  intro h
  rw [sub_eq_zero] at h
  exact absurd (h ▸ ht) (ne_of_lt (F.root_mem_ball j))

/-- The contour carries no zero. -/
theorem ne_zero_of_norm_eq (F : AnalyticPacket f r k) {t : ℂ} (ht : ‖t‖ = r) : f t ≠ 0 := by
  rw [F.eq_prod]
  exact mul_ne_zero (Finset.prod_ne_zero_iff.2 fun j _ ↦ F.sub_root_ne_zero ht j)
    (F.cofactor_ne_zero t ht.le)

-- `t` now comes from analyticity on the closed disc rather than from entirety.
/-- The logarithmic derivative splits over the packet and the cofactor. -/
theorem logDeriv_eq (F : AnalyticPacket f r k) {t : ℂ} (ht : ‖t‖ = r) :
    deriv f t / f t = (∑ j, (t - F.root j)⁻¹) + deriv F.cofactor t / F.cofactor t := by
  have htc : t ∈ closedBall (0 : ℂ) r := mem_closedBall_zero_iff.2 ht.le
  have hdg : DifferentiableAt ℂ F.cofactor t := (F.cofactor_analyticOnNhd t htc).differentiableAt
  have hfe : f = fun s : ℂ ↦ (∏ j, (s - F.root j)) * F.cofactor s := funext F.eq_prod
  have hp : (∏ j, (t - F.root j)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun j _ ↦ F.sub_root_ne_zero ht j
  have hg : F.cofactor t ≠ 0 := F.cofactor_ne_zero t ht.le
  have hdp : DifferentiableAt ℂ (fun s : ℂ ↦ ∏ j, (s - F.root j)) t :=
    (Differentiable.fun_finsetProd fun j _ ↦ differentiable_id.sub_const _) t
  have h1 : logDeriv f t
      = logDeriv (fun s : ℂ ↦ (∏ j, (s - F.root j)) * F.cofactor s) t :=
    congrArg (fun u : ℂ → ℂ ↦ logDeriv u t) hfe
  have h2 : logDeriv (fun s : ℂ ↦ (∏ j, (s - F.root j)) * F.cofactor s) t
      = logDeriv (fun s : ℂ ↦ ∏ j, (s - F.root j)) t + logDeriv F.cofactor t :=
    logDeriv_mul t hp hg hdp hdg
  have h3 : logDeriv (fun s : ℂ ↦ ∏ j, (s - F.root j)) t = ∑ j, (t - F.root j)⁻¹ := by
    rw [logDeriv_prod (f := fun (j : Fin k) (s : ℂ) ↦ s - F.root j)
      (fun j _ ↦ F.sub_root_ne_zero ht j) (fun j _ ↦ by fun_prop)]
    exact Finset.sum_congr rfl fun j _ ↦ by
      simp [logDeriv_apply, one_div]
  rw [show deriv f t / f t = logDeriv f t from rfl, h1, h2, h3, logDeriv_apply]

-- weight `φ` are now analytic on a neighborhood of the closed disc rather than entire.
/-- **The weighted argument principle for analytic functions.**  For `φ` analytic on a
neighborhood of the closed disc,
\[
  \oint_{|t| = r} \varphi(t)\,\frac{f'(t)}{f(t)}\,dt = 2\pi i \sum_j \varphi(a_j),
\]
the sum over the packet with multiplicity.  Neither `RoucheAnalytic` nor `Weierstrass` carries a
general weight; both carry a general center, which this does not.  At `φ = 1` this is the center-`0`
case of `Shields.circleIntegral_logDeriv` and at `φ = t^m` the center-`0` case of
`Shields.circleIntegral_pow_mul_logDeriv_of_zeroFactor`. -/
theorem weighted_argumentPrinciple (F : AnalyticPacket f r k) {φ : ℂ → ℂ}
    (hφ : AnalyticOnNhd ℂ φ (closedBall (0 : ℂ) r)) :
    (∮ t in C((0 : ℂ), r), φ t * (deriv f t / f t))
      = (2 * (Real.pi : ℂ) * Complex.I) * ∑ j, φ (F.root j) := by
  have hr := F.radius_pos
  have hdc : AnalyticOnNhd ℂ (deriv F.cofactor) (closedBall (0 : ℂ) r) :=
    F.cofactor_analyticOnNhd.deriv
  set g : ℂ → ℂ := fun t ↦ φ t * (deriv F.cofactor t / F.cofactor t) with hgdef
  have hgdiff : ∀ t ∈ closedBall (0 : ℂ) r, DifferentiableAt ℂ g t := fun t ht ↦
    (hφ t ht).differentiableAt.mul (((hdc t ht).differentiableAt).div
      ((F.cofactor_analyticOnNhd t ht).differentiableAt)
      (F.cofactor_ne_zero t (mem_closedBall_zero_iff.1 ht)))
  have hgcont : ContinuousOn g (closedBall (0 : ℂ) r) := fun t ht ↦
    ((hgdiff t ht).continuousAt).continuousWithinAt
  have hrootcont : ∀ j : Fin k,
      ContinuousOn (fun t : ℂ ↦ φ t / (t - F.root j)) (sphere (0 : ℂ) r) := by
    intro j t ht
    have htc : t ∈ closedBall (0 : ℂ) r := sphere_subset_closedBall ht
    have hne : t - F.root j ≠ 0 := F.sub_root_ne_zero (mem_sphere_zero_iff_norm.1 ht) j
    exact (((hφ t htc).continuousAt).div (by fun_prop) hne).continuousWithinAt
  have hrootint : ∀ j ∈ (Finset.univ : Finset (Fin k)),
      CircleIntegrable (fun t : ℂ ↦ φ t / (t - F.root j)) 0 r :=
    fun j _ ↦ (hrootcont j).circleIntegrable hr.le
  have hsumint : CircleIntegrable (fun t : ℂ ↦ ∑ j, φ t / (t - F.root j)) 0 r :=
    (continuousOn_finsetSum _ fun j _ ↦ hrootcont j).circleIntegrable hr.le
  have hgint : CircleIntegrable g 0 r :=
    (hgcont.mono sphere_subset_closedBall).circleIntegrable hr.le
  have hEq : Set.EqOn (fun t ↦ φ t * (deriv f t / f t))
      (fun t ↦ (∑ j, φ t / (t - F.root j)) + g t) (sphere (0 : ℂ) r) := by
    intro t ht
    have hn := mem_sphere_zero_iff_norm.1 ht
    simp only [hgdef]
    rw [F.logDeriv_eq hn, mul_add, Finset.mul_sum]
    congr 1
  have hzero : (∮ t in C((0 : ℂ), r), g t) = 0 :=
    Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable hr.le Set.countable_empty
      hgcont fun t ht ↦ hgdiff t (ball_subset_closedBall ht.1)
  have hroot : ∀ j : Fin k, (∮ t in C((0 : ℂ), r), φ t / (t - F.root j))
      = 2 * (Real.pi : ℂ) * Complex.I * φ (F.root j) := fun j ↦
    Complex.circleIntegral_div_sub_of_differentiable_on_off_countable Set.countable_empty
      (mem_ball_zero_iff.2 (F.root_mem_ball j)) hφ.continuousOn
      fun t ht ↦ (hφ t (ball_subset_closedBall ht.1)).differentiableAt
  rw [circleIntegral.integral_congr hr.le hEq, circleIntegral.integral_add hsumint hgint,
    circleIntegral.integral_fun_sum hrootint, hzero, add_zero,
    Finset.sum_congr rfl fun j (_ : j ∈ Finset.univ) ↦ hroot j, Finset.mul_sum]

/-- The count. -/
theorem circleIntegral_logDeriv (F : AnalyticPacket f r k) :
    (∮ t in C((0 : ℂ), r), deriv f t / f t) = (2 * (Real.pi : ℂ) * Complex.I) * k := by
  have h := F.weighted_argumentPrinciple (φ := fun _ ↦ (1 : ℂ)) analyticOnNhd_const
  simpa using h

/-- The power sums of the packet, for `f` merely analytic on the closed disc. -/
theorem circleIntegral_pow_logDeriv (F : AnalyticPacket f r k) (m : ℕ) :
    (∮ t in C((0 : ℂ), r), t ^ m * (deriv f t / f t))
      = (2 * (Real.pi : ℂ) * Complex.I) * ∑ j, F.root j ^ m :=
  F.weighted_argumentPrinciple (φ := fun t ↦ t ^ m)
    (fun _t _ ↦ analyticAt_id.pow m)

/-- **The bridge, analytic case.**  The `k` of an `AnalyticPacket` is `RoucheAnalytic`'s zero
count. -/
theorem zeroCount_eq (F : AnalyticPacket f r k) : zeroCount f 0 r = k := by
  have hcard := zeroCount_eq_card (f := f) (g := F.cofactor) (c := (0 : ℂ)) (R := r)
    (s := F.rootMultiset) (fun u hu ↦ F.rootMultiset_mem_ball hu) F.cofactor_analyticOnNhd
    (fun z hz ↦ F.cofactor_ne_zero z (mem_closedBall_zero_iff.1 hz)) F.eq_zeroFactor_mul
  rw [hcard, F.card_rootMultiset]

end AnalyticPacket

/-! ### Analytic Weierstrass preparation -/

/-- A multiset of complex numbers is the image of a tuple indexed by `Fin` of its cardinality.
`Shields.exists_fintype_map_univ` gives the same enumeration with an unspecified index bound;
the cardinality is what the packet structures need, and it is not imported here because that module
is not among this file's dependencies. -/
theorem exists_fin_card_map_univ (s : Multiset ℂ) :
    ∃ a : Fin (Multiset.card s) → ℂ, Multiset.map a Finset.univ.val = s := by
  obtain ⟨n, a, ha⟩ : ∃ (n : ℕ) (a : Fin n → ℂ), Multiset.map a Finset.univ.val = s :=
    ⟨s.toList.length, s.toList.get, by rw [Fin.univ_val_map, List.ofFn_get, Multiset.coe_toList]⟩
  have hn : n = Multiset.card s := by rw [← ha]; simp
  subst hn
  exact ⟨a, ha⟩

/-- **Every analytic function with a zero-free circle carries a packet.**  This is what
`PacketFactor` cannot supply: its cofactor is entire, and the cofactor produced here is analytic
only where `f` is.  The packet's cardinality is `Shields.zeroCount`. -/
theorem exists_analyticPacket {f : ℂ → ℂ} {r : ℝ} (hr : 0 < r)
    (hf : AnalyticOnNhd ℂ f (closedBall (0 : ℂ) r)) (hns : ∀ t : ℂ, ‖t‖ = r → f t ≠ 0) :
    Nonempty (AnalyticPacket f r (zeroCount f 0 r)) := by
  have hns' : ∀ z ∈ sphere (0 : ℂ) r, f z ≠ 0 := fun z hz ↦
    hns z (mem_sphere_zero_iff_norm.1 hz)
  obtain ⟨s, g, hsmem, hg, hgne, hfac⟩ := exists_zeroFactor hr hf hns'
  obtain ⟨a, ha⟩ := exists_fin_card_map_univ s
  have hcard : zeroCount f 0 r = Multiset.card s := zeroCount_eq_card hsmem hg hgne hfac
  rw [hcard]
  exact ⟨{ radius_pos := hr
           root := a
           cofactor := g
           root_mem_ball := fun j ↦ mem_ball_zero_iff.1 (hsmem _
             (ha ▸ Multiset.mem_map_of_mem a (Finset.mem_univ j)))
           cofactor_analyticOnNhd := hg
           cofactor_ne_zero := fun t ht ↦ hgne t (mem_closedBall_zero_iff.2 ht)
           eq_prod := fun t ↦ by rw [hfac t, ← zeroFactor_map_univ a t, ha] }⟩

/-- **Analytic Weierstrass preparation with a root tuple.**  For `f` analytic on a neighborhood of
the closed disc with no zero on the circle, there is a tuple `a` of `zeroCount f 0 r` points of the
open disc and an analytic zero-free `g` with `f = W · g`, where `W = packetPoly a` is monic of
degree `zeroCount f 0 r`.  `Shields.exists_analytic_preparation` proves the same factorization
with `W`'s roots presented as a multiset; the tuple is what the `esymmC` machinery consumes. -/
theorem exists_monic_analytic_preparation_packet {f : ℂ → ℂ} {r : ℝ} (hr : 0 < r)
    (hf : AnalyticOnNhd ℂ f (closedBall (0 : ℂ) r)) (hns : ∀ t : ℂ, ‖t‖ = r → f t ≠ 0) :
    ∃ (a : Fin (zeroCount f 0 r) → ℂ) (g : ℂ → ℂ),
      (∀ j, ‖a j‖ < r) ∧ (packetPoly a).Monic ∧
      (packetPoly a).natDegree = zeroCount f 0 r ∧
      AnalyticOnNhd ℂ g (closedBall (0 : ℂ) r) ∧
      (∀ z ∈ closedBall (0 : ℂ) r, g z ≠ 0) ∧
      ∀ z : ℂ, f z = (packetPoly a).eval z * g z := by
  obtain ⟨F⟩ := exists_analyticPacket hr hf hns
  exact ⟨F.root, F.cofactor, F.root_mem_ball, packetPoly_monic _, packetPoly_natDegree _,
    F.cofactor_analyticOnNhd,
    fun z hz ↦ F.cofactor_ne_zero z (mem_closedBall_zero_iff.1 hz),
    fun z ↦ by rw [eval_packetPoly]; exact F.eq_prod z⟩

/-- The multiplicity clause behind `Shields.zeroCount_eq_card`, stated pointwise: in a
factorization `f = (∏_{u ∈ s} (· - u)) · g` with `g` zero-free on the closed disc, the vanishing
order of `f` at a point of the disc is the multiplicity of that point in `s`.  The proof is the
inner step of `zeroCount_eq_card`, which sums this over the disc. -/
theorem analyticOrderNatAt_eq_count {f g : ℂ → ℂ} {c : ℂ} {R : ℝ} {s : Multiset ℂ}
    (hg : AnalyticOnNhd ℂ g (closedBall c R)) (hgne : ∀ z ∈ closedBall c R, g z ≠ 0)
    (hfac : ∀ z, f z = zeroFactor s z * g z) {u : ℂ} (hu : u ∈ closedBall c R) :
    analyticOrderNatAt f u = s.count u := by
  have hfeq : f = fun z ↦ zeroFactor s z * g z := funext hfac
  set m := s.count u with hm
  set t := s - Multiset.replicate m u with ht
  have hle : Multiset.replicate m u ≤ s := Multiset.le_count_iff_replicate_le.mp le_rfl
  have hst : Multiset.replicate m u + t = s := by
    rw [ht, add_comm]; exact Multiset.sub_add_cancel hle
  have hut : u ∉ t := by
    rw [← Multiset.count_eq_zero, ht, Multiset.count_sub, Multiset.count_replicate_self, ← hm]
    omega
  have hfu : ∀ z, f z = (z - u) ^ m * (zeroFactor t z * g z) := by
    intro z
    rw [hfac z, ← hst, zeroFactor_add, zeroFactor_replicate, mul_assoc]
  have hanal : AnalyticAt ℂ (fun z ↦ zeroFactor t z * g z) u :=
    (analyticAt_zeroFactor t u).mul (hg u hu)
  have hne : zeroFactor t u * g u ≠ 0 :=
    mul_ne_zero (zeroFactor_ne_zero fun v hv h ↦ hut (by rw [h]; exact hv)) (hgne u hu)
  have hfan : AnalyticAt ℂ f u := by
    rw [hfeq]; exact (analyticAt_zeroFactor s u).mul (hg u hu)
  have horder : analyticOrderAt f u = (m : ℕ∞) :=
    hfan.analyticOrderAt_eq_natCast.mpr ⟨_, hanal, hne,
      Filter.Eventually.of_forall fun z ↦ by simpa [smul_eq_mul] using hfu z⟩
  simp [analyticOrderNatAt, horder]

/-- **The multiplicities of the preparation polynomial are the vanishing orders of `f`.**  This is
what `Shields.exists_analytic_preparation` leaves unstated: it fixes `W`'s degree and confines
`W`'s roots to the open disc, but not the multiplicity at each point. -/
theorem rootMultiplicity_packetPoly_eq_analyticOrderNatAt {f : ℂ → ℂ} {r : ℝ} {k : ℕ}
    (F : AnalyticPacket f r k) {u : ℂ} (hu : ‖u‖ ≤ r) :
    (packetPoly F.root).rootMultiplicity u = analyticOrderNatAt f u := by
  have huc : u ∈ closedBall (0 : ℂ) r := mem_closedBall_zero_iff.2 hu
  rw [← Polynomial.count_roots, roots_packetPoly, ← AnalyticPacket.rootMultiset]
  exact (analyticOrderNatAt_eq_count F.cofactor_analyticOnNhd
    (fun z hz ↦ F.cofactor_ne_zero z (mem_closedBall_zero_iff.1 hz)) F.eq_zeroFactor_mul huc).symm

/-! ### Count stability through Rouché -/

/-- **Count stability from uniform convergence of the functions alone.**  The copied
`eventually_card_eq` proves the same conclusion for `PacketFactor`s, but needs uniform convergence
of the logarithmic derivatives, hence of the derivatives; its module notes that the route was taken
because Mathlib has no Rouché theorem.  `RoucheAnalytic` supplies one, and Hurwitz through Rouché
drops the hypothesis on the derivatives, so that route is preferable wherever the packets are
analytic.  The copied route remains the one available when only the two counting integrals are
under control and no factorization of the difference is at hand. -/
theorem AnalyticPacket.eventually_card_eq {r : ℝ} (hr : 0 < r) {k : ℕ} {kN : ℕ → ℕ}
    {f : ℂ → ℂ} {fN : ℕ → ℂ → ℂ}
    (F : AnalyticPacket f r k) (FN : ∀ n, AnalyticPacket (fN n) r (kN n))
    (hunif : TendstoUniformlyOn fN f atTop (sphere (0 : ℂ) r)) :
    ∀ᶠ n in atTop, kN n = k := by
  have h := eventually_zeroCount_eq hr (fun n ↦ (FN n).analyticOnNhd) F.analyticOnNhd hunif
    (fun z hz ↦ F.ne_zero_of_norm_eq (mem_sphere_zero_iff_norm.1 hz))
  filter_upwards [h] with n hn
  rwa [(FN n).zeroCount_eq, F.zeroCount_eq] at hn

end Shields
