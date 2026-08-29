/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.RemovableSingularity
import Shields.Analysis.Complex.ArgumentPrinciple.Polynomial

/-!
# The argument principle and Rouché's theorem for analytic functions

The same two theorems as in the polynomial case, for a function analytic on a neighborhood of a
closed disc, with multiplicity measured by `analyticOrderNatAt`.

## Main results

* `Shields.zeroCount`: the number of zeros of `f` in the open disc, with multiplicity.
* `Shields.circleIntegral_logDeriv`: **the argument principle** -- the contour integral of `f' / f`
  is `2πi * zeroCount f c R`.
* `Shields.zeroCount_add_eq`: **Rouché** -- if `‖g‖ < ‖f‖` on the circle then `f` and `f + g` have
  the same count.
* `Shields.eventually_zeroCount_eq`, `Shields.eventually_zeroCount_eq_one`: **Hurwitz**, and its
  simple-zero form.
* `Shields.zeroCount_add_eq_one`: the perturbation form -- one zero stays one zero.
* `Shields.logDeriv_prod_sub_mul`: the logarithmic derivative of a displayed factorization.
* `Shields.analyticAt_dslope`, `Shields.analyticOnNhd_iterate_dslope`: dividing a zero out without
  leaving the analytic class.  Neither asks for `U` open, which is what lets the closed-disc
  factorization in `Shields.Analysis.Complex.Rouche` consume them on a `closedBall`.
* `Shields.not_eventually_eq_zero_of_ne_zero_on_sphere`, `Shields.finite_zeros_of_analyticOnNhd`,
  `Shields.finite_zeros_of_ne_zero_on_sphere`: the zero set on a closed disc is isolated and
  finite.  The middle one takes the no-local-vanishing hypothesis directly, so a caller whose
  function *does* vanish on the circle can still use it.

## Implementation notes

`exists_zeroFactor` replaces the polynomial case's split factorization: on a disc where `f` has no
zero on the boundary circle, `f` is a product of linear factors times a zero-free analytic cofactor.
That is what makes the logarithmic derivative computable, and it is where all the analysis sits.

Multiplicity is Mathlib's `analyticOrderNatAt`, so `zeroCount` agrees with the usual notion rather
than with a bespoke one.

## Tags

argument principle, Rouché, Hurwitz, analytic function, zero counting, contour integral
-/

namespace Shields

open Complex Metric Filter

open scoped Topology

/-! ### The polynomial factor carrying the zeros -/

/-- `∏_{u ∈ s} (z - u)`, for a multiset `s` of points repeated with multiplicity. -/
noncomputable def zeroFactor (s : Multiset ℂ) (z : ℂ) : ℂ := (s.map fun u => z - u).prod

@[simp] theorem zeroFactor_zero (z : ℂ) : zeroFactor 0 z = 1 := by simp [zeroFactor]

theorem zeroFactor_cons (u : ℂ) (s : Multiset ℂ) (z : ℂ) :
    zeroFactor (u ::ₘ s) z = (z - u) * zeroFactor s z := by
  simp [zeroFactor]

theorem zeroFactor_add (s t : Multiset ℂ) (z : ℂ) :
    zeroFactor (s + t) z = zeroFactor s z * zeroFactor t z := by
  simp [zeroFactor]

theorem zeroFactor_replicate (m : ℕ) (u z : ℂ) :
    zeroFactor (Multiset.replicate m u) z = (z - u) ^ m := by
  simp [zeroFactor]

theorem zeroFactor_ne_zero {s : Multiset ℂ} {z : ℂ} (hz : ∀ u ∈ s, z ≠ u) :
    zeroFactor s z ≠ 0 := by
  refine Multiset.prod_ne_zero fun h0 => ?_
  obtain ⟨u, hu, heq⟩ := Multiset.mem_map.mp h0
  exact hz u hu (sub_eq_zero.mp heq)

theorem zeroFactor_eq_zero {s : Multiset ℂ} {z : ℂ} (hz : z ∈ s) : zeroFactor s z = 0 := by
  refine Multiset.prod_eq_zero ?_
  exact Multiset.mem_map.mpr ⟨z, hz, sub_self z⟩

theorem differentiable_zeroFactor (s : Multiset ℂ) : Differentiable ℂ (zeroFactor s) := by
  induction s using Multiset.induction_on with
  | empty =>
    have h : zeroFactor (0 : Multiset ℂ) = fun _ : ℂ => (1 : ℂ) := funext fun w => by simp
    rw [h]
    exact differentiable_const 1
  | cons u s ih =>
    have h : zeroFactor (u ::ₘ s) = fun z => (z - u) * zeroFactor s z :=
      funext fun z => zeroFactor_cons u s z
    rw [h]
    exact (differentiable_id.sub_const u).mul ih

theorem analyticAt_zeroFactor (s : Multiset ℂ) (z : ℂ) : AnalyticAt ℂ (zeroFactor s) z := by
  have h : DifferentiableOn ℂ (zeroFactor s) Set.univ :=
    (differentiable_zeroFactor s).differentiableOn
  exact h.analyticAt Filter.univ_mem

/-- The logarithmic derivative of `∏_{u ∈ s} (z - u)` is the sum of the simple poles. -/
theorem logDeriv_zeroFactor {s : Multiset ℂ} {z : ℂ} (hz : ∀ u ∈ s, z ≠ u) :
    logDeriv (zeroFactor s) z = (s.map fun u => (z - u)⁻¹).sum := by
  induction s using Multiset.induction_on with
  | empty =>
    have h : zeroFactor (0 : Multiset ℂ) = fun _ : ℂ => (1 : ℂ) := funext fun w => by simp
    rw [h]
    simp [logDeriv_apply]
  | cons u s ih =>
    have hzu : z ≠ u := hz u (Multiset.mem_cons_self u s)
    have hrest : ∀ v ∈ s, z ≠ v := fun v hv => hz v (Multiset.mem_cons_of_mem hv)
    have h : zeroFactor (u ::ₘ s) = fun w => (w - u) * zeroFactor s w :=
      funext fun w => zeroFactor_cons u s w
    have hd1 : DifferentiableAt ℂ (fun w : ℂ => w - u) z :=
      (differentiable_id.sub_const u).differentiableAt
    have hmul := logDeriv_mul (f := fun w : ℂ => w - u) (g := zeroFactor s) z
      (sub_ne_zero.mpr hzu) (zeroFactor_ne_zero hrest) hd1 ((differentiable_zeroFactor s) z)
    have h1 : logDeriv (fun w : ℂ => w - u) z = (z - u)⁻¹ := by
      simp [logDeriv_apply, one_div]
    rw [h, hmul, h1, ih hrest, Multiset.map_cons, Multiset.sum_cons]

/-- **The logarithmic derivative of a displayed factorization.**  If `f` is a finite product of
linear factors times a cofactor `G`, then off the roots and off the zeros of `G`,
`f'/f = ∑_j (z - a_j)⁻¹ + G'/G`.

Stated for an arbitrary index type and an arbitrary `Finset`, because the packets index their
roots by `Fin k` and the closed-disc factorizations by `Finset.range n`; the multiset form is
`Shields.logDeriv_zeroFactor`. -/
theorem logDeriv_prod_sub_mul {ι : Type*} {s : Finset ι} {a : ι → ℂ} {f G : ℂ → ℂ} {z : ℂ}
    (hf : f = fun w => (∏ j ∈ s, (w - a j)) * G w) (hsub : ∀ j ∈ s, z - a j ≠ 0) (hG : G z ≠ 0)
    (hGd : DifferentiableAt ℂ G z) :
    deriv f z / f z = (∑ j ∈ s, (z - a j)⁻¹) + deriv G z / G z := by
  have hPz : (∏ j ∈ s, (z - a j)) ≠ 0 := Finset.prod_ne_zero_iff.mpr hsub
  have hPd : DifferentiableAt ℂ (fun w => ∏ j ∈ s, (w - a j)) z := by fun_prop
  have hmul : logDeriv f z = logDeriv (fun w => ∏ j ∈ s, (w - a j)) z + logDeriv G z := by
    rw [hf]
    exact logDeriv_mul z hPz hG hPd hGd
  have hprod : logDeriv (fun w => ∏ j ∈ s, (w - a j)) z = ∑ j ∈ s, (z - a j)⁻¹ := by
    rw [logDeriv_prod (f := fun j w => w - a j) hsub fun j _ => by fun_prop]
    exact Finset.sum_congr rfl fun j _ => by simp [logDeriv_apply]
  rw [hprod] at hmul
  simpa only [logDeriv_apply] using hmul

/-! ### Dividing out a zero -/

/-- `dslope F w` is analytic wherever `F` is.  Away from `w` it is a quotient with
nonvanishing denominator; at `w` it is `F`'s power series with the constant term
dropped and the rest shifted down. -/
theorem analyticAt_dslope {F : ℂ → ℂ} {w z : ℂ} (hFw : AnalyticAt ℂ F w)
    (hFz : AnalyticAt ℂ F z) : AnalyticAt ℂ (dslope F w) z := by
  rcases eq_or_ne z w with rfl | hzw
  · obtain ⟨p, hp⟩ := hFw
    exact ⟨p.fslope, hp.has_fpower_series_dslope_fslope⟩
  · have hloc : (fun u => (F u - F w) / (u - w)) =ᶠ[nhds z] dslope F w := by
      filter_upwards [dslope_eventuallyEq_slope_of_ne F hzw] with u hu
      rw [hu, slope_def_field]
    have hden : AnalyticAt ℂ (fun u : ℂ => u - w) z := analyticAt_id.sub analyticAt_const
    exact AnalyticAt.congr
      ((hFz.sub analyticAt_const).div hden (sub_ne_zero.mpr hzw)) hloc

/-- Iterated `dslope` preserves analyticity on any set containing the base point.

Openness of `U` is not needed: `AnalyticOnNhd` already asks for analyticity on a neighborhood of
each point, so `analyticAt_dslope` applies pointwise.  The closed-disc consumers depend on this,
their `U` being a `closedBall`. -/
theorem analyticOnNhd_iterate_dslope {U : Set ℂ} {u : ℂ} (hu : u ∈ U) :
    ∀ (m : ℕ) {f : ℂ → ℂ}, AnalyticOnNhd ℂ f U →
      AnalyticOnNhd ℂ ((Function.swap dslope u)^[m] f) U := by
  intro m
  induction m with
  | zero => intro f hf; simpa using hf
  | succ m ih =>
    intro f hf
    rw [Function.iterate_succ_apply]
    exact ih (fun z hz => analyticAt_dslope (hf u hu) (hf z hz))

/-- An analytic function not identically zero near `u` splits off the full power of `(· - u)`,
with the quotient analytic on the same open set and nonzero at `u`.  The identity is global: the
quotient is `dslope` iterated, not a division. -/
theorem exists_pow_factor {U : Set ℂ} {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f U)
    {u : ℂ} (hu : u ∈ U) (hnd : ¬ (∀ᶠ z in 𝓝 u, f z = 0)) :
    ∃ (m : ℕ) (g : ℂ → ℂ), AnalyticOnNhd ℂ g U ∧ g u ≠ 0 ∧ ∀ z, f z = (z - u) ^ m * g z := by
  obtain ⟨p, hp⟩ := hf u hu
  have hp0 : p ≠ 0 := fun h => hnd (hp.locally_zero_iff.mpr h)
  refine ⟨p.order, (Function.swap dslope u)^[p.order] f,
    analyticOnNhd_iterate_dslope hu _ hf, hp.iterate_dslope_fslope_ne_zero hp0, fun z => ?_⟩
  simpa [smul_eq_mul] using hp.eq_pow_order_mul_iterate_dslope z

/-! ### The zero set on a closed disc -/

/-- A zero of a function that does not vanish on the circle lies strictly
inside it. -/
theorem mem_ball_of_eq_zero {c : ℂ} {R : ℝ} {F : ℂ → ℂ}
    (hne : ∀ z ∈ Metric.sphere c R, F z ≠ 0) {w : ℂ}
    (hw : w ∈ Metric.closedBall c R) (hw0 : F w = 0) : w ∈ Metric.ball c R := by
  rcases lt_or_eq_of_le (Metric.mem_closedBall.mp hw) with h | h
  · exact Metric.mem_ball.mpr h
  · exact absurd hw0 (hne w (Metric.mem_sphere.mpr h))

/-- On the closed disk, a function analytic there and nonvanishing on the circle
is nowhere locally zero.  A local zero would propagate across the open disk by the
identity theorem and then reach the circle by continuity. -/
theorem not_eventually_eq_zero_of_ne_zero_on_sphere {c : ℂ} {R : ℝ} (hR : 0 < R) {F : ℂ → ℂ}
    (hF : AnalyticOnNhd ℂ F (Metric.closedBall c R))
    (hne : ∀ z ∈ Metric.sphere c R, F z ≠ 0) {w : ℂ} (hw : w ∈ Metric.closedBall c R) :
    ¬ ∀ᶠ z in nhds w, F z = 0 := by
  intro hzero
  have hwb : w ∈ Metric.ball c R := mem_ball_of_eq_zero hne hw hzero.self_of_nhds
  have hball : Set.EqOn F 0 (Metric.ball c R) :=
    (hF.mono Metric.ball_subset_closedBall).eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (convex_ball c R).isPreconnected hwb hzero
  have hz₀ : c + (R : ℂ) ∈ Metric.sphere c R := by simp [hR.le]
  have hz₀c : c + (R : ℂ) ∈ Metric.closedBall c R := Metric.sphere_subset_closedBall hz₀
  have hcl : c + (R : ℂ) ∈ closure (Metric.ball c R) := by
    rw [closure_ball c hR.ne']
    exact hz₀c
  haveI : (nhdsWithin (c + (R : ℂ)) (Metric.ball c R)).NeBot :=
    mem_closure_iff_nhdsWithin_neBot.mp hcl
  have h₁ : Filter.Tendsto F (nhdsWithin (c + (R : ℂ)) (Metric.ball c R))
      (nhds (F (c + (R : ℂ)))) := (hF _ hz₀c).continuousAt.continuousWithinAt
  have h₂ : Filter.Tendsto F (nhdsWithin (c + (R : ℂ)) (Metric.ball c R)) (nhds 0) := by
    refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    exact Filter.eventually_of_mem self_mem_nhdsWithin fun x hx => (hball hx).symm
  exact hne _ hz₀ (tendsto_nhds_unique h₁ h₂)

/-- **Isolated zeros are finitely many on a compact disk.**  A function analytic on the closed
disk and vanishing identically near no point of it has finitely many zeros there: an infinite
zero set would accumulate somewhere in the disk, and the analytic dichotomy at that point leaves
only the identically-zero alternative. -/
theorem finite_zeros_of_analyticOnNhd {c : ℂ} {R : ℝ} {F : ℂ → ℂ}
    (hF : AnalyticOnNhd ℂ F (Metric.closedBall c R))
    (hnd : ∀ w ∈ Metric.closedBall c R, ¬ ∀ᶠ z in nhds w, F z = 0) :
    {z ∈ Metric.closedBall c R | F z = 0}.Finite := by
  by_contra hinf
  obtain ⟨x, hx, hacc⟩ :=
    Set.Infinite.exists_accPt_of_subset_isCompact hinf (isCompact_closedBall c R)
      (fun z hz => hz.1)
  rcases (hF x hx).eventually_eq_zero_or_eventually_ne_zero with h | h
  · exact hnd x hx h
  · rw [accPt_iff_frequently_nhdsNE] at hacc
    obtain ⟨z, hz₁, hz₂⟩ := (hacc.and_eventually h).exists
    exact hz₂ hz₁.2

/-- The zeros in the closed disk are finite in number: they are isolated, and an
infinite subset of a compact set accumulates somewhere. -/
theorem finite_zeros_of_ne_zero_on_sphere {c : ℂ} {R : ℝ} (hR : 0 < R) {F : ℂ → ℂ}
    (hF : AnalyticOnNhd ℂ F (Metric.closedBall c R))
    (hne : ∀ z ∈ Metric.sphere c R, F z ≠ 0) :
    {z ∈ Metric.closedBall c R | F z = 0}.Finite :=
  finite_zeros_of_analyticOnNhd hF fun _ hw =>
    not_eventually_eq_zero_of_ne_zero_on_sphere hR hF hne hw

/-! ### The factorization on a closed disc -/

/-- The inductive core of `exists_zeroFactor`, over the number of distinct zeros. -/
theorem exists_zeroFactor_aux {U : Set ℂ} {c : ℂ} {R : ℝ}
    (hsub : closedBall c R ⊆ U) :
    ∀ (n : ℕ) (f : ℂ → ℂ), AnalyticOnNhd ℂ f U →
      (∀ u ∈ closedBall c R, ¬ (∀ᶠ z in 𝓝 u, f z = 0)) →
      (∀ z ∈ sphere c R, f z ≠ 0) →
      ∀ hfin : {z ∈ closedBall c R | f z = 0}.Finite, hfin.toFinset.card ≤ n →
      ∃ (s : Multiset ℂ) (g : ℂ → ℂ), (∀ u ∈ s, u ∈ ball c R) ∧ AnalyticOnNhd ℂ g U ∧
        (∀ z ∈ closedBall c R, g z ≠ 0) ∧ ∀ z, f z = zeroFactor s z * g z := by
  intro n
  induction n with
  | zero =>
    intro f hf _ _ hfin hcard
    refine ⟨0, f, by simp, hf, fun z hz hz0 => ?_, by simp⟩
    have hmem : z ∈ hfin.toFinset := hfin.mem_toFinset.mpr ⟨hz, hz0⟩
    rw [Finset.card_eq_zero.mp (Nat.le_zero.mp hcard)] at hmem
    exact absurd hmem (Finset.notMem_empty z)
  | succ n ih =>
    intro f hf hnd hns hfin hcard
    by_cases hzero : ∀ z ∈ closedBall c R, f z ≠ 0
    · exact ⟨0, f, by simp, hf, hzero, by simp⟩
    push Not at hzero
    obtain ⟨u, hu, hu0⟩ := hzero
    have huball : u ∈ ball c R := mem_ball_of_eq_zero hns hu hu0
    obtain ⟨m, g, hg, hgu, hfac⟩ := exists_pow_factor hf (hsub hu) (hnd u hu)
    have hgz : ∀ z, g z = 0 → f z = 0 := fun z h => by rw [hfac z, h, mul_zero]
    have hgfin : {z ∈ closedBall c R | g z = 0}.Finite :=
      hfin.subset fun z hz => ⟨hz.1, hgz z hz.2⟩
    have humem : u ∈ hfin.toFinset := hfin.mem_toFinset.mpr ⟨hu, hu0⟩
    have hsubf : hgfin.toFinset ⊆ hfin.toFinset.erase u := by
      intro z hz
      rw [hgfin.mem_toFinset] at hz
      refine Finset.mem_erase.mpr ⟨?_, hfin.mem_toFinset.mpr ⟨hz.1, hgz z hz.2⟩⟩
      rintro rfl
      exact hgu hz.2
    have hgcard : hgfin.toFinset.card ≤ n := by
      have h1 := Finset.card_le_card hsubf
      rw [Finset.card_erase_of_mem humem] at h1
      have h2 : 0 < hfin.toFinset.card := Finset.card_pos.mpr ⟨u, humem⟩
      omega
    have hndg : ∀ v ∈ closedBall c R, ¬ (∀ᶠ z in 𝓝 v, g z = 0) := fun v hv hcon =>
      hnd v hv (hcon.mono fun z hz => hgz z hz)
    have hnsg : ∀ z ∈ sphere c R, g z ≠ 0 := fun z hz h => hns z hz (hgz z h)
    obtain ⟨s, g', hsmem, hg', hg'ne, hfac'⟩ := ih g hg hndg hnsg hgfin hgcard
    refine ⟨Multiset.replicate m u + s, g', fun v hv => ?_, hg', hg'ne, fun z => ?_⟩
    · rcases Multiset.mem_add.mp hv with h | h
      · rw [Multiset.eq_of_mem_replicate h]; exact huball
      · exact hsmem v h
    · rw [hfac z, hfac' z, zeroFactor_add, zeroFactor_replicate, mul_assoc]

/-- **The factorization on a closed disc.**  An analytic function with no zero on the circle is
`∏_{u ∈ s} (z - u)` times an analytic function with no zero on the closed disc, where `s` is a
finite multiset of points of the open disc.  The identity holds at every point of `ℂ`. -/
theorem exists_zeroFactor {f : ℂ → ℂ} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (closedBall c R)) (hns : ∀ z ∈ sphere c R, f z ≠ 0) :
    ∃ (s : Multiset ℂ) (g : ℂ → ℂ), (∀ u ∈ s, u ∈ ball c R) ∧
      AnalyticOnNhd ℂ g (closedBall c R) ∧ (∀ z ∈ closedBall c R, g z ≠ 0) ∧
      ∀ z, f z = zeroFactor s z * g z := by
  set U : Set ℂ := {z | AnalyticAt ℂ f z} with hUdef
  have hsub : closedBall c R ⊆ U := hf
  have hfU : AnalyticOnNhd ℂ f U := fun z hz => hz
  -- `f` vanishes identically near no point of the closed disc, so its zeros there are isolated
  -- and finitely many.
  have hnd : ∀ u ∈ closedBall c R, ¬ (∀ᶠ z in 𝓝 u, f z = 0) := fun u hu =>
    not_eventually_eq_zero_of_ne_zero_on_sphere hR hf hns hu
  have hfin : {z ∈ closedBall c R | f z = 0}.Finite := finite_zeros_of_analyticOnNhd hf hnd
  obtain ⟨s, g, hsmem, hg, hgne, hfac⟩ :=
    exists_zeroFactor_aux hsub _ f hfU hnd hns hfin le_rfl
  exact ⟨s, g, hsmem, hg.mono hsub, hgne, hfac⟩

/-! ### The zero count -/

/-- The number of zeros of `f` in the open disc `ball c R`, counted with multiplicity.  The
multiplicity at a point is `analyticOrderNatAt`, Mathlib's vanishing order of an analytic
function. -/
noncomputable def zeroCount (f : ℂ → ℂ) (c : ℂ) (R : ℝ) : ℕ :=
  ∑ᶠ u ∈ ball c R, analyticOrderNatAt f u

/-- The count read off a factorization: it is the cardinality of the multiset of factors. -/
theorem zeroCount_eq_card {f g : ℂ → ℂ} {c : ℂ} {R : ℝ} {s : Multiset ℂ}
    (hsmem : ∀ u ∈ s, u ∈ ball c R) (hg : AnalyticOnNhd ℂ g (closedBall c R))
    (hgne : ∀ z ∈ closedBall c R, g z ≠ 0) (hfac : ∀ z, f z = zeroFactor s z * g z) :
    zeroCount f c R = Multiset.card s := by
  have hfeq : f = fun z => zeroFactor s z * g z := funext hfac
  have hstep : ∀ u ∈ ball c R, analyticOrderNatAt f u = s.count u := by
    intro u hu
    have huc : u ∈ closedBall c R := ball_subset_closedBall hu
    set k := s.count u with hk
    set t := s - Multiset.replicate k u with ht
    have hle : Multiset.replicate k u ≤ s := Multiset.le_count_iff_replicate_le.mp le_rfl
    have hst : Multiset.replicate k u + t = s := by
      rw [ht, add_comm]; exact Multiset.sub_add_cancel hle
    have hut : u ∉ t := by
      rw [← Multiset.count_eq_zero, ht, Multiset.count_sub, Multiset.count_replicate_self, ← hk]
      omega
    have hfu : ∀ z, f z = (z - u) ^ k * (zeroFactor t z * g z) := by
      intro z
      rw [hfac z, ← hst, zeroFactor_add, zeroFactor_replicate, mul_assoc]
    have hanal : AnalyticAt ℂ (fun z => zeroFactor t z * g z) u :=
      (analyticAt_zeroFactor t u).mul (hg u huc)
    have hne : zeroFactor t u * g u ≠ 0 :=
      mul_ne_zero (zeroFactor_ne_zero fun v hv h => hut (by rw [h]; exact hv)) (hgne u huc)
    have hfan : AnalyticAt ℂ f u := by
      rw [hfeq]; exact (analyticAt_zeroFactor s u).mul (hg u huc)
    have horder : analyticOrderAt f u = (k : ℕ∞) :=
      hfan.analyticOrderAt_eq_natCast.mpr ⟨_, hanal, hne,
        Filter.Eventually.of_forall fun z => by simpa [smul_eq_mul] using hfu z⟩
    simp [analyticOrderNatAt, horder]
  have hsupp : ball c R ∩ Function.support (fun u => s.count u) ⊆ (s.toFinset : Set ℂ) := by
    intro u hu
    have h : s.count u ≠ 0 := hu.2
    simpa using Multiset.count_pos.mp (Nat.pos_of_ne_zero h)
  have hts : (s.toFinset : Set ℂ) ⊆ ball c R := fun u hu =>
    hsmem u (Multiset.mem_toFinset.mp (by simpa using hu))
  calc zeroCount f c R = ∑ᶠ u ∈ ball c R, s.count u := finsum_mem_congr rfl hstep
    _ = ∑ u ∈ s.toFinset, s.count u := finsum_mem_eq_sum_of_subset _ hsupp hts
    _ = Multiset.card s := Multiset.toFinset_sum_count_eq s

/-! ### The argument principle -/

/-- **The zero-free factor contributes nothing.**  If `g` is analytic and
nowhere zero on the closed disk, `∮ g'/g = 0`.

`g'/g` is then analytic on the disk — this is where `g` must be *analytic* rather
than merely differentiable, so that `deriv g` is differentiable too — and Cauchy's
theorem applies. -/
theorem circleIntegral_logDeriv_eq_zero {c : ℂ} {R : ℝ} (hR : 0 ≤ R) (g : ℂ → ℂ)
    (hg : AnalyticOnNhd ℂ g (Metric.closedBall c R))
    (hgne : ∀ z ∈ Metric.closedBall c R, g z ≠ 0) :
    (∮ z in C(c, R), deriv g z / g z) = 0 := by
  have hlog : AnalyticOnNhd ℂ (fun z => deriv g z / g z) (Metric.closedBall c R) :=
    fun z hz => (hg.deriv z hz).div (hg z hz) (hgne z hz)
  refine circleIntegral_eq_zero_of_differentiable_on_off_countable hR
    Set.countable_empty hlog.continuousOn ?_
  intro z hz
  exact (hlog z (Metric.ball_subset_closedBall hz.1)).differentiableAt


/-- **The argument principle for analytic functions.**  For `f` analytic on a neighborhood of
`closedBall c R` with no zero on the circle `|z - c| = R`,
\[
  \oint_{|z-c|=R}\frac{f'}{f} = 2\pi i \cdot \#\{\text{zeros of } f \text{ in } |z-c|<R\},
\]
the count taken with multiplicity, multiplicity being `analyticOrderNatAt`. -/
theorem circleIntegral_logDeriv {f : ℂ → ℂ} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (closedBall c R)) (hns : ∀ z ∈ sphere c R, f z ≠ 0) :
    (∮ z in C(c, R), deriv f z / f z) = ((zeroCount f c R : ℕ) : ℂ) * (2 * Real.pi * I) := by
  obtain ⟨s, g, hsmem, hg, hgne, hfac⟩ := exists_zeroFactor hR hf hns
  have hfeq : f = fun z => zeroFactor s z * g z := funext hfac
  have hnotsph : ∀ r ∈ s, r ∉ sphere c R := by
    intro r hr hmem
    have h1 : dist r c < R := mem_ball.mp (hsmem r hr)
    exact absurd (mem_sphere.mp hmem) (ne_of_lt h1)
  have hsphne : ∀ z ∈ sphere c R, ∀ u ∈ s, z ≠ u := by
    intro z hz u hu hzu
    exact hnotsph u hu (hzu ▸ hz)
  -- Split the logarithmic derivative along the factorization.
  have hcong : Set.EqOn (fun z => deriv f z / f z)
      (fun z => (s.map fun u => (z - u)⁻¹).sum + deriv g z / g z) (sphere c R) := by
    intro z hz
    have hzc : z ∈ closedBall c R := sphere_subset_closedBall hz
    have hdg : DifferentiableAt ℂ g z := (hg z hzc).differentiableAt
    have hsplit := logDeriv_mul (f := zeroFactor s) (g := g) z
      (zeroFactor_ne_zero (hsphne z hz)) (hgne z hzc) ((differentiable_zeroFactor s) z) hdg
    rw [logDeriv_zeroFactor (hsphne z hz)] at hsplit
    change logDeriv f z = _
    rw [hfeq, hsplit, logDeriv_apply]
  rw [circleIntegral.integral_congr hR.le hcong]
  -- Both pieces are circle-integrable.
  have h1 : CircleIntegrable (fun z => (s.map fun u => (z - u)⁻¹).sum) c R :=
    circleIntegrable_multiset_sum_sub_inv s (by rwa [abs_of_pos hR])
  have hlog : AnalyticOnNhd ℂ (fun z => deriv g z / g z) (closedBall c R) :=
    fun z hz => (hg.deriv z hz).div (hg z hz) (hgne z hz)
  have h2 : CircleIntegrable (fun z => deriv g z / g z) c R :=
    (hlog.continuousOn.mono sphere_subset_closedBall).circleIntegrable hR.le
  -- The zero-free factor integrates to zero by Cauchy's theorem.
  rw [circleIntegral.integral_add h1 h2, circleIntegral_logDeriv_eq_zero hR.le g hg hgne,
    add_zero, circleIntegral_multiset_sum_sub_inv hR s hnotsph,
    zeroCount_eq_card hsmem hg hgne hfac]
  congr 2
  exact congrArg _ (Multiset.filter_eq_self.mpr fun r hr => mem_ball.mp (hsmem r hr))

/-! ### Rouché -/

/-- **Rouché's theorem for analytic functions.**  If `f` and `g` are analytic on a neighborhood of
`closedBall c R` and `‖g‖ < ‖f‖` on the circle `|z - c| = R`, then `f` and `f + g` have the same
number of zeros in the open disc, counted with multiplicity. -/
theorem zeroCount_add_eq {f g : ℂ → ℂ} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (closedBall c R)) (hg : AnalyticOnNhd ℂ g (closedBall c R))
    (hlt : ∀ z ∈ sphere c R, ‖g z‖ < ‖f z‖) :
    zeroCount (f + g) c R = zeroCount f c R := by
  have habs : |R| = R := abs_of_pos hR
  -- Every member of the deformation `f + t·g` is analytic and zero-free on the circle.
  have hFa : ∀ t : ℝ,
      AnalyticOnNhd ℂ (fun z => f z + ((clamp01 t : ℝ) : ℂ) * g z) (closedBall c R) :=
    fun t z hz => (hf z hz).add (analyticAt_const.mul (hg z hz))
  have hFne : ∀ (t : ℝ), ∀ z ∈ sphere c R, f z + ((clamp01 t : ℝ) : ℂ) * g z ≠ 0 := fun t z hz =>
    add_smul_ne_zero_of_norm_lt f g (by rwa [habs]) (clamp01_mem t) (by rwa [habs])
  have hderiv : ∀ (t : ℝ), ∀ z ∈ closedBall c R,
      deriv (fun w => f w + ((clamp01 t : ℝ) : ℂ) * g w) z
        = deriv f z + ((clamp01 t : ℝ) : ℂ) * deriv g z := by
    intro t z hz
    have h2 : DifferentiableAt ℂ g z := (hg z hz).differentiableAt
    rw [deriv_fun_add (hf z hz).differentiableAt (h2.const_mul _), deriv_const_mul _ h2]
  -- So the argument principle reads its count off the contour integral.
  set N : ℝ → ℤ :=
    fun t => ((zeroCount (fun z => f z + ((clamp01 t : ℝ) : ℂ) * g z) c R : ℕ) : ℤ) with hNdef
  have hcount : ∀ t : ℝ,
      (∮ z in C(c, R), (deriv f z + ((clamp01 t : ℝ) : ℂ) * deriv g z)
          / (f z + ((clamp01 t : ℝ) : ℂ) * g z)) = (N t : ℂ) * (2 * Real.pi * I) := by
    intro t
    have heq : (∮ z in C(c, R), (deriv f z + ((clamp01 t : ℝ) : ℂ) * deriv g z)
          / (f z + ((clamp01 t : ℝ) : ℂ) * g z))
        = ∮ z in C(c, R), deriv (fun w => f w + ((clamp01 t : ℝ) : ℂ) * g w) z
            / (f z + ((clamp01 t : ℝ) : ℂ) * g z) :=
      circleIntegral.integral_congr hR.le fun z hz => by
        rw [hderiv t z (sphere_subset_closedBall hz)]
    rw [heq, circleIntegral_logDeriv hR (hFa t) (hFne t), hNdef]
    norm_cast
  -- And a continuous integer count cannot jump.
  have hfin := int_eq_of_circleIntegral_deform hR.le
    (hf.continuousOn.mono sphere_subset_closedBall)
    (hg.continuousOn.mono sphere_subset_closedBall)
    (hf.deriv.continuousOn.mono sphere_subset_closedBall)
    (hg.deriv.continuousOn.mono sphere_subset_closedBall) hlt hcount
  rw [hNdef] at hfin
  simp only [clamp01_zero, clamp01_one, Complex.ofReal_zero, Complex.ofReal_one, zero_mul,
    one_mul, add_zero] at hfin
  exact_mod_cast hfin.symm

/-! ### Hurwitz -/

/-- **Hurwitz's theorem for analytic functions.**  If `f n → f₀` uniformly on a circle carrying no
zero of `f₀`, all analytic on a neighborhood of the closed disc, then eventually `f n` has exactly
`f₀`'s number of zeros inside, counted with multiplicity. -/
theorem eventually_zeroCount_eq {c : ℂ} {R : ℝ} (hR : 0 < R) {f : ℕ → ℂ → ℂ} {f₀ : ℂ → ℂ}
    (hf : ∀ n, AnalyticOnNhd ℂ (f n) (closedBall c R))
    (hf₀ : AnalyticOnNhd ℂ f₀ (closedBall c R))
    (hunif : TendstoUniformlyOn f f₀ Filter.atTop (sphere c R))
    (hns : ∀ z ∈ sphere c R, f₀ z ≠ 0) :
    ∀ᶠ n in Filter.atTop, zeroCount (f n) c R = zeroCount f₀ c R := by
  filter_upwards [eventually_norm_sub_lt_of_tendstoUniformlyOn (isCompact_sphere c R)
    (hf₀.continuousOn.mono sphere_subset_closedBall) hns hunif] with n hn
  have hlt : ∀ z ∈ sphere c R, ‖(f n - f₀) z‖ < ‖f₀ z‖ := fun z hz => by
    simpa using hn z hz
  have h := zeroCount_add_eq hR hf₀ ((hf n).sub hf₀) hlt
  have hsum : f₀ + (f n - f₀) = f n := by funext z; simp
  rwa [hsum] at h

/-- The simple-zero form of Hurwitz: if `f₀` has exactly one zero in the disc, so does `f n` for
all large `n`. -/
theorem eventually_zeroCount_eq_one {c : ℂ} {R : ℝ} (hR : 0 < R) {f : ℕ → ℂ → ℂ} {f₀ : ℂ → ℂ}
    (hf : ∀ n, AnalyticOnNhd ℂ (f n) (closedBall c R))
    (hf₀ : AnalyticOnNhd ℂ f₀ (closedBall c R))
    (hunif : TendstoUniformlyOn f f₀ Filter.atTop (sphere c R))
    (hns : ∀ z ∈ sphere c R, f₀ z ≠ 0) (hone : zeroCount f₀ c R = 1) :
    ∀ᶠ n in Filter.atTop, zeroCount (f n) c R = 1 := by
  filter_upwards [eventually_zeroCount_eq hR hf hf₀ hunif hns] with n hn
  rw [hn, hone]

/-! ### The one-zero perturbation form -/

/-- **A single zero survives a small perturbation.**  If `‖h‖ < ‖f‖` on the circle and `f` has
exactly one zero in the open disc, then so does `f + h`. -/
theorem zeroCount_add_eq_one {f h : ℂ → ℂ} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (closedBall c R)) (hh : AnalyticOnNhd ℂ h (closedBall c R))
    (hlt : ∀ z ∈ sphere c R, ‖h z‖ < ‖f z‖) (hone : zeroCount f c R = 1) :
    zeroCount (f + h) c R = 1 := by
  rw [zeroCount_add_eq hR hf hh hlt, hone]

/-- A nonzero count exhibits a zero. -/
theorem exists_zero_of_zeroCount_ne_zero {f : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hc : zeroCount f c R ≠ 0) : ∃ z ∈ ball c R, f z = 0 := by
  by_contra hcon
  push Not at hcon
  refine hc ?_
  rw [zeroCount]
  refine (finsum_mem_congr rfl fun u hu => ?_).trans (finsum_mem_zero _)
  have h0 : analyticOrderAt f u = 0 := analyticOrderAt_eq_zero.mpr (Or.inr (hcon u hu))
  simp [analyticOrderNatAt, h0]

/-- Under the hypotheses of the argument principle, a zero count of zero means no zero. -/
theorem zeroCount_eq_zero_iff {f : ℂ → ℂ} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (closedBall c R)) (hns : ∀ z ∈ sphere c R, f z ≠ 0) :
    zeroCount f c R = 0 ↔ ∀ z ∈ ball c R, f z ≠ 0 := by
  obtain ⟨s, g, hsmem, hg, hgne, hfac⟩ := exists_zeroFactor hR hf hns
  rw [zeroCount_eq_card hsmem hg hgne hfac, Multiset.card_eq_zero]
  constructor
  · rintro rfl z hz
    rw [hfac z, zeroFactor_zero, one_mul]
    exact hgne z (ball_subset_closedBall hz)
  · intro hz
    by_contra hs
    obtain ⟨u, hu⟩ := Multiset.exists_mem_of_ne_zero hs
    exact hz u (hsmem u hu) (by rw [hfac u, zeroFactor_eq_zero hu, zero_mul])


/-! ### Axiom footprint -/

/-- info: 'Shields.eventually_zeroCount_eq_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms eventually_zeroCount_eq_one

/-- info: 'Shields.zeroCount_add_eq_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms zeroCount_add_eq_one

/-- info: 'Shields.logDeriv_prod_sub_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms logDeriv_prod_sub_mul

/-- info: 'Shields.finite_zeros_of_ne_zero_on_sphere' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms finite_zeros_of_ne_zero_on_sphere

end Shields
