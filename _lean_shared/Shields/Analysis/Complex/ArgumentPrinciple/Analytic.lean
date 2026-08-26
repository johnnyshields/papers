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
* `Shields.analyticAt_dslope`, `Shields.analyticOnNhd_iterate_dslope`: dividing a zero out without
  leaving the analytic class.  Neither asks for `U` open, which is what lets the closed-disc
  factorization in `Shields.Analysis.Complex.Rouche` consume them on a `closedBall`.

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

/-! ### The factorization on a closed disc -/

/-- The inductive core of `exists_zeroFactor`, over the number of distinct zeros. -/
theorem exists_zeroFactor_aux {U : Set ℂ} (hU : IsOpen U) {c : ℂ} {R : ℝ}
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
    have huball : u ∈ ball c R := by
      rcases lt_or_eq_of_le (mem_closedBall.mp hu) with h | h
      · exact mem_ball.mpr h
      · exact absurd hu0 (hns u (mem_sphere.mpr h))
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
  have hU : IsOpen U := isOpen_analyticAt ℂ f
  have hsub : closedBall c R ⊆ U := hf
  have hfU : AnalyticOnNhd ℂ f U := fun z hz => hz
  have hsphne : (c + (R : ℂ)) ∈ sphere c R := by
    rw [mem_sphere, dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hR]
  -- `f` vanishes identically near no point of the closed disc.
  have hnd : ∀ u ∈ closedBall c R, ¬ (∀ᶠ z in 𝓝 u, f z = 0) := by
    intro u hu hcon
    rcases lt_or_eq_of_le (mem_closedBall.mp hu) with h | h
    · have hball : AnalyticOnNhd ℂ f (ball c R) := hf.mono ball_subset_closedBall
      have hzero : Set.EqOn f 0 (ball c R) :=
        hball.eqOn_zero_of_preconnected_of_eventuallyEq_zero (convex_ball c R).isPreconnected
          (mem_ball.mpr h) hcon
      have hcl : Set.EqOn f 0 (closedBall c R) :=
        hzero.of_subset_closure hf.continuousOn continuousOn_const ball_subset_closedBall
          (closure_ball c hR.ne').symm.subset
      exact hns _ hsphne (by simpa using hcl (sphere_subset_closedBall hsphne))
    · exact hns u (mem_sphere.mpr h) hcon.self_of_nhds
  -- The zeros in the closed disc are finitely many.
  have hfin : {z ∈ closedBall c R | f z = 0}.Finite := by
    have hnbhd : ∀ x ∈ closedBall c R, {z | z ≠ x → f z ≠ 0} ∈ 𝓝 x := by
      intro x hx
      have := ((hf x hx).eventually_eq_zero_or_eventually_ne_zero).resolve_left (hnd x hx)
      rw [eventually_nhdsWithin_iff] at this
      exact this
    obtain ⟨t, _, htc⟩ := (isCompact_closedBall c R).elim_nhds_subcover _ hnbhd
    refine Set.Finite.subset t.finite_toSet fun z hz => ?_
    obtain ⟨x, hx, hzx⟩ := by simpa using htc hz.1
    by_contra hzt
    exact hzx (fun h => hzt (h ▸ hx)) hz.2
  obtain ⟨s, g, hsmem, hg, hgne, hfac⟩ :=
    exists_zeroFactor_aux hU hsub _ f hfU hnd hns hfin le_rfl
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

/-- **The argument principle for analytic functions.**  For `f` analytic on a neighborhood of
`closedBall c R` with no zero on the circle `|z - c| = R`,
\[
  \oint_{|z-c|=R}\frac{f'}{f} = 2\pi i \cdot \#\{\text{zeros of } f \text{ in } |z-c|<R\},
\]
the count taken with multiplicity, multiplicity being `analyticOrderNatAt`. -/
theorem circleIntegral_logDeriv {f : ℂ → ℂ} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (closedBall c R)) (hns : ∀ z ∈ sphere c R, f z ≠ 0) :
    (∮ z in C(c, R), deriv f z / f z) = ((zeroCount f c R : ℕ) : ℂ) * (2 * Real.pi * I) := by
  have habs : |R| = R := abs_of_pos hR
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
    circleIntegrable_multiset_sum_sub_inv s (by rwa [habs])
  have h2 : CircleIntegrable (fun z => deriv g z / g z) c R := by
    refine ContinuousOn.circleIntegrable hR.le ?_
    refine ContinuousOn.div ?_ ?_ ?_
    · exact (hg.deriv.continuousOn).mono sphere_subset_closedBall
    · exact hg.continuousOn.mono sphere_subset_closedBall
    · exact fun z hz => hgne z (sphere_subset_closedBall hz)
  rw [circleIntegral.integral_add h1 h2]
  -- The zero-free factor integrates to zero by Cauchy's theorem.
  have hcauchy : (∮ z in C(c, R), deriv g z / g z) = 0 := by
    refine Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable hR.le
      Set.countable_empty ?_ ?_
    · refine ContinuousOn.div (hg.deriv.continuousOn) hg.continuousOn fun z hz => hgne z hz
    · intro z hz
      have hzc : z ∈ closedBall c R := ball_subset_closedBall hz.1
      exact ((hg.deriv z hzc).differentiableAt).div ((hg z hzc).differentiableAt) (hgne z hzc)
  rw [hcauchy, add_zero, circleIntegral_multiset_sum_sub_inv hR s hnotsph,
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
  set a : ℝ → ℂ := fun t => ((clamp01 t : ℝ) : ℂ) with hadef
  set F : ℝ → ℂ → ℂ := fun t z => f z + a t * g z with hFdef
  -- (a) The family stays analytic and zero-free on the circle.
  have hFa : ∀ t : ℝ, AnalyticOnNhd ℂ (F t) (closedBall c R) := fun t z hz =>
    (hf z hz).add (analyticAt_const.mul (hg z hz))
  have hFne : ∀ (t : ℝ), ∀ z ∈ sphere c R, F t z ≠ 0 := fun t z hz =>
    add_smul_ne_zero_of_norm_lt f g (by rwa [habs]) (clamp01_mem t) (by rwa [habs])
  set N : ℝ → ℤ := fun t => ((zeroCount (F t) c R : ℕ) : ℤ) with hNdef
  have hcount : ∀ t : ℝ,
      (∮ z in C(c, R), deriv (F t) z / F t z) = (N t : ℂ) * (2 * Real.pi * I) := by
    intro t
    rw [circleIntegral_logDeriv hR (hFa t) (hFne t), hNdef]
    norm_cast
  -- (b) The integral moves continuously in `t`.
  have hderiv : ∀ (t : ℝ), ∀ z ∈ closedBall c R,
      deriv (F t) z = deriv f z + a t * deriv g z := by
    intro t z hz
    have h1 : DifferentiableAt ℂ f z := (hf z hz).differentiableAt
    have h2 : DifferentiableAt ℂ g z := (hg z hz).differentiableAt
    have hFt : F t = f + fun w => a t * g w := rfl
    rw [hFt, deriv_add h1 (h2.const_mul (a t)), deriv_const_mul (a t) h2]
  have hcm : Continuous fun p : ℝ × ℝ => circleMap c R p.2 :=
    (continuous_circleMap c R).comp continuous_snd
  have hmaps : ∀ p : ℝ × ℝ, circleMap c R p.2 ∈ closedBall c R := fun p =>
    sphere_subset_closedBall (circleMap_mem_sphere c hR.le p.2)
  have hcl : Continuous fun p : ℝ × ℝ => a p.1 :=
    Complex.continuous_ofReal.comp (continuous_clamp01.comp continuous_fst)
  have hcf : Continuous fun p : ℝ × ℝ => f (circleMap c R p.2) :=
    hf.continuousOn.comp_continuous hcm hmaps
  have hcg : Continuous fun p : ℝ × ℝ => g (circleMap c R p.2) :=
    hg.continuousOn.comp_continuous hcm hmaps
  have hcdf : Continuous fun p : ℝ × ℝ => deriv f (circleMap c R p.2) :=
    hf.deriv.continuousOn.comp_continuous hcm hmaps
  have hcdg : Continuous fun p : ℝ × ℝ => deriv g (circleMap c R p.2) :=
    hg.deriv.continuousOn.comp_continuous hcm hmaps
  set Φ : ℝ → ℂ → ℂ := fun t z => (deriv f z + a t * deriv g z) / (f z + a t * g z) with hΦdef
  have hjoint : Continuous fun p : ℝ × ℝ => Φ p.1 (circleMap c R p.2) := by
    rw [hΦdef]
    refine Continuous.div (hcdf.add (hcl.mul hcdg)) (hcf.add (hcl.mul hcg)) fun p => ?_
    exact hFne p.1 _ (circleMap_mem_sphere c hR.le p.2)
  have hΦeq : ∀ t : ℝ, (∮ z in C(c, R), Φ t z) = (N t : ℂ) * (2 * Real.pi * I) := by
    intro t
    rw [← hcount t]
    refine circleIntegral.integral_congr hR.le fun z hz => ?_
    rw [hΦdef, hderiv t z (sphere_subset_closedBall hz)]
  have hI : Continuous fun t : ℝ => ∮ z in C(c, R), Φ t z :=
    continuous_circleIntegral_param _ hjoint
  -- (c) A continuous integer count cannot jump.
  have h2pi : (2 * (Real.pi : ℂ) * I) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have hstep : Continuous fun t : ℝ => ((N t : ℂ) * (2 * Real.pi * I)) := by
    simpa only [hΦeq] using hI
  have hcast : Continuous fun t : ℝ => ((N t : ℂ)) := by
    simpa [mul_div_assoc, div_self h2pi] using hstep.div_const (2 * (Real.pi : ℂ) * I)
  have hreal : Continuous fun t : ℝ => ((N t : ℝ)) := by
    have h := Complex.continuous_re.comp hcast
    refine h.congr fun t => ?_
    simp [Function.comp]
  have hfin := int_eq_of_continuousOn_Icc N (continuous_int_of_continuous_cast hreal).continuousOn
  have hF0 : F 0 = f := by
    funext z; simp [hFdef, hadef]
  have hF1 : F 1 = f + g := by
    funext z; simp [hFdef, hadef]
  rw [hNdef] at hfin
  simp only [hF0, hF1] at hfin
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
  have habs : |R| = R := abs_of_pos hR
  have hsphne : (c + (R : ℂ)) ∈ sphere c R := by
    rw [mem_sphere, dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs, habs]
  obtain ⟨z₀, hz₀, hmin⟩ := (isCompact_sphere c R).exists_isMinOn ⟨_, hsphne⟩
    ((hf₀.continuousOn.mono sphere_subset_closedBall).norm)
  have hεpos : 0 < ‖f₀ z₀‖ := norm_pos_iff.mpr (hns z₀ hz₀)
  have hbound : ∀ z ∈ sphere c R, ‖f₀ z₀‖ ≤ ‖f₀ z‖ := fun z hz => isMinOn_iff.mp hmin z hz
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hunif _ hεpos] with n hn
  have hlt : ∀ z ∈ sphere c R, ‖(f n - f₀) z‖ < ‖f₀ z‖ := by
    intro z hz
    calc ‖(f n - f₀) z‖ = dist (f₀ z) (f n z) := by
          rw [Pi.sub_apply, dist_eq_norm, norm_sub_rev]
      _ < ‖f₀ z₀‖ := hn z hz
      _ ≤ ‖f₀ z‖ := hbound z hz
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

end Shields
