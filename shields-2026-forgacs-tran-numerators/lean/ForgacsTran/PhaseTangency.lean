/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import ForgacsTran.PhaseVariationBlocks
import ForgacsTran.PhaseStateDichotomy
import ForgacsTran.BranchCurvature
import ForgacsTran.ComplexPart

/-!
# The crossing set is finite once the arc has nonvanishing curvature

`PhaseVariationBlocks.sum_eVariationOn_branch_le` asks for a `Finset` containing
every parameter where the tangent angle and the viewing angle differ by an integer
multiple of `π`.  `PhaseStateDichotomy` supplies the two states the arc can be in
and the compactness argument that turns isolated zeros into finitely many; what is
missing there is the isolation itself, and this module is that.

**One real equation, not a family indexed by `j`.**  The two continuous angles are
`arg γ'` and `arg (γ - β)`, so their difference is an integer multiple of `π`
exactly where `γ'` and `γ - β` are real-parallel — where the line from `β` is
tangent to the arc.  That is the single real condition `wedge (γ' s) (γ s - β) = 0`,
and `tangency_eq_zero_of_polarAngle_sub` discharges the `∀ j : ℤ` once rather than
per `j`.  Verified independently in `scripts/check_crossing_set_tangency.py`, with
the lifted angle built by integration so that the base constants `Complex.log`
contributes are tested rather than assumed to cancel.

**Two shapes of zero, and only one of them is simple.**  Off the point where the arc
meets `β` the tangency function has a nonvanishing derivative, so its zeros are
simple.  **At a meeting point it has a double zero** — both `γ - β` and the
derivative `wedge (γ'' ·) (γ - β)` vanish there — so no simple-zero argument
reaches it.  What does reach it is two applications of the mean value theorem:
`tangency x = (x - m)(x - ξ)·wedge (γ'' η) (γ' ξ)` with `ξ`, `η` between, the first
two factors of one sign and the third near `wedge (γ'' m) (γ' m)`.  So the same
curvature hypothesis serves both, and no analyticity is used anywhere.

**Curvature is the whole of what is assumed.**  `wedge (γ'' s) (γ' s) ≠ 0` is the
signed curvature numerator; at the pencil's branch `im_wedge_ftGammaDeriv` computes
it as `τ² + 2τ'² - ττ''`, the classical polar form.  A branch running straight
through `β` makes the tangency function vanish identically and no finite set exists,
which is exactly the case this hypothesis excludes.

## Main statements

* `wedge` — `Im(u \overline{w})`, in real coordinates so that every step below is
  polynomial identities in four reals.
* `hasDerivAt_tangency` — the derivative of `tangency γ dγ β` is `tangency γ d2γ β`.
* `wedge_ne_zero_of_wedge_eq_zero` — the simple-zero step: a zero off the meeting
  point has nonvanishing derivative.
* `tangency_ne_zero_nhdsNE_of_meet` — the double-zero step, by two mean values.
* `finite_of_isolated_zeros` — isolated zeros on a compact set are finite.
* `finite_tangency_zeros` — the two steps combined.
* `tangency_eq_zero_of_polarAngle_sub` — the crossing condition is the tangency
  condition.
* `sum_eVariationOn_of_curvature` — `sum_eVariationOn_branch_le` with `hstate`
  discharged: the branch family is chosen, not assumed.
* `im_wedge_ftGammaDeriv` — the curvature hypothesis at the pencil's branch.

## References

* `../shields-2026-forgacs-tran-numerators.tex`, `lem:viewing-angle`,
  `cor:linear-phase-variation`, `lem:principal-endpoint-regularity`.
* `../scripts/check_crossing_set_tangency.py`, `../scripts/check_branch_convexity.py`.

## Tags

viewing angle, tangency, curvature, crossing set, phase variation, block state
-/

namespace ForgacsTran

open Set Filter Real
open scoped Topology

/-! ### The wedge of two complex numbers -/

/-- `Im(u · conj w)`, the signed area of the parallelogram on `u` and `w`.

Written in real coordinates rather than as `(u * (starRingEnd ℂ) w).im` because every
statement below is a polynomial identity in the four coordinates, and `linear_combination`
closes those directly. -/
noncomputable def wedge (u w : ℂ) : ℝ := u.im * w.re - u.re * w.im

theorem wedge_eq_im_mul_conj (u w : ℂ) : wedge u w = (u * (starRingEnd ℂ) w).im := by
  simp only [wedge, Complex.mul_im, Complex.conj_re, Complex.conj_im]
  ring

theorem wedge_self (u : ℂ) : wedge u u = 0 := by
  simp only [wedge]; ring

private theorem coord_sq_ne_zero {z : ℂ} (hz : z ≠ 0) : z.re ^ 2 + z.im ^ 2 ≠ 0 := by
  intro h0
  refine hz (Complex.normSq_eq_zero.1 ?_)
  rw [Complex.normSq_apply]
  linear_combination h0

/-- **A zero of the tangency function off the meeting point is simple.**  If `γ'` is
real-parallel to the chord `γ - β`, then `γ''` wedged against the chord is a nonzero
multiple of `γ''` wedged against `γ'` — the curvature.

The identity behind it is `‖u‖²·wedge D w = Re(u·conj w)·wedge D u` whenever
`wedge u w = 0`, which is one `linear_combination` in four real coordinates. -/
theorem wedge_ne_zero_of_wedge_eq_zero {u w D : ℂ} (hu : u ≠ 0) (hw : w ≠ 0)
    (h : wedge u w = 0) (hD : wedge D u ≠ 0) : wedge D w ≠ 0 := by
  have hnu := coord_sq_ne_zero hu
  simp only [wedge] at h ⊢
  -- `Re(u · conj w)` is nonzero: with the wedge zero, its vanishing forces `w = 0`
  have hc : u.re * w.re + u.im * w.im ≠ 0 := by
    intro h0
    refine hw (Complex.ext ?_ ?_)
    · have e1 : (u.re ^ 2 + u.im ^ 2) * w.re = 0 := by
        linear_combination u.re * h0 + u.im * h
      simpa [hnu] using (mul_eq_zero.1 e1).resolve_left hnu
    · have e2 : (u.re ^ 2 + u.im ^ 2) * w.im = 0 := by
        linear_combination u.im * h0 - u.re * h
      simpa [hnu] using (mul_eq_zero.1 e2).resolve_left hnu
  have hkey : (u.re ^ 2 + u.im ^ 2) * (D.im * w.re - D.re * w.im)
      = (u.re * w.re + u.im * w.im) * (D.im * u.re - D.re * u.im) := by
    linear_combination (D.re * u.re + D.im * u.im) * h
  intro h0
  rw [h0, mul_zero] at hkey
  exact (mul_ne_zero hc hD) hkey.symm

/-! ### The tangency function and its derivative -/

/-- The tangency function of an arc viewed from `β`: it vanishes exactly where the line
from `β` is tangent to the arc, which is where the viewing angle is critical. -/
noncomputable def tangency (γ dγ : ℝ → ℂ) (β : ℂ) (x : ℝ) : ℝ := wedge (dγ x) (γ x - β)

/-- The wedge is bilinear, so it differentiates by the product rule. -/
theorem hasDerivAt_wedge {F G : ℝ → ℂ} {F' G' : ℂ} {x : ℝ}
    (hF : HasDerivAt F F' x) (hG : HasDerivAt G G' x) :
    HasDerivAt (fun t => wedge (F t) (G t)) (wedge F' (G x) + wedge (F x) G') x := by
  have h1 := hF.im.mul hG.re
  have h2 := hF.re.mul hG.im
  refine (h1.sub h2).congr_deriv ?_
  simp only [wedge]
  ring

/-- **The derivative of the tangency function is the tangency function of the second
derivative.**  The `γ'` wedged against itself contributes nothing, which is why the
curvature — and not the speed — is what decides simplicity. -/
theorem hasDerivAt_tangency {γ dγ d2γ : ℝ → ℂ} {β : ℂ} {x : ℝ}
    (hγ : HasDerivAt γ (dγ x) x) (hd : HasDerivAt dγ (d2γ x) x) :
    HasDerivAt (tangency γ dγ β) (tangency γ d2γ β x) x := by
  refine (hasDerivAt_wedge hd (hγ.sub_const β)).congr_deriv ?_
  simp only [tangency, wedge]
  ring

theorem wedge_zero_left (w : ℂ) : wedge 0 w = 0 := by simp [wedge]

theorem wedge_zero_right (u : ℂ) : wedge u 0 = 0 := by simp [wedge]

/-! ### The double zero where the arc meets the vantage point

At a parameter `m` with `γ m = β` the chord vanishes, so `tangency` and its derivative
`tangency γ d2γ β` vanish together: the zero is **double**, and no simple-zero argument
reaches it.  Two mean values do.  Freezing the first slot of the wedge at `x` and running
the second from `m` to `x` gives `tangency x = (x - m)·wedge (γ' x) (γ' ξ)`; freezing the
second slot at `ξ` and running the first from `ξ` to `x` gives
`wedge (γ' x) (γ' ξ) = (x - ξ)·wedge (γ'' η) (γ' ξ)`.  Both `ξ` and `η` lie between `m` and
`x`, so the two linear factors carry the same sign and the curvature decides. -/

/-- **The tangency function factors at a meeting parameter.**  `ξ` and `η` lie in the same
convex neighborhood as `m` and `x`, and the product of the two linear factors is positive
whichever side of `m` the parameter `x` is on. -/
private theorem tangency_factor_of_meet {γ dγ d2γ : ℝ → ℂ} {β : ℂ} {W : Set ℝ}
    (hWconv : Convex ℝ W)
    (hd : ∀ s ∈ W, HasDerivAt γ (dγ s) s) (hd2 : ∀ s ∈ W, HasDerivAt dγ (d2γ s) s)
    {m x : ℝ} (hm : m ∈ W) (hx : x ∈ W) (hne : x ≠ m) (hmeet : γ m = β) :
    ∃ ξ ∈ W, ∃ η ∈ W, 0 < (x - m) * (x - ξ) ∧
      tangency γ dγ β x = (x - m) * (x - ξ) * wedge (d2γ η) (dγ ξ) := by
  classical
  have hoc := hWconv.ordConnected
  have huIcc : uIcc m x ⊆ W := hoc.uIcc_subset hm hx
  -- the chord slot, with the tangent frozen at `x`
  set f₁ : ℝ → ℝ := fun t => wedge (dγ x) (γ t - β) with hf₁def
  have hdf₁ : ∀ t ∈ W, HasDerivAt f₁ (wedge (dγ x) (dγ t)) t := by
    intro t ht
    refine (hasDerivAt_wedge (hasDerivAt_const t (dγ x)) ((hd t ht).sub_const β)).congr_deriv ?_
    rw [wedge_zero_left, zero_add]
  have hf₁m : f₁ m = 0 := by rw [hf₁def]; simp only [hmeet, sub_self, wedge_zero_right]
  have hf₁x : f₁ x = tangency γ dγ β x := rfl
  -- the tangent slot, with the other tangent frozen at a point `ξ`
  have hdf₂ : ∀ (ξ : ℝ), ∀ s ∈ W, HasDerivAt (fun t => wedge (dγ t) (dγ ξ))
      (wedge (d2γ s) (dγ ξ)) s := by
    intro ξ s hs
    refine (hasDerivAt_wedge (hd2 s hs) (hasDerivAt_const s (dγ ξ))).congr_deriv ?_
    rw [wedge_zero_right, add_zero]
  rcases hne.lt_or_gt with hlt | hgt
  · -- `x < m`
    have hsub : Icc x m ⊆ W := by
      rw [uIcc_of_ge hlt.le] at huIcc; exact huIcc
    obtain ⟨ξ, hξ, hslope⟩ := exists_hasDerivAt_eq_slope f₁ (fun t => wedge (dγ x) (dγ t)) hlt
      (fun t ht => (hdf₁ t (hsub ht)).continuousAt.continuousWithinAt)
      (fun t ht => hdf₁ t (hsub (Ioo_subset_Icc_self ht)))
    have hξW : ξ ∈ W := hsub (Ioo_subset_Icc_self hξ)
    have hsub2 : Icc x ξ ⊆ W := fun t ht => hsub ⟨ht.1, ht.2.trans hξ.2.le⟩
    obtain ⟨η, hη, hslope2⟩ := exists_hasDerivAt_eq_slope (fun t => wedge (dγ t) (dγ ξ))
      (fun s => wedge (d2γ s) (dγ ξ)) hξ.1
      (fun t ht => (hdf₂ ξ t (hsub2 ht)).continuousAt.continuousWithinAt)
      (fun t ht => hdf₂ ξ t (hsub2 (Ioo_subset_Icc_self ht)))
    refine ⟨ξ, hξW, η, hsub2 (Ioo_subset_Icc_self hη), by nlinarith [hξ.1, hξ.2, hlt], ?_⟩
    rw [hf₁m, hf₁x] at hslope
    rw [wedge_self] at hslope2
    have hmx : m - x ≠ 0 := sub_ne_zero.2 hlt.ne'
    have hξx : ξ - x ≠ 0 := sub_ne_zero.2 hξ.1.ne'
    rw [eq_div_iff hmx] at hslope
    rw [eq_div_iff hξx] at hslope2
    have h1 : tangency γ dγ β x = (x - m) * wedge (dγ x) (dγ ξ) := by
      linear_combination hslope
    have h2 : wedge (dγ x) (dγ ξ) = (x - ξ) * wedge (d2γ η) (dγ ξ) := by
      linear_combination hslope2
    rw [h1, h2]; ring
  · -- `m < x`
    have hsub : Icc m x ⊆ W := by
      rw [uIcc_of_le hgt.le] at huIcc; exact huIcc
    obtain ⟨ξ, hξ, hslope⟩ := exists_hasDerivAt_eq_slope f₁ (fun t => wedge (dγ x) (dγ t)) hgt
      (fun t ht => (hdf₁ t (hsub ht)).continuousAt.continuousWithinAt)
      (fun t ht => hdf₁ t (hsub (Ioo_subset_Icc_self ht)))
    have hξW : ξ ∈ W := hsub (Ioo_subset_Icc_self hξ)
    have hsub2 : Icc ξ x ⊆ W := fun t ht => hsub ⟨hξ.1.le.trans ht.1, ht.2⟩
    obtain ⟨η, hη, hslope2⟩ := exists_hasDerivAt_eq_slope (fun t => wedge (dγ t) (dγ ξ))
      (fun s => wedge (d2γ s) (dγ ξ)) hξ.2
      (fun t ht => (hdf₂ ξ t (hsub2 ht)).continuousAt.continuousWithinAt)
      (fun t ht => hdf₂ ξ t (hsub2 (Ioo_subset_Icc_self ht)))
    refine ⟨ξ, hξW, η, hsub2 (Ioo_subset_Icc_self hη), by nlinarith [hξ.1, hξ.2, hgt], ?_⟩
    rw [hf₁m, hf₁x] at hslope
    rw [wedge_self] at hslope2
    have hmx : x - m ≠ 0 := sub_ne_zero.2 hgt.ne'
    have hξx : x - ξ ≠ 0 := sub_ne_zero.2 hξ.2.ne'
    rw [eq_div_iff hmx] at hslope
    rw [eq_div_iff hξx] at hslope2
    have h1 : tangency γ dγ β x = (x - m) * wedge (dγ x) (dγ ξ) := by
      linear_combination -hslope
    have h2 : wedge (dγ x) (dγ ξ) = (x - ξ) * wedge (d2γ η) (dγ ξ) := by
      linear_combination -hslope2
    rw [h1, h2]; ring

/-- **A meeting parameter is isolated among the zeros of the tangency function.**  The
factorization of `tangency_factor_of_meet` with both auxiliary parameters held in a ball on
which the curvature does not vanish. -/
theorem tangency_ne_zero_nhdsNE_of_meet {γ dγ d2γ : ℝ → ℂ} {β : ℂ} {U : Set ℝ} {m : ℝ}
    (hU : IsOpen U) (hm : m ∈ U)
    (hd : ∀ s ∈ U, HasDerivAt γ (dγ s) s)
    (hd2 : ∀ s ∈ U, HasDerivAt dγ (d2γ s) s)
    (hc2 : ContinuousOn d2γ U) (hmeet : γ m = β)
    (hcurv : wedge (d2γ m) (dγ m) ≠ 0) :
    ∀ᶠ x in 𝓝[≠] m, tangency γ dγ β x ≠ 0 := by
  classical
  have hcd2 : ContinuousAt d2γ m := hc2.continuousAt (hU.mem_nhds hm)
  have hcd : ContinuousAt dγ m := (hd2 m hm).continuousAt
  have hK : ContinuousAt (fun p : ℝ × ℝ => wedge (d2γ p.1) (dγ p.2)) (m, m) := by
    have h1 : ContinuousAt (fun p : ℝ × ℝ => d2γ p.1) (m, m) := hcd2.comp continuousAt_fst
    have h2 : ContinuousAt (fun p : ℝ × ℝ => dγ p.2) (m, m) := hcd.comp continuousAt_snd
    simp only [wedge]
    exact ((Complex.continuous_im.continuousAt.comp h1).mul
        (Complex.continuous_re.continuousAt.comp h2)).sub
      ((Complex.continuous_re.continuousAt.comp h1).mul
        (Complex.continuous_im.continuousAt.comp h2))
  obtain ⟨ε₁, hε₁, hball₁⟩ := Metric.eventually_nhds_iff_ball.1 (hK.eventually_ne hcurv)
  obtain ⟨ε₂, hε₂, hball₂⟩ := Metric.isOpen_iff.1 hU m hm
  set ε := min ε₁ ε₂ with hεdef
  have hε : 0 < ε := lt_min hε₁ hε₂
  have hsubU : Metric.ball m ε ⊆ U :=
    fun t ht => hball₂ (Metric.ball_subset_ball (min_le_right _ _) ht)
  have hpair : ∀ s ∈ Metric.ball m ε, ∀ t ∈ Metric.ball m ε, wedge (d2γ s) (dγ t) ≠ 0 := by
    intro s hs t ht
    refine hball₁ (s, t) ?_
    rw [Metric.mem_ball, Prod.dist_eq]
    exact max_lt (lt_of_lt_of_le (Metric.mem_ball.1 hs) (min_le_left _ _))
      (lt_of_lt_of_le (Metric.mem_ball.1 ht) (min_le_left _ _))
  filter_upwards [mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds m hε), self_mem_nhdsWithin]
    with x hx hxne
  obtain ⟨ξ, hξ, η, hη, hpos, hfac⟩ := tangency_factor_of_meet (convex_ball m ε)
    (fun s hs => hd s (hsubU hs)) (fun s hs => hd2 s (hsubU hs))
    (Metric.mem_ball_self hε) hx hxne hmeet
  rw [hfac]
  exact mul_ne_zero hpos.ne' (hpair η hη ξ hξ)

/-! ### Isolated zeros on a compact set are finitely many

`PhaseStateDichotomy.finite_zeros_of_hasDerivAt_ne_zero` runs this argument for the
simple-zero case.  The tangency function has one zero that is not simple — the meeting
parameter — so the compactness step is separated from the reason a zero is isolated, and
takes that reason as a hypothesis. -/

/-- **A function whose zeros are isolated has finitely many on a compact set.**  If the zero
set were infinite it would accumulate somewhere in the compact, the limit point would itself
be a zero by continuity, and isolation at that point contradicts the accumulation. -/
theorem finite_of_isolated_zeros {f : ℝ → ℝ} {K : Set ℝ} (hK : IsCompact K)
    (hcont : ∀ x ∈ K, ContinuousAt f x)
    (hiso : ∀ p ∈ K, f p = 0 → ∀ᶠ x in 𝓝[≠] p, f x ≠ 0) :
    {x | x ∈ K ∧ f x = 0}.Finite := by
  classical
  by_contra hinf
  rw [Set.not_finite] at hinf
  obtain ⟨p, hpK, hacc⟩ := hinf.exists_accPt_of_subset_isCompact hK (fun x hx => hx.1)
  haveI : (𝓝[≠] p ⊓ Filter.principal {x | x ∈ K ∧ f x = 0}).NeBot := hacc
  have hfp : f p = 0 := by
    have h1 : Filter.Tendsto f (𝓝[≠] p ⊓ Filter.principal {x | x ∈ K ∧ f x = 0})
        (𝓝 (f p)) :=
      (hcont p hpK).tendsto.mono_left (le_trans inf_le_left nhdsWithin_le_nhds)
    have h2 : Filter.Tendsto f (𝓝[≠] p ⊓ Filter.principal {x | x ∈ K ∧ f x = 0})
        (𝓝 0) := by
      refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
      filter_upwards [Filter.mem_inf_of_right (Filter.mem_principal_self _)] with z hz
      exact hz.2.symm
    exact tendsto_nhds_unique h1 h2
  have hbad : ∀ᶠ _z in (𝓝[≠] p ⊓ Filter.principal {x | x ∈ K ∧ f x = 0}), False := by
    filter_upwards [Filter.mem_inf_of_left (hiso p hpK hfp),
      Filter.mem_inf_of_right (Filter.mem_principal_self _)] with z h1 h2
    exact h1 h2.2
  exact (Filter.eventually_false_iff_eq_bot.1 hbad ▸ (by infer_instance :
    (𝓝[≠] p ⊓ Filter.principal {x | x ∈ K ∧ f x = 0}).NeBot)).ne rfl

/-- **The crossing set of a regular `C²` arc of nonvanishing curvature is finite.**  Both
kinds of zero are isolated: off the meeting parameter by the simple-zero step, at it by the
two mean values.  No analyticity enters, and the meeting parameter needs no hypothesis of
its own — the same curvature condition covers it. -/
theorem finite_tangency_zeros {γ dγ d2γ : ℝ → ℂ} {β : ℂ} {U : Set ℝ} {a b : ℝ}
    (hU : IsOpen U) (hsub : Icc a b ⊆ U)
    (hd : ∀ s ∈ U, HasDerivAt γ (dγ s) s)
    (hd2 : ∀ s ∈ U, HasDerivAt dγ (d2γ s) s) (hc2 : ContinuousOn d2γ U)
    (hreg : ∀ s ∈ Icc a b, dγ s ≠ 0)
    (hcurv : ∀ s ∈ Icc a b, wedge (d2γ s) (dγ s) ≠ 0) :
    {x | x ∈ Icc a b ∧ tangency γ dγ β x = 0}.Finite := by
  refine finite_of_isolated_zeros isCompact_Icc
    (fun x hx => (hasDerivAt_tangency (hd x (hsub hx)) (hd2 x (hsub hx))).continuousAt)
    (fun p hp hzero => ?_)
  by_cases hmeet : γ p = β
  · exact tangency_ne_zero_nhdsNE_of_meet hU (hsub hp) hd hd2 hc2 hmeet (hcurv p hp)
  · -- a simple zero, by the curvature at `p`
    have hchord : γ p - β ≠ 0 := sub_ne_zero.2 hmeet
    have hsimple : tangency γ d2γ β p ≠ 0 :=
      wedge_ne_zero_of_wedge_eq_zero (hreg p hp) hchord hzero (hcurv p hp)
    have hev : ∀ᶠ z in 𝓝[≠] p, tangency γ dγ β z ≠ tangency γ dγ β p :=
      (hasDerivAt_tangency (hd p (hsub hp)) (hd2 p (hsub hp))).tendsto_nhdsNE hsimple
        self_mem_nhdsWithin
    filter_upwards [hev] with z hz
    rwa [hzero] at hz

/-! ### The crossing condition is the tangency condition

`hstate` states its critical set as `ϑ x - φ x = j·π` for an **integer** `j`, which reads as
a condition quantified over `j`.  It is not: `ϑ` is a branch of `arg γ'` and `φ` one of
`arg (γ - β)`, so their difference is an integer multiple of `π` exactly where the wedge of
tangent and chord vanishes.  The quantifier is discharged once. -/

/-- **A crossing parameter is a zero of the tangency function.**  Both angles are the
constructed branches, so the two polar decompositions are available and the difference of
the arguments is read off them directly.  The base of the chord's branch is free — the
right-hand component of a meeting uses the branch based at `b`. -/
theorem tangency_eq_zero_of_polarAngle_sub {γ dγ d2γ : ℝ → ℂ} {β : ℂ} {U : Set ℝ}
    {a b a' b' c₀ : ℝ} (hab : a ≤ b) (hU : IsOpen U) (hsub : Icc a b ⊆ U)
    (hd : ∀ s ∈ U, HasDerivAt γ (dγ s) s)
    (hd2 : ∀ s ∈ U, HasDerivAt dγ (d2γ s) s) (hc2 : ContinuousOn d2γ U)
    (hreg : ∀ s ∈ Icc a b, dγ s ≠ 0)
    (hab' : a' ≤ b') (hsub' : Icc a' b' ⊆ Icc a b) (hne : ∀ s ∈ Icc a' b', γ s ≠ β)
    (hc₀ : c₀ ∈ Icc a' b') {x : ℝ} (hx : x ∈ Icc a' b') {j : ℤ}
    (hj : polarAngle dγ d2γ 0 a x - polarAngle γ dγ β c₀ x = (j : ℝ) * π) :
    tangency γ dγ β x = 0 := by
  have hcd : ContinuousOn dγ U := fun s hs => (hd2 s hs).continuousAt.continuousWithinAt
  have hdx : dγ x = ((polarModulus dγ d2γ 0 a x : ℝ) : ℂ)
      * Complex.exp (((polarAngle dγ d2γ 0 a x : ℝ) : ℂ) * Complex.I) := by
    have h := polar_decomposition (γ := dγ) (dγ := d2γ) (β := 0) hab hU hsub hd2 hc2
      (fun s hs => hreg s hs) (hsub' hx)
    rwa [sub_zero] at h
  have hchord : γ x - β = ((polarModulus γ dγ β c₀ x : ℝ) : ℂ)
      * Complex.exp (((polarAngle γ dγ β c₀ x : ℝ) : ℂ) * Complex.I) :=
    polar_decomposition_base hab' hU (hsub'.trans hsub) hd hcd hne hc₀ hx
  set ν := polarModulus dγ d2γ 0 a x
  set ϑ := polarAngle dγ d2γ 0 a x
  set ρ := polarModulus γ dγ β c₀ x
  set φ := polarAngle γ dγ β c₀ x
  have hconj : (starRingEnd ℂ) (γ x - β)
      = ((ρ : ℝ) : ℂ) * Complex.exp ((((-φ : ℝ)) : ℂ) * Complex.I) := by
    rw [hchord, map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
    congr 1
    simp [Complex.conj_I]
  have hmul : ((ν : ℝ) : ℂ) * Complex.exp (((ϑ : ℝ) : ℂ) * Complex.I)
        * (((ρ : ℝ) : ℂ) * Complex.exp ((((-φ : ℝ)) : ℂ) * Complex.I))
      = ((ν * ρ : ℝ) : ℂ) * Complex.exp ((((ϑ - φ : ℝ)) : ℂ) * Complex.I) := by
    rw [Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_neg, sub_mul, Complex.exp_sub,
      neg_mul, Complex.exp_neg]
    field_simp
  rw [tangency, wedge_eq_im_mul_conj, hdx, hconj, hmul, Complex.mul_im,
    Complex.exp_ofReal_mul_I_im, Complex.exp_ofReal_mul_I_re, Complex.ofReal_re,
    Complex.ofReal_im, hj]
  simp [Real.sin_int_mul_pi]

/-! ### `sum_eVariationOn_branch_le` with its state discharged

Everything `hstate` asks for is now available: which of the two states the arc is in comes
from `PhaseStateDichotomy.miss_or_meet_once`, the finite set from `finite_tangency_zeros`,
and the identification of the critical set with the zeros of the tangency function from
`tangency_eq_zero_of_polarAngle_sub`.  One finite set serves both components of a meeting,
because the tangency function does not depend on which endpoint the chord's branch is based
at.

The branch family is **chosen** here rather than assumed: on a meeting the blocks left of the
meeting parameter take the branch based at `a` and those right of it the one based at `b`,
and no block contains the meeting parameter because the amplitude does not vanish on a
block. -/

/-- **`cor:linear-phase-variation` at one zero of `B`, with no state hypothesis.**  The
regularity is the arc's `C²` package, the geometry is `wedge (γ'' s) (γ' s) ≠ 0` — the
signed curvature — and injectivity is what makes the meeting parameter unique.

`hfree` is the hypothesis the composition already carries: the amplitude does not vanish on
a retained block, and an amplitude zero is exactly a parameter where `B ∘ γ` vanishes.

**`hfree` is stated over closed blocks including the degenerate ones**, where
`AngularDiscrepancyFT.FTPhaseSupply` asks for nonvanishing only when `Lb i < Rb i`.  The
extra content is one case: a block collapsed to the single parameter the arc meets `β` at.
`sum_eVariationOn_branch_le`'s own block clause cannot place such a block on either side of
the meeting parameter, so the strengthening is in that lemma rather than here.  It costs a
caller nothing — the variation over a singleton is `0`, so a degenerate block is dropped from
the family rather than accommodated. -/
theorem exists_phaseState_of_curvature {γ dγ d2γ : ℝ → ℂ} {U : Set ℝ} {a b : ℝ} {β : ℂ}
    {k : ℕ} {Lb Rb : Fin k → ℝ}
    (hab : a ≤ b) (hU : IsOpen U) (hsub : Icc a b ⊆ U)
    (hd : ∀ s ∈ U, HasDerivAt γ (dγ s) s)
    (hd2 : ∀ s ∈ U, HasDerivAt dγ (d2γ s) s) (hc2 : ContinuousOn d2γ U)
    (hreg : ∀ s ∈ Icc a b, dγ s ≠ 0)
    (hcurv : ∀ s ∈ Icc a b, wedge (d2γ s) (dγ s) ≠ 0)
    (hinj : Set.InjOn γ (Icc a b))
    (hJ : ∀ i, Icc (Lb i) (Rb i) ⊆ Icc a b)
    (hfree : ∀ i, ∀ x ∈ Icc (Lb i) (Rb i), γ x ≠ β) :
    ∃ ψ : Fin k → ℝ → ℝ,
      (∀ i, ψ i = polarAngle γ dγ β a ∨ ψ i = polarAngle γ dγ β b) ∧
      ((∃ S : Finset ℝ, (∀ x ∈ Icc a b, γ x ≠ β) ∧ (∀ x ∈ S, x ∈ Icc a b)
          ∧ (∀ x ∈ Ioo a b, ∀ j : ℤ,
              polarAngle dγ d2γ 0 a x - polarAngle γ dγ β a x = (j : ℝ) * π → x ∈ S)
          ∧ ∀ i, ψ i = polarAngle γ dγ β a)
        ∨ (∃ m, a ≤ m ∧ m ≤ b ∧ ∃ S₁ S₂ : Finset ℝ, γ m = β
            ∧ (∀ x ∈ Icc a b, x ≠ m → γ x ≠ β)
            ∧ (∀ x ∈ Ioo a m, ∀ j : ℤ,
                polarAngle dγ d2γ 0 a x - polarAngle γ dγ β a x = (j : ℝ) * π → x ∈ S₁)
            ∧ (∀ x ∈ Ioo m b, ∀ j : ℤ,
                polarAngle dγ d2γ 0 a x - polarAngle γ dγ β b x = (j : ℝ) * π → x ∈ S₂)
            ∧ ∀ i, (Icc (Lb i) (Rb i) ⊆ Ico a m ∧ ψ i = polarAngle γ dγ β a)
                ∨ (Icc (Lb i) (Rb i) ⊆ Ioc m b ∧ ψ i = polarAngle γ dγ β b))) := by
  classical
  have hfin := finite_tangency_zeros (β := β) hU hsub hd hd2 hc2 hreg hcurv
  set S : Finset ℝ := hfin.toFinset with hSdef
  have hSmem : ∀ x, x ∈ Icc a b → tangency γ dγ β x = 0 → x ∈ S := by
    intro x hx hz
    rw [hSdef, Set.Finite.mem_toFinset]
    exact ⟨hx, hz⟩
  have hSsub : ∀ x ∈ S, x ∈ Icc a b := by
    intro x hx
    rw [hSdef, Set.Finite.mem_toFinset] at hx
    exact hx.1
  rcases miss_or_meet_once hinj β with hmiss | ⟨m, hm, hmβ, hother⟩
  · refine ⟨fun _ => polarAngle γ dγ β a, fun _ => Or.inl rfl, Or.inl ?_⟩
    refine ⟨S, hmiss, hSsub, fun x hx j hj => ?_, fun _ => rfl⟩
    exact hSmem x (Ioo_subset_Icc_self hx)
      (tangency_eq_zero_of_polarAngle_sub hab hU hsub hd hd2 hc2 hreg hab (subset_refl _)
        hmiss ⟨le_rfl, hab⟩ (Ioo_subset_Icc_self hx) hj)
  · -- the arc meets `β`, at the single parameter `m`
    have hmne : ∀ x ∈ Icc a b, x ≠ m → γ x ≠ β := hother
    have hnotmem : ∀ i, Lb i ≤ Rb i → m ∉ Icc (Lb i) (Rb i) := by
      intro i _ hmem
      exact hfree i m hmem hmβ
    refine ⟨fun i => if Rb i < m then polarAngle γ dγ β a else polarAngle γ dγ β b,
      fun i => by by_cases h : Rb i < m <;> simp [h], Or.inr ?_⟩
    refine ⟨m, hm.1, hm.2, S, S, hmβ, hmne, fun x hx j hj => ?_, fun x hx j hj => ?_,
      fun i => ?_⟩
    · have hxab : x ∈ Icc a b := ⟨hx.1.le, hx.2.le.trans hm.2⟩
      refine hSmem x hxab (tangency_eq_zero_of_polarAngle_sub hab hU hsub hd hd2 hc2 hreg
        (a' := a) (b' := x) hx.1.le (Icc_subset_Icc le_rfl hxab.2)
        (fun s hs => hmne s ⟨hs.1, hs.2.trans hxab.2⟩ (ne_of_lt (lt_of_le_of_lt hs.2 hx.2)))
        ⟨le_rfl, hx.1.le⟩ ⟨hx.1.le, le_rfl⟩ hj)
    · have hxab : x ∈ Icc a b := ⟨hm.1.trans hx.1.le, hx.2.le⟩
      refine hSmem x hxab (tangency_eq_zero_of_polarAngle_sub hab hU hsub hd hd2 hc2 hreg
        (a' := x) (b' := b) hx.2.le (Icc_subset_Icc hxab.1 le_rfl)
        (fun s hs => hmne s ⟨hxab.1.trans hs.1, hs.2⟩ (ne_of_gt (lt_of_lt_of_le hx.1 hs.1)))
        ⟨hx.2.le, le_rfl⟩ ⟨le_rfl, hx.2.le⟩ hj)
    · by_cases hlt : Rb i < m
      · refine Or.inl ⟨fun x hx => ⟨(hJ i hx).1, lt_of_le_of_lt hx.2 hlt⟩, by simp [hlt]⟩
      · refine Or.inr ⟨fun x hx => ⟨?_, (hJ i hx).2⟩, by simp [hlt]⟩
        rcases le_or_gt (Lb i) (Rb i) with hLR | hLR
        · have hmlt : m < Lb i := by
            rcases lt_trichotomy m (Lb i) with h | h | h
            · exact h
            · exact absurd ⟨h.ge, le_trans h.le hLR⟩ (hnotmem i hLR)
            · exact absurd ⟨h.le, not_lt.1 hlt⟩ (hnotmem i hLR)
          exact lt_of_lt_of_le hmlt hx.1
        · exact absurd (le_trans hx.1 hx.2) (not_le.2 hLR)

/-- **`cor:linear-phase-variation` at one zero of `B`, with no state hypothesis.**  The
state is produced by `exists_phaseState_of_curvature` and consumed here. -/
theorem sum_eVariationOn_of_curvature {γ dγ d2γ : ℝ → ℂ} {U : Set ℝ} {a b Kγ : ℝ} {β : ℂ}
    {k : ℕ} {Lb Rb : Fin k → ℝ}
    (hab : a ≤ b) (hU : IsOpen U) (hsub : Icc a b ⊆ U)
    (hd : ∀ s ∈ U, HasDerivAt γ (dγ s) s)
    (hd2 : ∀ s ∈ U, HasDerivAt dγ (d2γ s) s) (hc2 : ContinuousOn d2γ U)
    (hreg : ∀ s ∈ Icc a b, dγ s ≠ 0) (hKγ : 0 ≤ Kγ)
    (hKvar : eVariationOn (polarAngle dγ d2γ 0 a) (Icc a b) ≤ ENNReal.ofReal Kγ)
    (hcurv : ∀ s ∈ Icc a b, wedge (d2γ s) (dγ s) ≠ 0)
    (hinj : Set.InjOn γ (Icc a b))
    (hJ : ∀ i, Icc (Lb i) (Rb i) ⊆ Icc a b)
    (hord : ∀ i j : Fin k, i < j → Rb i ≤ Lb j)
    (hfree : ∀ i, ∀ x ∈ Icc (Lb i) (Rb i), γ x ≠ β) :
    ∃ ψ : Fin k → ℝ → ℝ,
      (∀ i, ψ i = polarAngle γ dγ β a ∨ ψ i = polarAngle γ dγ β b) ∧
      ∑ i, eVariationOn (ψ i) (Icc (Lb i) (Rb i)) ≤ ENNReal.ofReal (Kγ + π) := by
  obtain ⟨ψ, hψ, hstate⟩ :=
    exists_phaseState_of_curvature hab hU hsub hd hd2 hc2 hreg hcurv hinj hJ hfree
  exact ⟨ψ, hψ, sum_eVariationOn_branch_le (β := β) hab hU hsub hd hd2 hc2 hreg hKγ hKvar
    hJ hord hstate⟩

/-! ### The curvature hypothesis at the pencil's branch

`γ = τe^{iθ}` gives `γ' = e^{iθ}(τ' + iτ)` and `γ'' = e^{iθ}(τ'' + 2iτ' - τ)`
(`BranchCurvature`), and the unit factor cancels against its own conjugate.  What is left is
the classical polar curvature numerator, so `sum_eVariationOn_of_curvature`'s geometric
hypothesis reads, at the pencil's branch, as `τ² + 2τ'² - ττ'' ≠ 0` — the branch is nowhere
inflected.  Measured positive on every admissible pencil sampled in
`../scripts/check_branch_convexity.py`. -/

/-- **The signed curvature of the branch, in polar form.**  Pure algebra: the modulus-one
factor cancels and the remaining product is expanded. -/
theorem wedge_ftGammaDeriv2_ftGammaDeriv {n : ℕ} (a : Fin n → ℝ) (r l : ℕ) (θ : ℝ) :
    wedge (ftGammaDeriv2 a r l θ) (ftGammaDeriv a r l θ)
      = ftTau a r l θ ^ 2 + 2 * ftTauDeriv a r l θ ^ 2
        - ftTau a r l θ * ftTauDeriv2 a r l θ := by
  have hcj : (starRingEnd ℂ) (Complex.exp (((θ : ℝ) : ℂ) * Complex.I))
      = (Complex.exp (((θ : ℝ) : ℂ) * Complex.I))⁻¹ := by
    rw [← Complex.exp_conj, ← Complex.exp_neg]
    congr 1
    simp [Complex.conj_I]
  have hexp : Complex.exp (((θ : ℝ) : ℂ) * Complex.I) ≠ 0 := Complex.exp_ne_zero _
  set E := Complex.exp (((θ : ℝ) : ℂ) * Complex.I) with hE
  set A := ((ftTauDeriv2 a r l θ : ℝ) : ℂ) + 2 * ((ftTauDeriv a r l θ : ℝ) : ℂ) * Complex.I
      - ((ftTau a r l θ : ℝ) : ℂ) with hA
  set B := ((ftTauDeriv a r l θ : ℝ) : ℂ) + ((ftTau a r l θ : ℝ) : ℂ) * Complex.I with hB
  have hstep : E * A * (starRingEnd ℂ) (E * B) = A * (starRingEnd ℂ) B := by
    rw [map_mul, hcj]
    field_simp
  rw [wedge_eq_im_mul_conj, ftGammaDeriv2, ftGammaDeriv, ← hA, ← hB, ← hE, hstep, hA, hB]
  simp [Complex.mul_im, Complex.mul_re]
  ring

/-- **The curvature hypothesis cannot be dropped.**  A straight arc through `β` has a
tangency function identically zero — every line from `β` meets it tangentially in the limiting
sense — so the crossing set is the whole parameter interval and no finite set contains it.
This is the case `wedge (γ'' s) (γ' s) ≠ 0` excludes, and it is not hypothetical. -/
theorem not_finite_tangency_zeros_of_line :
    ¬ {x | x ∈ Icc (0 : ℝ) 1 ∧ tangency (fun t : ℝ => (t : ℂ)) (fun _ => 1) 0 x = 0}.Finite := by
  have heq : {x | x ∈ Icc (0 : ℝ) 1 ∧ tangency (fun t : ℝ => (t : ℂ)) (fun _ => 1) 0 x = 0}
      = Icc (0 : ℝ) 1 := by
    ext x
    simp [tangency, wedge]
  rw [heq]
  exact Set.Icc_infinite (by norm_num)

/-- **`finite_tangency_zeros` is not satisfied by having no zeros at all.**  The parabola
`γ(x) = x + (x² + 1)i` viewed from the origin has curvature `2` everywhere and tangency
function `x² - 1`, so the hypotheses hold and the crossing set on `[-2, 2]` is the two-point
set rather than the empty one.

Chosen over a circle because it needs no exponential, and over a line because a line has no
curvature — which is the point of `not_finite_tangency_zeros_of_line`. -/
theorem finite_tangency_zeros_witness_nonempty :
    ∃ (γ dγ d2γ : ℝ → ℂ) (β : ℂ) (U : Set ℝ) (a b : ℝ),
      IsOpen U ∧ Icc a b ⊆ U ∧ (∀ s ∈ U, HasDerivAt γ (dγ s) s)
        ∧ (∀ s ∈ U, HasDerivAt dγ (d2γ s) s) ∧ ContinuousOn d2γ U
        ∧ (∀ s ∈ Icc a b, dγ s ≠ 0) ∧ (∀ s ∈ Icc a b, wedge (d2γ s) (dγ s) ≠ 0)
        ∧ (1 : ℝ) ∈ {x | x ∈ Icc a b ∧ tangency γ dγ β x = 0} := by
  have hofReal : ∀ x : ℝ, HasDerivAt (fun t : ℝ => ((t : ℝ) : ℂ)) 1 x := by
    intro x
    simpa using (hasDerivAt_id x).ofReal_comp
  refine ⟨fun x => ((x : ℝ) : ℂ) + (((x : ℝ) : ℂ) ^ 2 + 1) * Complex.I,
    fun x => 1 + 2 * ((x : ℝ) : ℂ) * Complex.I, fun _ => 2 * Complex.I, 0, univ, -2, 2,
    isOpen_univ, subset_univ _, fun s _ => ?_, fun s _ => ?_, continuousOn_const,
    fun s _ => ?_, fun s _ => ?_, ⟨by norm_num, ?_⟩⟩
  · refine ((hofReal s).add ((((hofReal s).pow 2).add_const 1).mul_const Complex.I)).congr_deriv ?_
    ring
  · refine ((((hofReal s).const_mul (2 : ℂ)).mul_const Complex.I).const_add 1).congr_deriv ?_
    ring
  · intro h
    have := congrArg Complex.re h
    simp at this
  · simp [wedge]
  · simp only [tangency, wedge]
    norm_num

end ForgacsTran
