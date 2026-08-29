/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Shields.Analysis.Complex.Rouche

/-!
# Hurwitz's theorem on a disc

Zero counts pass to a uniform limit.  Where `f` is analytic on a closed disc and zero-free on its
circle, any function uniformly close to `f` on that circle carries exactly the zero count of `f`
inside, with multiplicity; and where `f` vanishes inside, so does every function close enough.

Mathlib has no Hurwitz theorem for analytic functions at the pinned revision.  The `Hurwitz` in
`Mathlib.NumberTheory.LSeries` is Hurwitz *zeta*, an unrelated object.

## Main results

* `Shields.eventually_zero_free_of_tendstoUniformlyOn` — a limit zero-free on a compact set forces
  the approximants eventually zero-free there.
* `Shields.factoredOn_of_norm_sub_lt` — `Shields.factoredOn_of_norm_lt` with the perturbation
  written as a difference, which is the form a convergent family supplies it in.
* `Shields.eventually_factoredOn_of_tendstoUniformlyOn` — **Hurwitz's theorem**: the count inside
  transfers to every late approximant.
* `Shields.factoredOn_one_of_simple_zero` and
  `Shields.eventually_existsUnique_zero_of_simple_zero` — a simple zero of the limit at the center
  becomes exactly one zero of each late approximant in the disc.
* `Shields.eventually_zero_count` — the count over an observation range: one zero in each of
  finitely many disks, and none on a compact set disjoint from them.
* `Shields.factoredOn_of_dist_lt_of_const` and `Shields.eventually_factoredOn_sub_const` — the
  solution count of `h = w` is locally constant in `w`, which is Hurwitz with the perturbation a
  constant rather than a limit.
* `Shields.eventually_exists_zero_of_tendstoUniformlyOn` — the converse direction: a zero of the
  limit forces a zero of every late approximant strictly inside.
* `Shields.mem_of_tendstoLocallyUniformly_of_zeros_subset` — a closed constraint on the zeros of the
  approximants passes to the zeros of the limit.

## Implementation notes

Everything runs through `Shields.FactoredOn`, the displayed factorization of
`Shields.Analysis.Complex.Rouche`, rather than through a divisor: the count a caller wants is the
length of the list, and `Shields.factoredOn_of_norm_lt` transports it one-sidedly, so no
factorization of the perturbed function is ever assumed.

`Shields.factoredOn_id`, `Shields.tendstoUniformlyOn_sub_const` and
`Shields.eventually_existsUnique_zero_natCast_shift` are non-vacuity witnesses on the family
`z ↦ z - cₙ`, inhabited by a sequence Mathlib already knows converges.

## Papers depending on this file

* `edrei-spectral-classification`, `exterior-sinc-hierarchies`, `hard-edge-edrei`,
  `toeplitz-newton-boundary` — zero counting under a limit.

## Tags

Hurwitz, uniform convergence, zero counting, Rouché, analytic function
-/

open Filter Topology Set

namespace Shields

/-! ## No intruding zeros -/

/-- **No intruding zeros.**  Where the limit is zero-free on a compact set, the
approximants are eventually zero-free there. -/
theorem eventually_zero_free_of_tendstoUniformlyOn
    {X : Type*} [TopologicalSpace X] {E : Type*} [NormedAddCommGroup E]
    {ι : Type*} {L : Filter ι} {F : ι → X → E} {f : X → E} {K : Set X}
    (hK : IsCompact K) (hfc : ContinuousOn f K) (hfne : ∀ x ∈ K, f x ≠ 0)
    (hunif : TendstoUniformlyOn F f L K) :
    ∀ᶠ i in L, ∀ x ∈ K, F i x ≠ 0 := by
  obtain ⟨m, hm, hlb⟩ := exists_pos_forall_le_norm hK hfc hfne
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hunif m hm] with i hi x hx hx0
  have hdist := hi x hx
  rw [dist_eq_norm, hx0, sub_zero] at hdist
  exact absurd (hlb x hx) (not_le.mpr hdist)

/-! ## The Rouché corollary

`factoredOn_of_norm_lt` states the perturbation additively.  A convergent family
supplies it as a difference, so that is the form recorded here. -/

/-- **The zero count survives a small perturbation.**  If `F` differs from `f` by
less than `‖f‖` on the circle, and `f` factors with `n` roots inside, then so does
`F`.

This is `factoredOn_of_norm_lt` with the perturbation written as a difference,
which is the form a convergent family supplies it in. -/
theorem factoredOn_of_norm_sub_lt {c : ℂ} {R : ℝ} (hR : 0 < R) {f F : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall c R))
    (hF : AnalyticOnNhd ℂ F (Metric.closedBall c R))
    (hlt : ∀ z ∈ Metric.sphere c R, ‖F z - f z‖ < ‖f z‖)
    {n : ℕ} {a : ℕ → ℂ} {G : ℂ → ℂ} (hfac : FactoredOn f c R n a G) :
    ∃ (a' : ℕ → ℂ) (G' : ℂ → ℂ), FactoredOn F c R n a' G' := by
  obtain ⟨a', G', hfac'⟩ := factoredOn_of_norm_lt (g := fun w => F w - f w) hR hf
    (fun z hz => (hF z hz).sub (hf z hz)) hlt hfac
  exact ⟨a', G', hfac'.congr fun z => by ring⟩

/-! ## Hurwitz's theorem

Over `ℂ`, uniform convergence on the circle is by itself enough: the count inside
is a contour integral over that circle, so nothing about the interior is needed.
The real-variable statement has no such form — `x + i⁻¹ sin(i²x)` converges
uniformly to `x` on `[-1,1]` with arbitrarily many zeros there — and a real proof
must consume convergence of the derivatives as well. -/

/-- **Hurwitz's theorem.**  If the approximants are analytic on the closed disk
and converge uniformly to `f` on the circle, where `f` does not vanish, then they
eventually carry exactly the zero count of `f` inside, with multiplicity. -/
theorem eventually_factoredOn_of_tendstoUniformlyOn
    {ι : Type*} {L : Filter ι} {F : ι → ℂ → ℂ} {f : ℂ → ℂ} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall c R))
    (hF : ∀ i, AnalyticOnNhd ℂ (F i) (Metric.closedBall c R))
    (hfne : ∀ z ∈ Metric.sphere c R, f z ≠ 0)
    (hunif : TendstoUniformlyOn F f L (Metric.sphere c R))
    {n : ℕ} {a : ℕ → ℂ} {G : ℂ → ℂ} (hfac : FactoredOn f c R n a G) :
    ∀ᶠ i in L, ∃ (a' : ℕ → ℂ) (G' : ℂ → ℂ), FactoredOn (F i) c R n a' G' := by
  have hcont : ContinuousOn f (Metric.sphere c R) :=
    hf.continuousOn.mono Metric.sphere_subset_closedBall
  filter_upwards [eventually_norm_sub_lt_of_tendstoUniformlyOn (isCompact_sphere c R)
    hcont hfne hunif] with i hi
  exact factoredOn_of_norm_sub_lt hR hf (hF i) hi hfac

/-! ## A simple zero factors with one root

To read Hurwitz as "exactly one zero" the limit's own factorization must display
exactly one.  `dslope` supplies it: `f z = (z - c)·(dslope f c) z` holds
identically, and the cofactor is zero-free on the disk exactly when `c` is the
only zero and is simple. -/

/-- **A simple zero, displayed.**  If `f` vanishes at the center with nonzero
derivative and nowhere else on the closed disk, it factors with the single root
`c` and cofactor `dslope f c`. -/
theorem factoredOn_one_of_simple_zero {c : ℂ} {R : ℝ} (hR : 0 < R) {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall c R))
    (hfc : f c = 0) (hd : deriv f c ≠ 0)
    (hne : ∀ z ∈ Metric.closedBall c R, z ≠ c → f z ≠ 0) :
    FactoredOn f c R 1 (fun _ => c) (dslope f c) where
  mem_ball := fun _ _ => Metric.mem_ball_self hR
  analytic := fun z hz =>
    analyticAt_dslope (hf c (Metric.mem_closedBall_self hR.le)) (hf z hz)
  ne_zero := by
    intro z hz
    rcases eq_or_ne z c with rfl | hzc
    · rwa [dslope_same]
    · rw [dslope_of_ne f hzc, slope_def_field, hfc, sub_zero]
      exact div_ne_zero (hne z hz hzc) (sub_ne_zero.mpr hzc)
  eq := by
    intro z
    have h := sub_smul_dslope f c z
    rw [hfc, sub_zero, smul_eq_mul] at h
    simp [h.symm]

/-- **Exactly one zero, eventually.**  A simple zero of the limit at the center,
with no other zero on the closed disk, is inherited by the approximants: each
eventually has exactly one zero there. -/
theorem eventually_existsUnique_zero_of_simple_zero
    {ι : Type*} {L : Filter ι} {F : ι → ℂ → ℂ} {f : ℂ → ℂ} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall c R))
    (hF : ∀ i, AnalyticOnNhd ℂ (F i) (Metric.closedBall c R))
    (hfc : f c = 0) (hd : deriv f c ≠ 0)
    (hne : ∀ z ∈ Metric.closedBall c R, z ≠ c → f z ≠ 0)
    (hunif : TendstoUniformlyOn F f L (Metric.sphere c R)) :
    ∀ᶠ i in L, ∃! w : ℂ, w ∈ Metric.closedBall c R ∧ F i w = 0 := by
  have hfne : ∀ z ∈ Metric.sphere c R, f z ≠ 0 := by
    intro z hz
    have hzc : z ≠ c := by
      intro h
      rw [h, Metric.mem_sphere, dist_self] at hz
      exact absurd hz.symm hR.ne'
    exact hne z (Metric.sphere_subset_closedBall hz) hzc
  filter_upwards [eventually_factoredOn_of_tendstoUniformlyOn hR hf hF hfne hunif
    (factoredOn_one_of_simple_zero hR hf hfc hd hne)] with i hi
  obtain ⟨a', G', hfac⟩ := hi
  have hmem : a' 0 ∈ Metric.closedBall c R :=
    Metric.ball_subset_closedBall (hfac.mem_ball 0 Nat.one_pos)
  refine ⟨a' 0, ⟨hmem, (hfac.eq_zero_iff hmem).2 ⟨0, Nat.one_pos, rfl⟩⟩, ?_⟩
  rintro w ⟨hw, hw0⟩
  obtain ⟨j, hj, hja⟩ := (hfac.eq_zero_iff hw).1 hw0
  rw [← hja, Nat.lt_one_iff.mp hj]

/-! ## The paper's conclusion

The count over a whole observation range, rather than one disc:
one zero in each of the `N₀` disks around the lattice points, and no zero on the
compact complement. -/

/-- **Exactly one zero in each disk and none outside.**  With the limit carrying a
simple zero at the center of each of finitely many disks, no other zero on any of
them, and no zero at all on a compact set `K` disjoint from them, the
approximants eventually do the same.

`K` is the
compact complement of the disks in the observation range, and the disks are the
ones around the first `N₀` zeros of the limiting sinc. -/
theorem eventually_zero_count
    {ι : Type*} {L : Filter ι} {F : ι → ℂ → ℂ} {f : ℂ → ℂ}
    {N₀ : ℕ} (c : Fin N₀ → ℂ) (r : Fin N₀ → ℝ) (hr : ∀ j, 0 < r j)
    {K : Set ℂ} (hK : IsCompact K)
    (hFa : ∀ i j, AnalyticOnNhd ℂ (F i) (Metric.closedBall (c j) (r j)))
    (hfa : ∀ j, AnalyticOnNhd ℂ f (Metric.closedBall (c j) (r j)))
    (hfc : ∀ j, f (c j) = 0) (hd : ∀ j, deriv f (c j) ≠ 0)
    (hne : ∀ j, ∀ z ∈ Metric.closedBall (c j) (r j), z ≠ c j → f z ≠ 0)
    (hfK : ContinuousOn f K) (hfKne : ∀ z ∈ K, f z ≠ 0)
    (hunif : ∀ j, TendstoUniformlyOn F f L (Metric.sphere (c j) (r j)))
    (hunifK : TendstoUniformlyOn F f L K) :
    ∀ᶠ i in L, (∀ j, ∃! w : ℂ, w ∈ Metric.closedBall (c j) (r j) ∧ F i w = 0) ∧
      (∀ z ∈ K, F i z ≠ 0) := by
  have hdisks : ∀ᶠ i in L, ∀ j : Fin N₀,
      ∃! w : ℂ, w ∈ Metric.closedBall (c j) (r j) ∧ F i w = 0 := by
    rw [eventually_all]
    intro j
    exact eventually_existsUnique_zero_of_simple_zero (hr j) (hfa j) (fun i => hFa i j)
      (hfc j) (hd j) (hne j) (hunif j)
  filter_upwards [hdisks,
    eventually_zero_free_of_tendstoUniformlyOn hK hfK hfKne hunifK] with i h1 h2
  exact ⟨h1, h2⟩

/-! ## Root-count stability in a parameter

A caller fixes `z₀`, picks radii whose circles
carry no solution of `h(t) = 1/z₀`, and reads off Rouché that the count is the
same for every nearby `z`.  That is `factoredOn_of_norm_sub_lt` with the
perturbation a *constant*. -/

/-- **The solution count of `h(t) = w` is locally constant in `w`.**  If `h - w₀`
factors with `n` roots inside the circle and `|w - w₀|` is below the minimum of
`|h - w₀|` there, then `h - w` factors with `n` roots too. -/
theorem factoredOn_of_dist_lt_of_const {c : ℂ} {R : ℝ} (hR : 0 < R) {h : ℂ → ℂ} {w₀ w : ℂ}
    (hh : AnalyticOnNhd ℂ h (Metric.closedBall c R))
    (hlt : ∀ t ∈ Metric.sphere c R, ‖w - w₀‖ < ‖h t - w₀‖)
    {n : ℕ} {a : ℕ → ℂ} {G : ℂ → ℂ} (hfac : FactoredOn (fun t => h t - w₀) c R n a G) :
    ∃ (a' : ℕ → ℂ) (G' : ℂ → ℂ), FactoredOn (fun t => h t - w) c R n a' G' := by
  refine factoredOn_of_norm_sub_lt hR (fun t ht => (hh t ht).sub analyticAt_const)
    (fun t ht => (hh t ht).sub analyticAt_const) (fun t ht => ?_) hfac
  change ‖h t - w - (h t - w₀)‖ < ‖h t - w₀‖
  have hid : h t - w - (h t - w₀) = -(w - w₀) := by ring
  rw [hid, norm_neg]
  exact hlt t ht

/-- **The count is stable on a whole neighborhood.**  Packaging
`factoredOn_of_dist_lt_of_const` as an eventual statement: the number of solutions
of `h(t) = w` in the disk is the same as at `w₀` for all `w` near `w₀`.

This is the step a caller applies to thin annuli
around each distinct root modulus; iterating it over the finitely many moduli is
what makes every ordered modulus continuous. -/
theorem eventually_factoredOn_sub_const {c : ℂ} {R : ℝ} (hR : 0 < R) {h : ℂ → ℂ} {w₀ : ℂ}
    (hh : AnalyticOnNhd ℂ h (Metric.closedBall c R))
    (hne : ∀ t ∈ Metric.sphere c R, h t - w₀ ≠ 0)
    {n : ℕ} {a : ℕ → ℂ} {G : ℂ → ℂ} (hfac : FactoredOn (fun t => h t - w₀) c R n a G) :
    ∀ᶠ w in 𝓝 w₀, ∃ (a' : ℕ → ℂ) (G' : ℂ → ℂ),
      FactoredOn (fun t => h t - w) c R n a' G' := by
  have hcont : ContinuousOn (fun t => h t - w₀) (Metric.sphere c R) :=
    (hh.continuousOn.mono Metric.sphere_subset_closedBall).sub continuousOn_const
  obtain ⟨m, hm, hlb⟩ := exists_pos_forall_le_norm (isCompact_sphere c R) hcont hne
  filter_upwards [Metric.ball_mem_nhds w₀ hm] with w hw
  refine factoredOn_of_dist_lt_of_const hR hh (fun t ht => ?_) hfac
  rw [← dist_eq_norm]
  exact lt_of_lt_of_le (Metric.mem_ball.mp hw) (hlb t ht)

/-! ### A worked instance

The hypotheses are inhabited, and the conclusion is not vacuous: the identity
factors over the unit disk with the single root `0`, and the shifted family
`z ↦ z - cₙ` with `cₙ → 0` inherits that count — each member has exactly one zero
in the closed unit disk, which is `cₙ` itself. -/

/-- `id` factors over the unit disk with the single root `0`. -/
theorem factoredOn_id :
    FactoredOn (fun z : ℂ => z) 0 1 1 (fun _ => 0) (dslope (fun z : ℂ => z) 0) :=
  factoredOn_one_of_simple_zero one_pos (fun _ _ => analyticAt_id) rfl (by simp)
    (fun _ _ hz => hz)

/-- A vanishing shift converges uniformly to the identity on the unit circle. -/
theorem tendstoUniformlyOn_sub_const {c : ℕ → ℂ} (hc : Tendsto c atTop (𝓝 0)) :
    TendstoUniformlyOn (fun n : ℕ => fun z : ℂ => z - c n) (fun z : ℂ => z) atTop
      (Metric.sphere (0 : ℂ) 1) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [Metric.tendsto_nhds.mp hc ε hε] with n hn z _
  rw [dist_eq_norm]
  simpa [dist_eq_norm] using hn

/-- **Hurwitz on a concrete family.**  Each `z ↦ z - cₙ` eventually has exactly one
zero in the closed unit disk. -/
theorem eventually_existsUnique_zero_sub_const {c : ℕ → ℂ} (hc : Tendsto c atTop (𝓝 0)) :
    ∀ᶠ n in atTop, ∃! w : ℂ, w ∈ Metric.closedBall (0 : ℂ) 1 ∧ w - c n = 0 :=
  eventually_existsUnique_zero_of_simple_zero one_pos (fun _ _ => analyticAt_id)
    (fun _ _ _ => analyticAt_id.sub analyticAt_const) rfl (by simp) (fun _ _ hz => hz)
    (tendstoUniformlyOn_sub_const hc)

/-- The instance is inhabited by a sequence Mathlib already knows converges. -/
theorem tendsto_natCast_add_one_inv : Tendsto (fun n : ℕ => ((n : ℂ) + 1)⁻¹) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hnorm : ∀ n : ℕ, ‖((n : ℂ) + 1)⁻¹‖ = 1 / ((n : ℝ) + 1) := by
    intro n
    rw [norm_inv, one_div]
    congr 1
    rw [show ((n : ℂ) + 1) = (((n : ℝ) + 1 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by positivity)]
  simpa only [hnorm] using tendsto_one_div_add_atTop_nhds_zero_nat

/-- The worked instance at a concrete sequence: `z ↦ z - (n + 1)⁻¹` eventually has exactly one
zero in the closed unit disc. -/
theorem eventually_existsUnique_zero_natCast_shift :
    ∀ᶠ (n : ℕ) in atTop, ∃! w : ℂ,
      w ∈ Metric.closedBall (0 : ℂ) 1 ∧ w - ((n : ℂ) + 1)⁻¹ = 0 :=
  eventually_existsUnique_zero_sub_const tendsto_natCast_add_one_inv

/-! ## Zero persistence, and localization of the limit's zeros

The two statements above run from the limit to the approximants when the limit is *nonzero*.  The
converse direction — a zero of the limit forces zeros of the approximants nearby — is what localizes
the zero set of a limit inside a closed set the approximants' zeros are confined to.
-/

/-- **Hurwitz's theorem, zero persistence.**  If `f` vanishes at the center of a disc on whose
circle it is zero-free, then every function uniformly close to `f` on that circle vanishes somewhere
strictly inside.

No simplicity is assumed: `exists_factoredOn` supplies a factorization of `f` whose length is
positive because `f c = 0`, and `factoredOn_of_norm_sub_lt` transports that length to the
perturbation. -/
theorem eventually_exists_zero_of_tendstoUniformlyOn
    {ι : Type*} {L : Filter ι} {F : ι → ℂ → ℂ} {f : ℂ → ℂ} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall c R))
    (hF : ∀ i, AnalyticOnNhd ℂ (F i) (Metric.closedBall c R))
    (hfc : f c = 0)
    (hne : ∀ z ∈ Metric.sphere c R, f z ≠ 0)
    (hunif : TendstoUniformlyOn F f L (Metric.sphere c R)) :
    ∀ᶠ i in L, ∃ z ∈ Metric.ball c R, F i z = 0 := by
  obtain ⟨n, a, G, hfac⟩ := exists_factoredOn hR hf hne
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · obtain ⟨j, hj, -⟩ :=
        (hfac.eq_zero_iff (Metric.mem_closedBall_self hR.le)).mp hfc
      omega
    · exact h
  have hfc' : ContinuousOn f (Metric.sphere c R) := fun z hz =>
    ((hf z (Metric.sphere_subset_closedBall hz)).continuousAt).continuousWithinAt
  filter_upwards [eventually_norm_sub_lt_of_tendstoUniformlyOn (isCompact_sphere c R) hfc' hne
    hunif] with i hi
  obtain ⟨a', G', hfac'⟩ := factoredOn_of_norm_sub_lt hR hf (hF i) hi hfac
  have hmem := hfac'.mem_ball 0 hn
  exact ⟨a' 0, hmem, (hfac'.eq_zero_iff (Metric.ball_subset_closedBall hmem)).mpr ⟨0, hn, rfl⟩⟩

/-- An isolated zero has arbitrarily small circles about it carrying no zero.  The identity
theorem is what rules out the alternative, that `f` vanishes on a whole neighborhood, which is
where `∃ w, f w ≠ 0` is spent. -/
theorem exists_lt_forall_mem_sphere_ne_zero {f : ℂ → ℂ} (hfa : AnalyticOnNhd ℂ f univ)
    (hfne : ∃ w, f w ≠ 0) (z₀ : ℂ) {ε : ℝ} (hε : 0 < ε) :
    ∃ R : ℝ, 0 < R ∧ R < ε ∧ ∀ z ∈ Metric.sphere z₀ R, f z ≠ 0 := by
  rcases (hfa z₀ (mem_univ _)).eventually_eq_zero_or_eventually_ne_zero with hzero | hiso
  · obtain ⟨w, hw⟩ := hfne
    exact absurd (hfa.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      isPreconnected_univ (mem_univ z₀) hzero (mem_univ w)) hw
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hiso
  obtain ⟨δ, hδ, hδne⟩ := hiso
  refine ⟨min ε δ / 2, by have := lt_min hε hδ; linarith,
    by have := min_le_left ε δ; linarith, fun z hz => ?_⟩
  rw [Metric.mem_sphere] at hz
  refine hδne (y := z) (by rw [hz]; have := min_le_right ε δ; linarith) fun hzz => ?_
  rw [Set.mem_singleton_iff.mp hzz, dist_self] at hz
  have := lt_min hε hδ
  linarith

/-- **Hurwitz's theorem, zero localization.**  If the zeros of every approximant lie in a closed set
`S`, the approximants converge locally uniformly, and the limit does not vanish identically, then
every zero of the limit lies in `S`.

This is the statement that makes a closed constraint on the zeros — real, or real and nonpositive —
survive a locally uniform limit.  The identity theorem enters only to rule out the limit vanishing
on a neighborhood of the disputed point, which is where `∃ w, f w ≠ 0` is spent. -/
theorem mem_of_tendstoLocallyUniformly_of_zeros_subset
    {ι : Type*} {L : Filter ι} [L.NeBot] {F : ι → ℂ → ℂ} {f : ℂ → ℂ} {S : Set ℂ}
    (hS : IsClosed S) (hFd : ∀ i, Differentiable ℂ (F i))
    (hzeros : ∀ᶠ i in L, ∀ z, F i z = 0 → z ∈ S)
    (hconv : TendstoLocallyUniformly F f L)
    (hfne : ∃ w, f w ≠ 0) {z₀ : ℂ} (hz₀ : f z₀ = 0) :
    z₀ ∈ S := by
  by_contra hz₀S
  -- `f` is entire, being a locally uniform limit of entire functions.
  have hlu : TendstoLocallyUniformlyOn F f L univ := tendstoLocallyUniformlyOn_univ.mpr hconv
  have hfa : AnalyticOnNhd ℂ f univ :=
    (hlu.differentiableOn (.of_forall fun i => (hFd i).differentiableOn)
      isOpen_univ).analyticOnNhd isOpen_univ
  -- A radius `ε` inside the complement of `S`, then a zero-free circle inside that.
  obtain ⟨ε, hε, hεS⟩ := Metric.isOpen_iff.mp hS.isOpen_compl z₀ hz₀S
  obtain ⟨R, hR, hRε, hsphere⟩ := exists_lt_forall_mem_sphere_ne_zero hfa hfne z₀ hε
  have hunif : TendstoUniformlyOn F f L (Metric.sphere z₀ R) :=
    (tendstoLocallyUniformly_iff_forall_isCompact.mp hconv) _ (isCompact_sphere z₀ R)
  obtain ⟨i, hi, z, hzmem, hzzero⟩ := (hzeros.and
    (eventually_exists_zero_of_tendstoUniformlyOn hR (hfa.mono (subset_univ _))
      (fun i => ((hFd i).differentiableOn.analyticOnNhd isOpen_univ).mono (subset_univ _))
      hz₀ hsphere hunif)).exists
  exact hεS (Metric.ball_subset_ball hRε.le hzmem) (hi z hzzero)



/-! ### Axiom footprint -/

/-- info: 'Shields.eventually_zero_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms eventually_zero_count

/-- info: 'Shields.eventually_factoredOn_sub_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms eventually_factoredOn_sub_const

/-- info: 'Shields.mem_of_tendstoLocallyUniformly_of_zeros_subset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms mem_of_tendstoLocallyUniformly_of_zeros_subset

end Shields
