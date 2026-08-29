/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Instances.Int
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IntermediateValue

/-!
# The argument principle and Rouché's theorem for polynomials

Root counting inside a disc by a contour integral of the logarithmic derivative, and the
consequence that a small perturbation on the boundary circle does not change the count.

## Main results

* `Shields.circleIntegral_pow_div_sub_of_mem_ball` and
  `Shields.circleIntegral_pow_div_sub_of_lt`: Cauchy's integral formula and Cauchy's theorem for a
  simple pole weighted by `z ^ k`, and `Shields.circleIntegral_multiset_sum_pow_div_sub` for a
  multiset of them.  The unweighted cases are what the count is read off.
* `Shields.rootsIn`: the roots of a polynomial inside an open disc, with multiplicity.
* `Shields.circleIntegral_logDeriv_polynomial`: **the argument principle** -- the contour
  integral of `P' / P` over `|z - c| = R` is `2πi` times the number of roots inside.
* `Shields.card_rootsIn_add_eq`: **Rouché**, unconditionally, for polynomials.
* `Shields.card_rootsIn_add_eq_natDegree`: with all roots inside, the count is the degree.
* `Shields.eventually_card_rootsIn_eq`: a Hurwitz-type corollary for coefficientwise limits.
* `Shields.exists_pos_forall_le_norm` and
  `Shields.eventually_norm_sub_lt_of_tendstoUniformlyOn`: a continuous nowhere-zero function on a
  compact set is bounded away from zero, so a uniformly convergent family eventually stays within
  the limit's own modulus there.  That is the Rouché hypothesis, and it is stated over an
  arbitrary compact set in a normed group because every counting route below consumes it.

## Implementation notes

Rouché is proved by deforming along `P + t Q` for `t ∈ [0, 1]`. The count is an integer-valued
continuous function of `t`, hence constant -- `clamp01` keeps the deformation parameter in range so
that continuity is stated on all of `ℝ`.

Mathlib has no argument principle, no Rouché theorem and no winding number at the pinned revision,
and none is in flight: no `circleIntegral` lemma anywhere relates a contour integral to a root, zero
or divisor count. The analytic case is `Shields.Analysis.Complex.ArgumentPrinciple.Analytic`; the
only polynomial-specific step here is the split factorization through `Polynomial.roots`.

## Tags

argument principle, Rouché, winding number, root counting, contour integral
-/

namespace Shields

open Complex Metric Polynomial

/-! ### Bounded away from zero on a compact set

Stated for a normed space over an arbitrary topological domain rather than for real-valued
functions on `ℝ`, so that it applies to complex-valued families.
-/

/-- A continuous nowhere-zero function on a compact set is bounded away from
zero. -/
theorem exists_pos_forall_le_norm {X : Type*} [TopologicalSpace X]
    {E : Type*} [NormedAddCommGroup E] {f : X → E} {K : Set X} (hK : IsCompact K)
    (hfc : ContinuousOn f K) (hfne : ∀ x ∈ K, f x ≠ 0) :
    ∃ m : ℝ, 0 < m ∧ ∀ x ∈ K, m ≤ ‖f x‖ := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact ⟨1, one_pos, by simp⟩
  · obtain ⟨x₀, hx₀, hmin⟩ := hK.exists_isMinOn hne hfc.norm
    exact ⟨‖f x₀‖, norm_pos_iff.mpr (hfne x₀ hx₀), fun x hx => isMinOn_iff.mp hmin x hx⟩

/-- **Uniform convergence eventually stays inside the limit's modulus.**  On a compact set
carrying no zero of the limit, `‖F i - f‖ < ‖f‖` holds at every point of the set at once for all
late `i`.  This is the Rouché hypothesis, and the quantifier order is its content: one eventual
index serves the whole set, because the limit's modulus has a positive lower bound there. -/
theorem eventually_norm_sub_lt_of_tendstoUniformlyOn
    {X : Type*} [TopologicalSpace X] {E : Type*} [NormedAddCommGroup E]
    {ι : Type*} {L : Filter ι} {F : ι → X → E} {f : X → E} {K : Set X}
    (hK : IsCompact K) (hfc : ContinuousOn f K) (hfne : ∀ x ∈ K, f x ≠ 0)
    (hunif : TendstoUniformlyOn F f L K) :
    ∀ᶠ i in L, ∀ x ∈ K, ‖F i x - f x‖ < ‖f x‖ := by
  obtain ⟨m, hm, hlb⟩ := exists_pos_forall_le_norm hK hfc hfne
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hunif m hm] with i hi x hx
  have hdist := hi x hx
  rw [dist_eq_norm, ← norm_neg, neg_sub] at hdist
  exact lt_of_lt_of_le hdist (hlb x hx)

/-! ### Poles inside and outside the contour

A simple pole weighted by `z ^ k`.  A pole inside the circle contributes `2πi·a^k` to the integral
of `z^k/(z - a)`; a pole outside contributes nothing.  At `k = 0` these are Cauchy's integral
formula and Cauchy's theorem. -/

/-- `z^k/(z - a)` is circle-integrable whenever the pole misses the circle. -/
theorem circleIntegrable_pow_div_sub {c a : ℂ} {R : ℝ} (ha : a ∉ sphere c |R|) (k : ℕ) :
    CircleIntegrable (fun z => z ^ k / (z - a)) c R := by
  refine ContinuousOn.circleIntegrable' ?_
  refine (continuous_pow k).continuousOn.div (continuousOn_id.sub continuousOn_const) ?_
  intro z hz hz0
  rw [sub_eq_zero] at hz0
  exact ha (hz0 ▸ hz)

/-- **Cauchy's integral formula for the monomial `z^k`.**  A pole inside the circle contributes
`2πi·a^k`. -/
theorem circleIntegral_pow_div_sub_of_mem_ball {c a : ℂ} {R : ℝ} (ha : a ∈ ball c R) (k : ℕ) :
    (∮ z in C(c, R), z ^ k / (z - a)) = 2 * Real.pi * I * a ^ k := by
  have hd : DifferentiableOn ℂ (fun z : ℂ => z ^ k) (closedBall c R) :=
    (differentiable_pow k).differentiableOn
  have h := hd.circleIntegral_sub_inv_smul ha
  simp only [smul_eq_mul] at h
  simpa only [div_eq_inv_mul] using h

/-- A pole strictly outside the closed disc contributes nothing: `z^k/(z - a)` is differentiable on
the closed disc and Cauchy's theorem applies. -/
theorem circleIntegral_pow_div_sub_of_lt {c a : ℂ} {R : ℝ} (hR : 0 ≤ R) (ha : R < dist a c)
    (k : ℕ) : (∮ z in C(c, R), z ^ k / (z - a)) = 0 := by
  have hne : ∀ z ∈ closedBall c R, z - a ≠ 0 := by
    intro z hz hz0
    rw [sub_eq_zero] at hz0
    rw [mem_closedBall, hz0] at hz
    exact absurd hz (not_le.mpr ha)
  refine Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable hR
    Set.countable_empty ?_ ?_
  · exact (continuous_pow k).continuousOn.div (continuousOn_id.sub continuousOn_const) hne
  · intro z hz
    exact ((differentiable_pow k) z).div (differentiableAt_id.sub_const a)
      (hne z (ball_subset_closedBall hz.1))

/-- A simple pole strictly outside the closed disc contributes nothing.  This is the unweighted
case of `circleIntegral_pow_div_sub_of_lt`. -/
theorem circleIntegral_sub_inv_of_lt {c w : ℂ} {R : ℝ} (hR : 0 ≤ R) (hw : R < dist w c) :
    (∮ z in C(c, R), (z - w)⁻¹) = 0 := by
  simpa using circleIntegral_pow_div_sub_of_lt hR hw 0

/-- **The boundary hypothesis keeps the family zero-free on the circle.**  If `‖g‖ < ‖f‖` there,
then `f + t·g` never vanishes on the circle for `t ∈ [0,1]`, so the counting integral is defined
all along the family. -/
theorem add_smul_ne_zero_of_norm_lt {c : ℂ} {R : ℝ} (f g : ℂ → ℂ)
    (hlt : ∀ z ∈ Metric.sphere c |R|, ‖g z‖ < ‖f z‖) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1)
    {z : ℂ} (hz : z ∈ Metric.sphere c |R|) :
    f z + (t : ℂ) * g z ≠ 0 := by
  intro hc
  have hfz : ‖f z‖ ≤ ‖(t : ℂ) * g z‖ := by
    have hneg : f z = -((t : ℂ) * g z) := by linear_combination hc
    rw [hneg, norm_neg]
  have htg : ‖(t : ℂ) * g z‖ ≤ ‖g z‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1]
    exact mul_le_of_le_one_left (norm_nonneg _) ht.2
  exact absurd (hfz.trans htg) (not_le.mpr (hlt z hz))

/-- **A count that varies continuously cannot jump.**  A continuous integer-valued function on
`[0,1]` takes the same value at both ends: its image is preconnected, and `ℤ` is totally
disconnected. -/
theorem int_eq_of_continuousOn_Icc (N : ℝ → ℤ) (hN : ContinuousOn N (Set.Icc (0 : ℝ) 1)) :
    N 0 = N 1 := by
  have hpre : IsPreconnected (N '' Set.Icc (0 : ℝ) 1) := isPreconnected_Icc.image N hN
  exact hpre.subsingleton ⟨0, by norm_num, rfl⟩ ⟨1, by norm_num, rfl⟩

/-- An integer family whose real embedding is continuous is continuous for the discrete topology
on `ℤ` — `Int.isClosedEmbedding_coe_real` transfers it. -/
theorem continuous_int_of_continuous_cast {N : ℝ → ℤ}
    (h : Continuous fun t => ((N t : ℝ))) : Continuous N :=
  Int.isClosedEmbedding_coe_real.isEmbedding.continuous_iff.mpr h

/-- **A count read off a `2πi`-multiple cannot jump.**  For an integer-valued `N`, continuity of
`t ↦ 2πi · N t` forces `N 0 = N 1`: dividing by `2πi` and taking real parts makes the integer
family itself continuous, and a continuous integer family on `[0,1]` is constant. -/
theorem int_eq_of_continuous_mul_two_pi_I {N : ℝ → ℤ}
    (h : Continuous fun t : ℝ => (N t : ℂ) * (2 * Real.pi * I)) : N 0 = N 1 := by
  have hcast : Continuous fun t : ℝ => ((N t : ℂ)) := by
    simpa [mul_div_assoc, div_self two_pi_I_ne_zero] using h.div_const (2 * (Real.pi : ℂ) * I)
  have hreal : Continuous fun t : ℝ => ((N t : ℝ)) := by
    refine (Complex.continuous_re.comp hcast).congr fun t => ?_
    simp [Function.comp]
  exact int_eq_of_continuousOn_Icc N (continuous_int_of_continuous_cast hreal).continuousOn

-- Adapted: upstream asks for joint continuity on all of `ℝ × ℂ`, which the Rouché integrand does
-- not have — its denominator vanishes inside the disc.  Only the values along the circle enter the
-- integral, so the hypothesis is weakened to joint continuity of `(u, θ) ↦ F u (circleMap c R θ)`.
/-- **The count moves continuously.**  A circle integral of a family that is jointly continuous
along the circle is continuous in the parameter, which ranges over an arbitrary topological
space. -/
theorem continuous_circleIntegral_param {X : Type*} [TopologicalSpace X] {c : ℂ} {R : ℝ}
    (F : X → ℂ → ℂ) (hF : Continuous fun p : X × ℝ => F p.1 (circleMap c R p.2)) :
    Continuous fun u : X => ∮ z in C(c, R), F u z := by
  simp only [circleIntegral]
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  have h1 : Continuous fun p : X × ℝ => deriv (circleMap c R) p.2 := by
    simp only [deriv_circleMap]
    exact ((continuous_circleMap 0 R).comp continuous_snd).mul continuous_const
  exact h1.smul hF

/-! ### The counting integral -/

/-- A multiset of simple poles, each weighted by `z^k`, is circle-integrable when none of the poles
lies on the circle. -/
theorem circleIntegrable_multiset_sum_pow_div_sub {c : ℂ} {R : ℝ} (k : ℕ) (s : Multiset ℂ)
    (hs : ∀ r ∈ s, r ∉ sphere c |R|) :
    CircleIntegrable (fun z => (s.map fun r => z ^ k / (z - r)).sum) c R := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons w s ih =>
    have h1 : CircleIntegrable (fun z => z ^ k / (z - w)) c R :=
      circleIntegrable_pow_div_sub (hs w (Multiset.mem_cons_self w s)) k
    have h2 := ih fun r hr => hs r (Multiset.mem_cons_of_mem hr)
    have h3 : CircleIntegrable
        (fun z => z ^ k / (z - w) + (s.map fun r => z ^ k / (z - r)).sum) c R := h1.add h2
    simpa only [Multiset.map_cons, Multiset.sum_cons] using h3

/-- The sum of the simple poles is circle-integrable whenever none of them sits on the circle.
This is the unweighted case of `circleIntegrable_multiset_sum_pow_div_sub`. -/
theorem circleIntegrable_multiset_sum_sub_inv {c : ℂ} {R : ℝ} (s : Multiset ℂ)
    (hs : ∀ r ∈ s, r ∉ sphere c |R|) :
    CircleIntegrable (fun z => (s.map fun r => (z - r)⁻¹).sum) c R := by
  simpa using circleIntegrable_multiset_sum_pow_div_sub 0 s hs

/-- **The `z^k`-weighted residue sum.**  For a multiset of points none of which lies on the circle,
`∮ ∑_{r ∈ s} z^k/(z - r) dz = 2πi · ∑_{r ∈ s, |r - c| < R} r^k`, both counts taken with
multiplicity. -/
theorem circleIntegral_multiset_sum_pow_div_sub {c : ℂ} {R : ℝ} (hR : 0 < R) (k : ℕ)
    (s : Multiset ℂ) (hs : ∀ r ∈ s, r ∉ sphere c R) :
    (∮ z in C(c, R), (s.map fun r => z ^ k / (z - r)).sum)
      = 2 * Real.pi * I * (((s.filter fun r => dist r c < R).map fun r => r ^ k).sum) := by
  have habs : |R| = R := abs_of_pos hR
  induction s using Multiset.induction_on with
  | empty => simp [circleIntegral]
  | cons w s ih =>
    have hw : w ∉ sphere c R := hs w (Multiset.mem_cons_self w s)
    have hrest : ∀ r ∈ s, r ∉ sphere c R := fun r hr => hs r (Multiset.mem_cons_of_mem hr)
    have h1 : CircleIntegrable (fun z => z ^ k / (z - w)) c R :=
      circleIntegrable_pow_div_sub (by rwa [habs]) k
    have h2 : CircleIntegrable (fun z => (s.map fun r => z ^ k / (z - r)).sum) c R :=
      circleIntegrable_multiset_sum_pow_div_sub k s (by rwa [habs])
    simp only [Multiset.map_cons, Multiset.sum_cons]
    rw [circleIntegral.integral_add h1 h2, ih hrest]
    by_cases hb : dist w c < R
    · rw [circleIntegral_pow_div_sub_of_mem_ball (mem_ball.mpr hb),
        Multiset.filter_cons_of_pos (p := fun r => dist r c < R) s hb, Multiset.map_cons,
        Multiset.sum_cons]
      ring
    · have hlt : R < dist w c := by
        rcases lt_trichotomy (dist w c) R with h | h | h
        · exact absurd h hb
        · exact absurd (mem_sphere.mpr h) hw
        · exact h
      rw [circleIntegral_pow_div_sub_of_lt hR.le hlt,
        Multiset.filter_cons_of_neg (p := fun r => dist r c < R) s hb, zero_add]

/-- **Each simple pole inside contributes `2πi`, each one outside contributes nothing.**  For a
multiset of points none of which lies on the circle,
`∮ ∑_{r ∈ s} (z - r)⁻¹ = 2πi · #{r ∈ s : |r - c| < R}`, the count taken with multiplicity.  This is
the unweighted case of `circleIntegral_multiset_sum_pow_div_sub`. -/
theorem circleIntegral_multiset_sum_sub_inv {c : ℂ} {R : ℝ} (hR : 0 < R) (s : Multiset ℂ)
    (hs : ∀ r ∈ s, r ∉ sphere c R) :
    (∮ z in C(c, R), (s.map fun r => (z - r)⁻¹).sum)
      = ((s.filter fun r => dist r c < R).card : ℂ) * (2 * Real.pi * I) := by
  simpa [Multiset.map_const', Multiset.sum_replicate, mul_comm] using
    circleIntegral_multiset_sum_pow_div_sub hR 0 s hs


/-! ### The root count -/

/-- The roots of `P` in the open disc `ball c R`, with multiplicity.  The predicate is written
`dist r c < R` rather than `r ∈ ball c R` — the two are definitionally the same — so that
`Multiset.filter` takes the order-theoretic `Decidable` instance on `ℝ`. -/
noncomputable def rootsIn (P : Polynomial ℂ) (c : ℂ) (R : ℝ) : Multiset ℂ :=
  P.roots.filter fun r => dist r c < R

theorem mem_rootsIn {P : Polynomial ℂ} {c : ℂ} {R : ℝ} {r : ℂ} :
    r ∈ rootsIn P c R ↔ r ∈ P.roots ∧ r ∈ ball c R := by
  simp [rootsIn, Multiset.mem_filter, mem_ball]

/-- `rootsIn` in the membership form, for a caller who has a `Decidable` instance for the
disc — a classical one will do. -/
theorem rootsIn_eq_filter_mem_ball (P : Polynomial ℂ) (c : ℂ) (R : ℝ)
    [DecidablePred fun r : ℂ => r ∈ ball c R] :
    rootsIn P c R = P.roots.filter fun r => r ∈ ball c R :=
  Multiset.filter_congr fun r _ => by simp [mem_ball]

/-- **The argument principle for polynomials.**  For `P ≠ 0` with no root on the circle
`|z - c| = R`,
\[
  \oint_{|z-c|=R}\frac{P'}{P} = 2\pi i \cdot \#\{\text{roots of } P \text{ in } |z-c|<R\},
\]
the count taken with multiplicity. -/
theorem circleIntegral_logDeriv_polynomial {P : Polynomial ℂ} (hP : P ≠ 0) {c : ℂ} {R : ℝ}
    (hR : 0 < R) (hns : ∀ r ∈ P.roots, r ∉ sphere c R) :
    (∮ z in C(c, R), (derivative P).eval z / P.eval z)
      = ((rootsIn P c R).card : ℂ) * (2 * Real.pi * I) := by
  have hcong : Set.EqOn (fun z => (derivative P).eval z / P.eval z)
      (fun z => (P.roots.map fun r => (z - r)⁻¹).sum) (sphere c R) := by
    intro z hz
    have hz0 : P.eval z ≠ 0 := fun h0 => hns z (mem_roots'.mpr ⟨hP, h0⟩) hz
    simpa only [one_div] using
      (IsAlgClosed.splits P).eval_derivative_div_eval_of_ne_zero hz0
  rw [circleIntegral.integral_congr hR.le hcong]
  exact circleIntegral_multiset_sum_sub_inv hR P.roots hns

/-! ### The Rouché family -/

/-- `t` retracted onto `[0,1]`: the identity there, constant outside.  The Rouché family is run
through this so that its logarithmic derivative is jointly continuous along the circle for every
real `t`, not merely for `t` in the interval. -/
noncomputable def clamp01 (t : ℝ) : ℝ := max 0 (min 1 t)

theorem clamp01_mem (t : ℝ) : clamp01 t ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩

theorem continuous_clamp01 : Continuous clamp01 :=
  continuous_const.max (continuous_const.min continuous_id)

@[simp] theorem clamp01_zero : clamp01 0 = 0 := by norm_num [clamp01]

@[simp] theorem clamp01_one : clamp01 1 = 1 := by norm_num [clamp01]

/-- **A count read off the deformation `f + t·g` cannot jump.**  If `f`, `g` and the numerators
`f'`, `g'` are continuous on the circle, `‖g‖ < ‖f‖` there, and the contour integral of
`(f' + t·g') / (f + t·g)` is `2πi · N t` at every `t`, then `N 0 = N 1`.

Steps (b) and (c) of the classical Rouché argument, with the parameter run through `clamp01` so
that the family is zero-free on the circle for *every* real `t` — which is what the continuity
statement has to quantify over.  The numerators are left free rather than written as derivatives,
so that a caller holding `Polynomial.derivative` need not first rewrite it as a `deriv`. -/
theorem int_eq_of_circleIntegral_deform {c : ℂ} {R : ℝ} (hR : 0 ≤ R) {f g f' g' : ℂ → ℂ}
    (hcf : ContinuousOn f (sphere c R)) (hcg : ContinuousOn g (sphere c R))
    (hcf' : ContinuousOn f' (sphere c R)) (hcg' : ContinuousOn g' (sphere c R))
    (hlt : ∀ z ∈ sphere c R, ‖g z‖ < ‖f z‖) {N : ℝ → ℤ}
    (hcount : ∀ t : ℝ, (∮ z in C(c, R),
        (f' z + ((clamp01 t : ℝ) : ℂ) * g' z) / (f z + ((clamp01 t : ℝ) : ℂ) * g z))
      = (N t : ℂ) * (2 * Real.pi * I)) :
    N 0 = N 1 := by
  have habs : |R| = R := abs_of_nonneg hR
  have hmaps : ∀ p : ℝ × ℝ, circleMap c R p.2 ∈ sphere c R := fun p =>
    circleMap_mem_sphere c hR p.2
  have hcs : ∀ u : ℂ → ℂ, ContinuousOn u (sphere c R) →
      Continuous fun p : ℝ × ℝ => u (circleMap c R p.2) := fun _ hu =>
    hu.comp_continuous ((continuous_circleMap c R).comp continuous_snd) hmaps
  have hcl : Continuous fun p : ℝ × ℝ => ((clamp01 p.1 : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (continuous_clamp01.comp continuous_fst)
  have hI := continuous_circleIntegral_param
    (c := c) (R := R)
    (fun t z => (f' z + ((clamp01 t : ℝ) : ℂ) * g' z) / (f z + ((clamp01 t : ℝ) : ℂ) * g z))
    (Continuous.div ((hcs _ hcf').add (hcl.mul (hcs _ hcg')))
      ((hcs _ hcf).add (hcl.mul (hcs _ hcg))) fun p =>
      add_smul_ne_zero_of_norm_lt f g (by rwa [habs]) (clamp01_mem p.1)
        (by rw [habs]; exact hmaps p))
  exact int_eq_of_continuous_mul_two_pi_I (by simpa only [hcount] using hI)


/-- The Rouché family `P + t·Q`, run at the clamped parameter. -/
noncomputable def rouchePoly (P Q : Polynomial ℂ) (t : ℝ) : Polynomial ℂ :=
  P + C ((clamp01 t : ℝ) : ℂ) * Q

theorem eval_rouchePoly (P Q : Polynomial ℂ) (t : ℝ) (z : ℂ) :
    (rouchePoly P Q t).eval z = P.eval z + ((clamp01 t : ℝ) : ℂ) * Q.eval z := by
  simp [rouchePoly]

theorem derivative_eval_rouchePoly (P Q : Polynomial ℂ) (t : ℝ) (z : ℂ) :
    (derivative (rouchePoly P Q t)).eval z
      = (derivative P).eval z + ((clamp01 t : ℝ) : ℂ) * (derivative Q).eval z := by
  simp [rouchePoly, derivative_add]

@[simp] theorem rouchePoly_zero (P Q : Polynomial ℂ) : rouchePoly P Q 0 = P := by
  simp [rouchePoly]

@[simp] theorem rouchePoly_one (P Q : Polynomial ℂ) : rouchePoly P Q 1 = P + Q := by
  simp [rouchePoly]

/-! ### Rouché -/

/-- **Rouché's theorem for polynomials.**  If `‖Q‖ < ‖P‖` on the circle `|z - c| = R`, then `P`
and `P + Q` have the same number of roots in the open disc, counted with multiplicity.

Unconditional: the counting hypothesis the sibling development left open is discharged by
`circleIntegral_logDeriv_polynomial` at each `t`, and the resulting integer count moves
continuously in `t` by `continuous_circleIntegral_param`. -/
theorem card_rootsIn_add_eq {P Q : Polynomial ℂ} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hlt : ∀ z ∈ sphere c R, ‖Q.eval z‖ < ‖P.eval z‖) :
    (rootsIn P c R).card = (rootsIn (P + Q) c R).card := by
  have habs : |R| = R := abs_of_pos hR
  -- The family stays zero-free on the circle, so every member has a root count to read off.
  have hne : ∀ (t : ℝ), ∀ z ∈ sphere c R, (rouchePoly P Q t).eval z ≠ 0 := by
    intro t z hz
    rw [eval_rouchePoly]
    exact add_smul_ne_zero_of_norm_lt (fun z => P.eval z) (fun z => Q.eval z)
      (by rwa [habs]) (clamp01_mem t) (by rwa [habs])
  have hsph : (c + (R : ℂ)) ∈ sphere c R := by simp [hR.le]
  have hP0 : ∀ t : ℝ, rouchePoly P Q t ≠ 0 := fun t h0 => hne t _ hsph (by rw [h0]; simp)
  have hns : ∀ (t : ℝ), ∀ r ∈ (rouchePoly P Q t).roots, r ∉ sphere c R := fun t r hr hmem =>
    hne t r hmem (mem_roots'.mp hr).2
  -- Each count is an integer read off the contour integral, which the argument principle supplies.
  set N : ℝ → ℤ := fun t => ((rootsIn (rouchePoly P Q t) c R).card : ℤ) with hNdef
  have hcount : ∀ t : ℝ,
      (∮ z in C(c, R), ((derivative P).eval z + ((clamp01 t : ℝ) : ℂ) * (derivative Q).eval z)
          / (P.eval z + ((clamp01 t : ℝ) : ℂ) * Q.eval z))
        = (N t : ℂ) * (2 * Real.pi * I) := by
    intro t
    have hz : ∀ z : ℂ, ((derivative P).eval z + ((clamp01 t : ℝ) : ℂ) * (derivative Q).eval z)
        / (P.eval z + ((clamp01 t : ℝ) : ℂ) * Q.eval z)
        = (derivative (rouchePoly P Q t)).eval z / (rouchePoly P Q t).eval z := fun z => by
      rw [derivative_eval_rouchePoly, eval_rouchePoly]
    simp only [hz]
    rw [circleIntegral_logDeriv_polynomial (hP0 t) hR (hns t), hNdef]
    norm_cast
  have hfin := int_eq_of_circleIntegral_deform hR.le P.continuous.continuousOn
    Q.continuous.continuousOn (derivative P).continuous.continuousOn
    (derivative Q).continuous.continuousOn hlt hcount
  rw [hNdef] at hfin
  simpa using hfin

/-- **The localization form.**  A polynomial all of whose roots lie in the disc keeps its full
root count there under a perturbation smaller on the boundary.

Monicity is not needed.  All that is used is that every one of the `natDegree P` roots lies in
the disc, which is the hypothesis `hroots`. -/
theorem card_rootsIn_add_eq_natDegree {P Q : Polynomial ℂ} {M : ℝ} (hM : 0 < M)
    (hroots : ∀ r ∈ P.roots, r ∈ ball (0 : ℂ) M)
    (hlt : ∀ z ∈ sphere (0 : ℂ) M, ‖Q.eval z‖ < ‖P.eval z‖) :
    (rootsIn (P + Q) 0 M).card = P.natDegree := by
  have hfil : rootsIn P 0 M = P.roots :=
    Multiset.filter_eq_self.mpr fun r hr => by
      simpa [dist_zero_right] using mem_ball.mp (hroots r hr)
  rw [← card_rootsIn_add_eq hM hlt, hfil, (IsAlgClosed.splits P).natDegree_eq_card_roots]

/-- **Hurwitz, in the form the zero-transfer corollary consumes.**  If `P n → P₀` uniformly on a
circle carrying no zero of `P₀`, then eventually `P n` has exactly `P₀`'s number of zeros inside,
counted with multiplicity. -/
theorem eventually_card_rootsIn_eq {c : ℂ} {R : ℝ} (hR : 0 < R) {P : ℕ → Polynomial ℂ}
    {P₀ : Polynomial ℂ}
    (hunif : TendstoUniformlyOn (fun n z => (P n).eval z) (fun z => P₀.eval z) Filter.atTop
      (sphere c R))
    (hns : ∀ z ∈ sphere c R, P₀.eval z ≠ 0) :
    ∀ᶠ n in Filter.atTop, (rootsIn (P n) c R).card = (rootsIn P₀ c R).card := by
  filter_upwards [eventually_norm_sub_lt_of_tendstoUniformlyOn (isCompact_sphere c R)
    P₀.continuous.continuousOn hns hunif] with n hn
  have hlt : ∀ z ∈ sphere c R, ‖(P n - P₀).eval z‖ < ‖P₀.eval z‖ := fun z hz => by
    rw [eval_sub]; exact hn z hz
  have h := card_rootsIn_add_eq hR hlt
  rw [show P₀ + (P n - P₀) = P n by ring] at h
  exact h.symm


/-! ### Axiom footprint -/

/-- info: 'Shields.card_rootsIn_add_eq_natDegree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms card_rootsIn_add_eq_natDegree

/-- info: 'Shields.eventually_card_rootsIn_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms eventually_card_rootsIn_eq

end Shields
