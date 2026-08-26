/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities
import Shields.Analysis.Complex.ArgumentPrinciple.Polynomial
import Shields.Analysis.Complex.ArgumentPrinciple.Analytic

/-!
# Weierstrass preparation in one variable

On a disc where `f` has exactly `r` zeros, `f = W * U` with `W` monic of degree `r` whose roots are
those zeros and `U` zero-free -- with `W`'s coefficients depending continuously, and analytically,
on a parameter.

## Main results

* `Shields.exists_preparation`, `Shields.exists_monic_preparation`: the factorization for a
  polynomial `f`.
* `Shields.exists_analytic_preparation`: the factorization for an analytic `f`.
* `Shields.exists_continuous_analytic_preparation`,
  `Shields.exists_differentiableOn_analytic_preparation`: with parameter dependence.
* `Shields.circleIntegral_pow_mul_logDeriv_polynomial`: the power sums of the roots inside a disc as
  contour integrals.

## Implementation notes

Preparation here is the argument principle plus Newton's identities, in four steps: the power sums
of the zeros in the disc are contour integrals of `z ^ k * f' / f`; Newton's identities
(`Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities`) turn those into the elementary
symmetric functions; `W` is assembled from them; and `U := f / W` is zero-free because `W`'s roots
are exactly `f`'s there.

Parameter regularity is inherited through the integral: `wedgeIntegral_circleIntegral` swaps the
order of integration so that Morera applies to the parametrized contour integral.

**This is not the Mathlib result of the same name.**
`Mathlib.RingTheory.PowerSeries.WeierstrassPreparation` (#24584) is preparation for formal power
series over a complete local ring. This is the analytic one-variable theorem with parameters, which
is absent upstream.

## Tags

Weierstrass preparation, argument principle, Newton's identities, analytic function
-/

namespace Shields

open Complex Metric Polynomial

/-! ### Cauchy's formula for a monomial numerator

Two contour integrals.  A simple pole inside the circle contributes `2πi·a^k` to the integral of
`z^k/(z - a)`; a pole outside contributes nothing.  At `k = 0` these are Cauchy's integral formula
and Cauchy's theorem, and `Rouche.circleIntegral_sub_inv_of_lt` is the second of them. -/

/-- `z^k/(z - a)` is circle-integrable whenever the pole misses the circle. -/
theorem circleIntegrable_pow_div_sub {c a : ℂ} {R : ℝ} (hR : 0 ≤ R) (ha : a ∉ sphere c R) (k : ℕ) :
    CircleIntegrable (fun z => z ^ k / (z - a)) c R := by
  refine ContinuousOn.circleIntegrable hR ?_
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

/-! ### The weighted counting integral -/

/-- A multiset of simple poles, each weighted by `z^k`, is circle-integrable when none of the poles
lies on the circle. -/
theorem circleIntegrable_multiset_sum_pow_div_sub {c : ℂ} {R : ℝ} (hR : 0 ≤ R) (k : ℕ)
    (s : Multiset ℂ) (hs : ∀ r ∈ s, r ∉ sphere c R) :
    CircleIntegrable (fun z => (s.map fun r => z ^ k / (z - r)).sum) c R := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons w s ih =>
    have h1 : CircleIntegrable (fun z => z ^ k / (z - w)) c R :=
      circleIntegrable_pow_div_sub hR (hs w (Multiset.mem_cons_self w s)) k
    have h2 := ih fun r hr => hs r (Multiset.mem_cons_of_mem hr)
    have h3 : CircleIntegrable
        (fun z => z ^ k / (z - w) + (s.map fun r => z ^ k / (z - r)).sum) c R := h1.add h2
    simpa only [Multiset.map_cons, Multiset.sum_cons] using h3

/-- **The `z^k`-weighted residue sum.**  For a multiset of points none of which lies on the circle,
`∮ ∑_{r ∈ s} z^k/(z - r) dz = 2πi · ∑_{r ∈ s, |r - c| < R} r^k`, both counts taken with
multiplicity. -/
theorem circleIntegral_multiset_sum_pow_div_sub {c : ℂ} {R : ℝ} (hR : 0 < R) (k : ℕ)
    (s : Multiset ℂ) (hs : ∀ r ∈ s, r ∉ sphere c R) :
    (∮ z in C(c, R), (s.map fun r => z ^ k / (z - r)).sum)
      = 2 * Real.pi * I * (((s.filter fun r => dist r c < R).map fun r => r ^ k).sum) := by
  induction s using Multiset.induction_on with
  | empty => simp [circleIntegral]
  | cons w s ih =>
    have hw : w ∉ sphere c R := hs w (Multiset.mem_cons_self w s)
    have hrest : ∀ r ∈ s, r ∉ sphere c R := fun r hr => hs r (Multiset.mem_cons_of_mem hr)
    have h1 : CircleIntegrable (fun z => z ^ k / (z - w)) c R :=
      circleIntegrable_pow_div_sub hR.le hw k
    have h2 : CircleIntegrable (fun z => (s.map fun r => z ^ k / (z - r)).sum) c R :=
      circleIntegrable_multiset_sum_pow_div_sub hR.le k s hrest
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

/-! ### Power sums of the roots inside the disc -/

/-- The `k`-th power sum of a multiset of complex numbers. -/
noncomputable def powerSum (s : Multiset ℂ) (k : ℕ) : ℂ := (s.map fun r => r ^ k).sum

@[simp] theorem powerSum_zero (s : Multiset ℂ) : powerSum s 0 = (s.card : ℂ) := by
  simp [powerSum]

/-- **Power sums of a packet as contour integrals.**  For `P ≠ 0` with no root on the circle
`|z - c| = R`,
\[
  \oint_{|z-c|=R} z^k\,\frac{P'(z)}{P(z)}\,dz
  = 2\pi i\sum_{\substack{P(\rho)=0\\|\rho-c|<R}}\rho^k ,
\]
the sum taken with multiplicity.  At `k = 0` this is the argument principle
`circleIntegral_logDeriv_polynomial`; the general `k` is step 1 of the preparation. -/
theorem circleIntegral_pow_mul_logDeriv_polynomial {P : Polynomial ℂ} (hP : P ≠ 0) {c : ℂ} {R : ℝ}
    (hR : 0 < R) (hns : ∀ r ∈ P.roots, r ∉ sphere c R) (k : ℕ) :
    (∮ z in C(c, R), z ^ k * ((derivative P).eval z / P.eval z))
      = 2 * Real.pi * I * powerSum (rootsIn P c R) k := by
  have hcong : Set.EqOn (fun z => z ^ k * ((derivative P).eval z / P.eval z))
      (fun z => (P.roots.map fun r => z ^ k / (z - r)).sum) (sphere c R) := by
    intro z hz
    have hz0 : P.eval z ≠ 0 := fun h0 => hns z (mem_roots'.mpr ⟨hP, h0⟩) hz
    have hlog : (derivative P).eval z / P.eval z = (P.roots.map fun r => (z - r)⁻¹).sum := by
      simpa only [one_div] using
        (IsAlgClosed.splits P).eval_derivative_div_eval_of_ne_zero hz0
    simp only [hlog, ← Multiset.sum_map_mul_left]
    simp [div_eq_mul_inv]
  rw [circleIntegral.integral_congr hR.le hcong]
  exact circleIntegral_multiset_sum_pow_div_sub hR k P.roots hns

/-! ### Newton's identities for a multiset

Mathlib proves Newton's identities for the universal symmetric polynomials in `MvPolynomial σ R`.
A multiset of `r` complex numbers is the image of `Finset.univ` under a function `Fin r → ℂ`, so
`MvPolynomial.aeval` transports the identity to the concrete form step 2 uses. -/

/-- `aeval` sends the universal power sum to the power sum of the evaluated family. -/
theorem aeval_psum_eq_powerSum {σ : Type*} [Fintype σ] (f : σ → ℂ) (k : ℕ) :
    MvPolynomial.aeval f (MvPolynomial.psum σ ℂ k)
      = powerSum (Multiset.map f Finset.univ.val) k := by
  have h1 : MvPolynomial.aeval f (MvPolynomial.psum σ ℂ k) = ∑ i, f i ^ k := by
    simp only [MvPolynomial.psum, map_sum, map_pow, MvPolynomial.aeval_X]
  rw [h1, powerSum, Multiset.map_map, Finset.sum_eq_multiset_sum, Function.comp_def]

/-- Every multiset of complex numbers is the image of `Finset.univ` under a family indexed by a
finite type. -/
theorem exists_fintype_map_univ (s : Multiset ℂ) :
    ∃ (n : ℕ) (f : Fin n → ℂ), Multiset.map f Finset.univ.val = s :=
  ⟨s.toList.length, s.toList.get, by rw [Fin.univ_val_map, List.ofFn_get, Multiset.coe_toList]⟩

/-- **Newton's identities** for a multiset of complex numbers: for every `k`,
`k·e_k = (-1)^{k+1} ∑_{i+j=k, i<k} (-1)^i e_i p_j`.  This is step 2 of the preparation — it
recovers the elementary symmetric functions of a packet from its power sums, which
`circleIntegral_pow_mul_logDeriv_polynomial` presents as contour integrals. -/
theorem mul_esymm_eq_sum_powerSum (s : Multiset ℂ) (k : ℕ) :
    (k : ℂ) * s.esymm k = (-1) ^ (k + 1) *
      ∑ a ∈ Finset.antidiagonal k with a.1 < k, (-1) ^ a.1 * s.esymm a.1 * powerSum s a.2 := by
  obtain ⟨n, f, hf⟩ := exists_fintype_map_univ s
  have h := congrArg (MvPolynomial.aeval f) (MvPolynomial.mul_esymm_eq_sum (Fin n) ℂ k)
  simp only [map_mul, map_sum, map_pow, map_neg, map_one, map_natCast,
    MvPolynomial.aeval_esymm_eq_multiset_esymm, aeval_psum_eq_powerSum, hf] at h
  exact h

/-! ### The polynomial preparation theorem -/

/-- The monic factor of `P` carrying exactly the roots in the open disc `ball c R`, with
multiplicity.  This is the monic factor `W` of the preparation, for a polynomial family. -/
noncomputable def insideFactor (P : Polynomial ℂ) (c : ℂ) (R : ℝ) : Polynomial ℂ :=
  ((rootsIn P c R).map fun r => X - C r).prod

theorem monic_insideFactor (P : Polynomial ℂ) (c : ℂ) (R : ℝ) : (insideFactor P c R).Monic :=
  monic_multisetProd_X_sub_C _

theorem natDegree_insideFactor (P : Polynomial ℂ) (c : ℂ) (R : ℝ) :
    (insideFactor P c R).natDegree = (rootsIn P c R).card :=
  natDegree_multiset_prod_X_sub_C_eq_card _

theorem roots_insideFactor (P : Polynomial ℂ) (c : ℂ) (R : ℝ) :
    (insideFactor P c R).roots = rootsIn P c R :=
  roots_multiset_prod_X_sub_C _

theorem insideFactor_ne_zero (P : Polynomial ℂ) (c : ℂ) (R : ℝ) : insideFactor P c R ≠ 0 :=
  (monic_insideFactor P c R).ne_zero

theorem insideFactor_dvd {P : Polynomial ℂ} (hP : P ≠ 0) (c : ℂ) (R : ℝ) :
    insideFactor P c R ∣ P :=
  (Multiset.prod_X_sub_C_dvd_iff_le_roots hP _).mpr (Multiset.filter_le _ _)

/-- **Vieta for the inside factor.**  The non-leading coefficients of `W` are, up to sign, the
elementary symmetric functions of the roots inside the disc. -/
theorem coeff_insideFactor (P : Polynomial ℂ) (c : ℂ) (R : ℝ) {k : ℕ}
    (hk : k ≤ (rootsIn P c R).card) :
    (insideFactor P c R).coeff k
      = (-1) ^ ((rootsIn P c R).card - k) * (rootsIn P c R).esymm ((rootsIn P c R).card - k) :=
  Multiset.prod_X_sub_C_coeff _ hk

/-- **Weierstrass preparation for a polynomial.**  `P` splits as a monic polynomial carrying
exactly its roots in the open disc, times a factor with no root there.  This is
Weierstrass preparation for a polynomial, with `W = insideFactor P c R` and `U = V`. -/
theorem exists_preparation {P : Polynomial ℂ} (hP : P ≠ 0) (c : ℂ) (R : ℝ) :
    ∃ V : Polynomial ℂ, P = insideFactor P c R * V ∧ V ≠ 0 ∧
      ∀ z ∈ ball c R, V.eval z ≠ 0 := by
  obtain ⟨V, hV⟩ := insideFactor_dvd hP c R
  refine ⟨V, hV, ?_, ?_⟩
  · exact fun h0 => hP (by rw [hV, h0, mul_zero])
  · intro z hz hz0
    have hPne : insideFactor P c R * V ≠ 0 := hV ▸ hP
    have hroots : P.roots = rootsIn P c R + V.roots := by
      conv_lhs => rw [hV]
      rw [roots_mul hPne, roots_insideFactor]
    have hsplit : rootsIn P c R + P.roots.filter (fun r => ¬ dist r c < R) = P.roots :=
      Multiset.filter_add_not _ _
    have hVroots : V.roots = P.roots.filter (fun r => ¬ dist r c < R) := by
      refine add_left_cancel (a := rootsIn P c R) ?_
      rw [hsplit, ← hroots]
    have hzV : z ∈ V.roots := mem_roots'.mpr ⟨fun h0 => hP (by rw [hV, h0, mul_zero]), hz0⟩
    rw [hVroots, Multiset.mem_filter] at hzV
    exact hzV.2 (mem_ball.mp hz)

/-- The preparation in packaged form: a monic `W` of
degree the inside root count, whose roots are exactly the roots of `P` inside, together with a
zero-free cofactor. -/
theorem exists_monic_preparation {P : Polynomial ℂ} (hP : P ≠ 0) (c : ℂ) (R : ℝ) :
    ∃ W V : Polynomial ℂ, W.Monic ∧ W.natDegree = (rootsIn P c R).card ∧
      W.roots = rootsIn P c R ∧ P = W * V ∧ ∀ z ∈ ball c R, V.eval z ≠ 0 := by
  obtain ⟨V, hV, _, hVne⟩ := exists_preparation hP c R
  exact ⟨insideFactor P c R, V, monic_insideFactor P c R, natDegree_insideFactor P c R,
    roots_insideFactor P c R, hV, hVne⟩

/-! ### Dependence on a parameter

The contour representation is what makes the inside factor inherit the family's regularity: the
power sums are integrals of a jointly continuous integrand, hence continuous, and Newton's
identities are a polynomial recursion, so the elementary symmetric functions follow. -/

/-- A circle integral of a family jointly continuous along the circle is continuous in the
parameter.  `Rouche.continuous_circleIntegral_param` is the case of a real parameter. -/
theorem continuous_circleIntegral_param' {X : Type*} [TopologicalSpace X] {c : ℂ} {R : ℝ}
    (F : X → ℂ → ℂ) (hF : Continuous fun p : X × ℝ => F p.1 (circleMap c R p.2)) :
    Continuous fun u : X => ∮ z in C(c, R), F u z := by
  simp only [circleIntegral]
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  have h1 : Continuous fun p : X × ℝ => deriv (circleMap c R) p.2 := by
    simp only [deriv_circleMap]
    exact ((continuous_circleMap 0 R).comp continuous_snd).mul continuous_const
  exact h1.smul hF

section Parametric

variable {X : Type*} [TopologicalSpace X]

/-- A family with no zero on the circle is nonzero. -/
theorem ne_zero_of_ne_zero_on_sphere {P : Polynomial ℂ} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hns : ∀ z ∈ sphere c R, P.eval z ≠ 0) : P ≠ 0 := by
  have hsph : (c + (R : ℂ)) ∈ sphere c R := by
    rw [mem_sphere, dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hR]
  exact fun h0 => hns _ hsph (by rw [h0]; simp)

/-- **The power sums move continuously.**  For a polynomial family whose evaluation and
derivative-evaluation are jointly continuous in the parameter and the point, and which has no zero
on the circle, every power sum of the roots inside the disc is continuous in the parameter. -/
theorem continuous_powerSum_rootsIn {c : ℂ} {R : ℝ} (hR : 0 < R) {P : X → Polynomial ℂ}
    (hev : Continuous fun p : X × ℂ => (P p.1).eval p.2)
    (hev' : Continuous fun p : X × ℂ => (derivative (P p.1)).eval p.2)
    (hns : ∀ u, ∀ z ∈ sphere c R, (P u).eval z ≠ 0) (k : ℕ) :
    Continuous fun u : X => powerSum (rootsIn (P u) c R) k := by
  have hcirc : Continuous fun p : X × ℝ => ((p.1, circleMap c R p.2) : X × ℂ) :=
    continuous_fst.prodMk ((continuous_circleMap c R).comp continuous_snd)
  have hjoint : Continuous fun p : X × ℝ => (circleMap c R p.2) ^ k *
      ((derivative (P p.1)).eval (circleMap c R p.2) / (P p.1).eval (circleMap c R p.2)) := by
    refine (((continuous_circleMap c R).comp continuous_snd).pow k).mul ?_
    refine (hev'.comp hcirc).div (hev.comp hcirc) ?_
    intro p
    exact hns p.1 _ (circleMap_mem_sphere c hR.le p.2)
  have hI : Continuous fun u : X =>
      ∮ z in C(c, R), z ^ k * ((derivative (P u)).eval z / (P u).eval z) :=
    continuous_circleIntegral_param' _ hjoint
  have hrepr : ∀ u : X, powerSum (rootsIn (P u) c R) k
      = (2 * (Real.pi : ℂ) * I)⁻¹ *
        ∮ z in C(c, R), z ^ k * ((derivative (P u)).eval z / (P u).eval z) := by
    intro u
    have hP : P u ≠ 0 := ne_zero_of_ne_zero_on_sphere hR (hns u)
    have hroots : ∀ r ∈ (P u).roots, r ∉ sphere c R := fun r hr hmem =>
      hns u r hmem (mem_roots'.mp hr).2
    rw [circleIntegral_pow_mul_logDeriv_polynomial hP hR hroots k,
      inv_mul_cancel_left₀ two_pi_I_ne_zero]
  simp only [hrepr]
  exact continuous_const.mul hI

/-- **Newton's identities carry regularity from the power sums to the `e_k`.**  For a family of
multisets whose power sums are all continuous in the parameter, every elementary symmetric function
is continuous, by strong induction on `k`. -/
theorem continuous_esymm_of_continuous_powerSum (S : X → Multiset ℂ)
    (hp : ∀ j, Continuous fun u => powerSum (S u) j) (k : ℕ) :
    Continuous fun u : X => (S u).esymm k := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    match k with
    | 0 => simpa [Multiset.esymm] using continuous_const (y := (1 : ℂ))
    | (m + 1) =>
      have hm : ((m + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero m)
      have key : ∀ u : X, (S u).esymm (m + 1)
          = ((m + 1 : ℕ) : ℂ)⁻¹ * ((-1) ^ (m + 2) *
              ∑ a ∈ Finset.antidiagonal (m + 1) with a.1 < m + 1,
                (-1) ^ a.1 * (S u).esymm a.1 * powerSum (S u) a.2) := by
        intro u
        rw [← mul_esymm_eq_sum_powerSum, inv_mul_cancel_left₀ hm]
      simp only [key]
      refine continuous_const.mul (continuous_const.mul ?_)
      refine continuous_finsetSum _ fun a ha => ?_
      have hlt : a.1 < m + 1 := (Finset.mem_filter.mp ha).2
      exact (continuous_const.mul (ih a.1 hlt)).mul (hp a.2)

/-- **The elementary symmetric functions move continuously.** -/
theorem continuous_esymm_rootsIn {c : ℂ} {R : ℝ} (hR : 0 < R) {P : X → Polynomial ℂ}
    (hev : Continuous fun p : X × ℂ => (P p.1).eval p.2)
    (hev' : Continuous fun p : X × ℂ => (derivative (P p.1)).eval p.2)
    (hns : ∀ u, ∀ z ∈ sphere c R, (P u).eval z ≠ 0) (k : ℕ) :
    Continuous fun u : X => (rootsIn (P u) c R).esymm k :=
  continuous_esymm_of_continuous_powerSum _
    (fun j => continuous_powerSum_rootsIn hR hev hev' hns j) k

/-- **The inside factor moves continuously.**  For a family with a stable root count in the disc,
every coefficient of the monic inside factor is continuous in the parameter.  This is the
parametric half of the preparation, for a polynomial family. -/
theorem continuous_coeff_insideFactor {c : ℂ} {R : ℝ} (hR : 0 < R) {P : X → Polynomial ℂ} {r : ℕ}
    (hev : Continuous fun p : X × ℂ => (P p.1).eval p.2)
    (hev' : Continuous fun p : X × ℂ => (derivative (P p.1)).eval p.2)
    (hns : ∀ u, ∀ z ∈ sphere c R, (P u).eval z ≠ 0)
    (hcard : ∀ u, (rootsIn (P u) c R).card = r) (k : ℕ) :
    Continuous fun u : X => (insideFactor (P u) c R).coeff k := by
  by_cases hk : k ≤ r
  · have key : ∀ u : X, (insideFactor (P u) c R).coeff k
        = (-1) ^ (r - k) * (rootsIn (P u) c R).esymm (r - k) := by
      intro u
      rw [coeff_insideFactor (P u) c R (by rw [hcard u]; exact hk), hcard u]
    simp only [key]
    exact continuous_const.mul (continuous_esymm_rootsIn hR hev hev' hns (r - k))
  · have key : ∀ u : X, (insideFactor (P u) c R).coeff k = 0 := by
      intro u
      refine coeff_eq_zero_of_natDegree_lt ?_
      rw [natDegree_insideFactor, hcard u]
      exact not_le.mp hk
    simp only [key]
    exact continuous_const

end Parametric

/-! ### Holomorphic dependence on a parameter

Morera and Fubini in place of differentiation under the integral sign.  A circle integral of a
family holomorphic in the parameter is continuous in the parameter by
`continuous_circleIntegral_param'`, and its wedge integral over any rectangle in the domain is
antisymmetric because the two integrations commute and each slice of the contour is itself a
holomorphic function of the parameter.  Morera then upgrades the pair to holomorphy. -/

/-- Fubini for a pair of interval integrals with jointly continuous integrand. -/
theorem intervalIntegral_swap_of_continuous {a b c d : ℝ} (H : ℝ → ℝ → ℂ)
    (hH : Continuous fun p : ℝ × ℝ => H p.1 p.2) :
    (∫ x in a..b, ∫ y in c..d, H x y) = ∫ y in c..d, ∫ x in a..b, H x y := by
  refine MeasureTheory.intervalIntegral_intervalIntegral_swap ?_
  have hcpt : IsCompact (Set.uIcc a b ×ˢ Set.uIcc c d) := isCompact_uIcc.prod isCompact_uIcc
  have hint : MeasureTheory.IntegrableOn (Function.uncurry H) (Set.uIcc a b ×ˢ Set.uIcc c d) :=
    (hH.continuousOn).integrableOn_compact hcpt
  exact hint.mono_set (Set.prod_mono Set.Ioc_subset_Icc_self Set.Ioc_subset_Icc_self)

/-- The circle integral commutes with the wedge integral of the parameter: the wedge integral of
`u ↦ ∮ F u` is the contour integral of the wedge integrals of the individual slices. -/
theorem wedgeIntegral_circleIntegral {c : ℂ} {R : ℝ} (F : ℂ → ℂ → ℂ) (z w : ℂ)
    (hF : Continuous fun p : ℂ × ℝ => F p.1 (circleMap c R p.2)) :
    wedgeIntegral z w (fun v => ∮ ζ in C(c, R), F v ζ)
      = ∫ θ in (0 : ℝ)..(2 * Real.pi),
          wedgeIntegral z w fun v => deriv (circleMap c R) θ • F v (circleMap c R θ) := by
  have hK : Continuous fun q : ℝ × ℂ =>
      deriv (circleMap c R) q.1 • F q.2 (circleMap c R q.1) := by
    have h1 : Continuous fun q : ℝ × ℂ => deriv (circleMap c R) q.1 := by
      simp only [deriv_circleMap]
      exact ((continuous_circleMap 0 R).comp continuous_fst).mul continuous_const
    exact h1.smul (hF.comp (continuous_snd.prodMk continuous_fst))
  have hslice : ∀ g : ℝ → ℂ, Continuous g → Continuous fun p : ℝ × ℝ =>
      deriv (circleMap c R) p.2 • F (g p.1) (circleMap c R p.2) := fun _ hg =>
    hK.comp (continuous_snd.prodMk (hg.comp continuous_fst))
  have hg1 : Continuous fun x : ℝ => (x : ℂ) + (z.im : ℂ) * I :=
    (Complex.continuous_ofReal.add continuous_const)
  have hg2 : Continuous fun y : ℝ => (w.re : ℂ) + (y : ℂ) * I :=
    continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
  have hA : Continuous fun θ : ℝ => ∫ x in z.re..w.re,
      deriv (circleMap c R) θ • F ((x : ℂ) + (z.im : ℂ) * I) (circleMap c R θ) := by
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    exact (hslice _ hg1).comp (continuous_snd.prodMk continuous_fst)
  have hB : Continuous fun θ : ℝ => ∫ y in z.im..w.im,
      deriv (circleMap c R) θ • F ((w.re : ℂ) + (y : ℂ) * I) (circleMap c R θ) := by
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    exact (hslice _ hg2).comp (continuous_snd.prodMk continuous_fst)
  have hswap1 : (∫ x in z.re..w.re, ∫ θ in (0 : ℝ)..(2 * Real.pi),
        deriv (circleMap c R) θ • F ((x : ℂ) + (z.im : ℂ) * I) (circleMap c R θ))
      = ∫ θ in (0 : ℝ)..(2 * Real.pi), ∫ x in z.re..w.re,
        deriv (circleMap c R) θ • F ((x : ℂ) + (z.im : ℂ) * I) (circleMap c R θ) :=
    intervalIntegral_swap_of_continuous _ (hslice _ hg1)
  have hswap2 : (∫ y in z.im..w.im, ∫ θ in (0 : ℝ)..(2 * Real.pi),
        deriv (circleMap c R) θ • F ((w.re : ℂ) + (y : ℂ) * I) (circleMap c R θ))
      = ∫ θ in (0 : ℝ)..(2 * Real.pi), ∫ y in z.im..w.im,
        deriv (circleMap c R) θ • F ((w.re : ℂ) + (y : ℂ) * I) (circleMap c R θ) :=
    intervalIntegral_swap_of_continuous _ (hslice _ hg2)
  simp only [wedgeIntegral, circleIntegral]
  have hB' : Continuous fun θ : ℝ => I • ∫ y in z.im..w.im,
      deriv (circleMap c R) θ • F ((w.re : ℂ) + (y : ℂ) * I) (circleMap c R θ) := hB.const_smul I
  rw [hswap1, hswap2, ← intervalIntegral.integral_smul,
    ← intervalIntegral.integral_add (hA.intervalIntegrable 0 (2 * Real.pi))
      (hB'.intervalIntegrable 0 (2 * Real.pi))]

/-- **Holomorphy of a circle integral in its parameter.**  If the integrand is jointly continuous
along the contour and, for each point of the contour, holomorphic in the parameter on an open set
`U`, then the contour integral is holomorphic on `U`. -/
theorem differentiableOn_circleIntegral_param {U : Set ℂ} (hU : IsOpen U) {c : ℂ} {R : ℝ}
    (F : ℂ → ℂ → ℂ) (hF : Continuous fun p : ℂ × ℝ => F p.1 (circleMap c R p.2))
    (hhol : ∀ θ : ℝ, DifferentiableOn ℂ (fun u => F u (circleMap c R θ)) U) :
    DifferentiableOn ℂ (fun u => ∮ ζ in C(c, R), F u ζ) U := by
  refine (isConservativeOn_and_continuousOn_iff_isDifferentiableOn hU).mp
    ⟨?_, (continuous_circleIntegral_param' F hF).continuousOn⟩
  intro z w hzw
  have hcons : ∀ θ : ℝ,
      IsConservativeOn (fun v => deriv (circleMap c R) θ • F v (circleMap c R θ)) U := fun θ =>
    ((hhol θ).const_smul (deriv (circleMap c R) θ)).isConservativeOn
  calc wedgeIntegral z w (fun v => ∮ ζ in C(c, R), F v ζ)
      = ∫ θ in (0 : ℝ)..(2 * Real.pi),
          wedgeIntegral z w fun v => deriv (circleMap c R) θ • F v (circleMap c R θ) :=
        wedgeIntegral_circleIntegral F z w hF
    _ = ∫ θ in (0 : ℝ)..(2 * Real.pi),
          -wedgeIntegral w z fun v => deriv (circleMap c R) θ • F v (circleMap c R θ) :=
        intervalIntegral.integral_congr fun θ _ => hcons θ z w hzw
    _ = -∫ θ in (0 : ℝ)..(2 * Real.pi),
          wedgeIntegral w z fun v => deriv (circleMap c R) θ • F v (circleMap c R θ) :=
        intervalIntegral.integral_neg
    _ = -wedgeIntegral w z (fun v => ∮ ζ in C(c, R), F v ζ) := by
        rw [wedgeIntegral_circleIntegral F w z hF]

/-- **The power sums are holomorphic in the parameter.**  Same hypotheses as
`continuous_powerSum_rootsIn`, with holomorphy of the family in the parameter added. -/
theorem differentiableOn_powerSum_rootsIn {U : Set ℂ} (hU : IsOpen U) {c : ℂ} {R : ℝ} (hR : 0 < R)
    {P : ℂ → Polynomial ℂ}
    (hev : Continuous fun p : ℂ × ℂ => (P p.1).eval p.2)
    (hev' : Continuous fun p : ℂ × ℂ => (derivative (P p.1)).eval p.2)
    (hns : ∀ u, ∀ z ∈ sphere c R, (P u).eval z ≠ 0)
    (hhol : ∀ z : ℂ, DifferentiableOn ℂ (fun u => (P u).eval z) U)
    (hhol' : ∀ z : ℂ, DifferentiableOn ℂ (fun u => (derivative (P u)).eval z) U) (k : ℕ) :
    DifferentiableOn ℂ (fun u => powerSum (rootsIn (P u) c R) k) U := by
  have hcirc : Continuous fun p : ℂ × ℝ => ((p.1, circleMap c R p.2) : ℂ × ℂ) :=
    continuous_fst.prodMk ((continuous_circleMap c R).comp continuous_snd)
  have hjoint : Continuous fun p : ℂ × ℝ => (circleMap c R p.2) ^ k *
      ((derivative (P p.1)).eval (circleMap c R p.2) / (P p.1).eval (circleMap c R p.2)) := by
    refine (((continuous_circleMap c R).comp continuous_snd).pow k).mul ?_
    refine (hev'.comp hcirc).div (hev.comp hcirc) ?_
    intro p
    exact hns p.1 _ (circleMap_mem_sphere c hR.le p.2)
  have hD : DifferentiableOn ℂ
      (fun u => ∮ z in C(c, R), z ^ k * ((derivative (P u)).eval z / (P u).eval z)) U := by
    refine differentiableOn_circleIntegral_param hU _ hjoint fun θ => ?_
    refine DifferentiableOn.const_mul ?_ _
    exact (hhol' _).div (hhol _) fun u _ =>
      hns u _ (circleMap_mem_sphere c hR.le θ)
  have hrepr : ∀ u : ℂ, powerSum (rootsIn (P u) c R) k
      = (2 * (Real.pi : ℂ) * I)⁻¹ *
        ∮ z in C(c, R), z ^ k * ((derivative (P u)).eval z / (P u).eval z) := by
    intro u
    have hP : P u ≠ 0 := ne_zero_of_ne_zero_on_sphere hR (hns u)
    have hroots : ∀ r ∈ (P u).roots, r ∉ sphere c R := fun r hr hmem =>
      hns u r hmem (mem_roots'.mp hr).2
    rw [circleIntegral_pow_mul_logDeriv_polynomial hP hR hroots k,
      inv_mul_cancel_left₀ two_pi_I_ne_zero]
  simpa only [hrepr] using hD.const_mul (2 * (Real.pi : ℂ) * I)⁻¹

/-- The holomorphic counterpart of `continuous_esymm_of_continuous_powerSum`. -/
theorem differentiableOn_esymm_of_differentiableOn_powerSum {U : Set ℂ} (S : ℂ → Multiset ℂ)
    (hp : ∀ j, DifferentiableOn ℂ (fun u => powerSum (S u) j) U) (k : ℕ) :
    DifferentiableOn ℂ (fun u => (S u).esymm k) U := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    match k with
    | 0 =>
      simp [Multiset.esymm]
    | (m + 1) =>
      have hm : ((m + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero m)
      have key : ∀ u : ℂ, (S u).esymm (m + 1)
          = ((m + 1 : ℕ) : ℂ)⁻¹ * ((-1) ^ (m + 2) *
              ∑ a ∈ Finset.antidiagonal (m + 1) with a.1 < m + 1,
                (-1) ^ a.1 * (S u).esymm a.1 * powerSum (S u) a.2) := by
        intro u
        rw [← mul_esymm_eq_sum_powerSum, inv_mul_cancel_left₀ hm]
      simp only [key]
      refine DifferentiableOn.const_mul (DifferentiableOn.const_mul ?_ _) _
      refine DifferentiableOn.fun_sum fun a ha => ?_
      have hlt : a.1 < m + 1 := (Finset.mem_filter.mp ha).2
      exact (DifferentiableOn.const_mul (ih a.1 hlt) _).mul (hp a.2)

/-- **The elementary symmetric functions are holomorphic in the parameter.** -/
theorem differentiableOn_esymm_rootsIn {U : Set ℂ} (hU : IsOpen U) {c : ℂ} {R : ℝ} (hR : 0 < R)
    {P : ℂ → Polynomial ℂ}
    (hev : Continuous fun p : ℂ × ℂ => (P p.1).eval p.2)
    (hev' : Continuous fun p : ℂ × ℂ => (derivative (P p.1)).eval p.2)
    (hns : ∀ u, ∀ z ∈ sphere c R, (P u).eval z ≠ 0)
    (hhol : ∀ z : ℂ, DifferentiableOn ℂ (fun u => (P u).eval z) U)
    (hhol' : ∀ z : ℂ, DifferentiableOn ℂ (fun u => (derivative (P u)).eval z) U) (k : ℕ) :
    DifferentiableOn ℂ (fun u => (rootsIn (P u) c R).esymm k) U :=
  differentiableOn_esymm_of_differentiableOn_powerSum _
    (fun j => differentiableOn_powerSum_rootsIn hU hR hev hev' hns hhol hhol' j) k

/-- **The inside factor is holomorphic in the parameter.**  For a family with a stable root count
in the disc, every coefficient of the monic inside factor is holomorphic on `U`.  This is the
parametric half of the preparation, for one complex parameter. -/
theorem differentiableOn_coeff_insideFactor {U : Set ℂ} (hU : IsOpen U) {c : ℂ} {R : ℝ} (hR : 0 < R)
    {P : ℂ → Polynomial ℂ} {r : ℕ}
    (hev : Continuous fun p : ℂ × ℂ => (P p.1).eval p.2)
    (hev' : Continuous fun p : ℂ × ℂ => (derivative (P p.1)).eval p.2)
    (hns : ∀ u, ∀ z ∈ sphere c R, (P u).eval z ≠ 0)
    (hhol : ∀ z : ℂ, DifferentiableOn ℂ (fun u => (P u).eval z) U)
    (hhol' : ∀ z : ℂ, DifferentiableOn ℂ (fun u => (derivative (P u)).eval z) U)
    (hcard : ∀ u, (rootsIn (P u) c R).card = r) (k : ℕ) :
    DifferentiableOn ℂ (fun u => (insideFactor (P u) c R).coeff k) U := by
  by_cases hk : k ≤ r
  · have key : ∀ u : ℂ, (insideFactor (P u) c R).coeff k
        = (-1) ^ (r - k) * (rootsIn (P u) c R).esymm (r - k) := by
      intro u
      rw [coeff_insideFactor (P u) c R (by rw [hcard u]; exact hk), hcard u]
    simp only [key]
    exact DifferentiableOn.const_mul
      (differentiableOn_esymm_rootsIn hU hR hev hev' hns hhol hhol' (r - k)) _
  · have key : ∀ u : ℂ, (insideFactor (P u) c R).coeff k = 0 := by
      intro u
      refine coeff_eq_zero_of_natDegree_lt ?_
      rw [natDegree_insideFactor, hcard u]
      exact not_le.mp hk
    simp only [key]
    exact differentiableOn_const 0

/-! ### The analytic case

`RoucheAnalytic.exists_zeroFactor` factors an analytic function with no zero on the circle as
`∏_{u ∈ s} (z - u)` times an analytic function with no zero on the closed disc.  That factorization
is what step 1 consumes: the logarithmic derivative splits into the simple poles at `s` and a term
holomorphic on the disc, and the second integrates to zero by Cauchy's theorem.  The polynomial
proof of `circleIntegral_pow_mul_logDeriv_polynomial` used the splitting of `P`; this is the same
argument with the factorization in its place. -/

/-- The monic polynomial with root multiset `s` evaluates to `RoucheAnalytic.zeroFactor s`. -/
theorem eval_multisetProd_X_sub_C (s : Multiset ℂ) (z : ℂ) :
    ((s.map fun u => X - C u).prod).eval z = zeroFactor s z := by
  simp [zeroFactor, Polynomial.eval_multiset_prod, Multiset.map_map]

/-- **Power sums of an analytic packet as contour integrals.**  Given a factorization
`f = (∏_{u ∈ s} (· - u)) · g` with `g` analytic and zero-free on the closed disc and `s` inside the
open disc, the `z^k`-weighted logarithmic-derivative integral is `2πi` times the `k`-th power sum of
`s`.  At `k = 0` this is `RoucheAnalytic.circleIntegral_logDeriv`. -/
theorem circleIntegral_pow_mul_logDeriv_of_zeroFactor {f g : ℂ → ℂ} {c : ℂ} {R : ℝ}
    {s : Multiset ℂ} (hR : 0 < R) (hsmem : ∀ u ∈ s, u ∈ ball c R)
    (hg : AnalyticOnNhd ℂ g (closedBall c R)) (hgne : ∀ z ∈ closedBall c R, g z ≠ 0)
    (hfac : ∀ z, f z = zeroFactor s z * g z) (k : ℕ) :
    (∮ z in C(c, R), z ^ k * (deriv f z / f z)) = 2 * Real.pi * I * powerSum s k := by
  have hfeq : f = fun z => zeroFactor s z * g z := funext hfac
  have hnotsph : ∀ r ∈ s, r ∉ sphere c R := by
    intro r hr hmem
    exact absurd (mem_sphere.mp hmem) (ne_of_lt (mem_ball.mp (hsmem r hr)))
  have hsphne : ∀ z ∈ sphere c R, ∀ u ∈ s, z ≠ u := fun z hz u hu hzu =>
    hnotsph u hu (hzu ▸ hz)
  have hcong : Set.EqOn (fun z => z ^ k * (deriv f z / f z))
      (fun z => (s.map fun u => z ^ k / (z - u)).sum + z ^ k * (deriv g z / g z))
      (sphere c R) := by
    intro z hz
    have hzc : z ∈ closedBall c R := sphere_subset_closedBall hz
    have hdg : DifferentiableAt ℂ g z := (hg z hzc).differentiableAt
    have hsplit := logDeriv_mul (f := zeroFactor s) (g := g) z
      (zeroFactor_ne_zero (hsphne z hz)) (hgne z hzc) ((differentiable_zeroFactor s) z) hdg
    rw [logDeriv_zeroFactor (hsphne z hz)] at hsplit
    have hlog : deriv f z / f z = (s.map fun u => (z - u)⁻¹).sum + deriv g z / g z := by
      change logDeriv f z = _
      rw [hfeq, hsplit, logDeriv_apply]
    simp only [hlog, mul_add, ← Multiset.sum_map_mul_left]
    simp [div_eq_mul_inv]
  rw [circleIntegral.integral_congr hR.le hcong]
  have h1 : CircleIntegrable (fun z => (s.map fun u => z ^ k / (z - u)).sum) c R :=
    circleIntegrable_multiset_sum_pow_div_sub hR.le k s hnotsph
  have h2 : CircleIntegrable (fun z => z ^ k * (deriv g z / g z)) c R := by
    refine ContinuousOn.circleIntegrable hR.le ?_
    refine (continuous_pow k).continuousOn.mul (ContinuousOn.div ?_ ?_ ?_)
    · exact (hg.deriv.continuousOn).mono sphere_subset_closedBall
    · exact hg.continuousOn.mono sphere_subset_closedBall
    · exact fun z hz => hgne z (sphere_subset_closedBall hz)
  have hcauchy : (∮ z in C(c, R), z ^ k * (deriv g z / g z)) = 0 := by
    refine Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable hR.le
      Set.countable_empty ?_ ?_
    · exact (continuous_pow k).continuousOn.mul
        (ContinuousOn.div hg.deriv.continuousOn hg.continuousOn fun z hz => hgne z hz)
    · intro z hz
      have hzc : z ∈ closedBall c R := ball_subset_closedBall hz.1
      exact ((differentiable_pow k) z).mul
        (((hg.deriv z hzc).differentiableAt).div ((hg z hzc).differentiableAt) (hgne z hzc))
  rw [circleIntegral.integral_add h1 h2, hcauchy, add_zero,
    circleIntegral_multiset_sum_pow_div_sub hR k s hnotsph,
    Multiset.filter_eq_self.mpr fun r hr => mem_ball.mp (hsmem r hr)]
  rfl

/-- **Weierstrass preparation on a disc, analytic case.**  An analytic function with no zero on the
circle is a monic polynomial `W` times an analytic function with no zero on the closed disc; `W` has
degree the zero count, its roots are exactly the zeros of `f` in the open disc with multiplicity,
and the power sums of those roots are the contour integrals of step 1.  This is
Weierstrass preparation at a single parameter value. -/
theorem exists_analytic_preparation {f : ℂ → ℂ} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (closedBall c R)) (hns : ∀ z ∈ sphere c R, f z ≠ 0) :
    ∃ (W : Polynomial ℂ) (g : ℂ → ℂ), W.Monic ∧ W.natDegree = zeroCount f c R ∧
      (∀ u ∈ W.roots, u ∈ ball c R) ∧ AnalyticOnNhd ℂ g (closedBall c R) ∧
      (∀ z ∈ closedBall c R, g z ≠ 0) ∧ (∀ z, f z = W.eval z * g z) ∧
      ∀ k : ℕ, (∮ z in C(c, R), z ^ k * (deriv f z / f z))
        = 2 * Real.pi * I * powerSum W.roots k := by
  obtain ⟨s, g, hsmem, hg, hgne, hfac⟩ := exists_zeroFactor hR hf hns
  have hroots : ((s.map fun u => X - C u).prod).roots = s := roots_multiset_prod_X_sub_C s
  refine ⟨(s.map fun u => X - C u).prod, g, monic_multisetProd_X_sub_C _, ?_, ?_, hg, hgne, ?_, ?_⟩
  · rw [natDegree_multiset_prod_X_sub_C_eq_card, zeroCount_eq_card hsmem hg hgne hfac]
  · rw [hroots]; exact hsmem
  · intro z; rw [eval_multisetProd_X_sub_C]; exact hfac z
  · intro k
    rw [hroots]
    exact circleIntegral_pow_mul_logDeriv_of_zeroFactor hR hsmem hg hgne hfac k

/-! ### The analytic case with a parameter

The three analytic ingredients now compose.  `exists_analytic_preparation` produces, at each
parameter value, a monic `W` whose power sums are the contour integrals; those integrals are
continuous (resp. holomorphic) in the parameter by the results above; and Newton's identities plus
Vieta turn that into continuity (resp. holomorphy) of the coefficients of `W`.  The hypothesis
`hcard` — a constant zero count — is Rouché's conclusion, available from
`Shields.zeroCount_add_eq`, and is what pins the degree of `W`. -/

/-- Vieta for a monic polynomial of known degree. -/
theorem coeff_eq_esymm_roots_of_monic {W : Polynomial ℂ} (hW : W.Monic) {r k : ℕ}
    (hdeg : W.natDegree = r) (hk : k ≤ r) :
    W.coeff k = (-1) ^ (r - k) * W.roots.esymm (r - k) := by
  rw [Polynomial.coeff_eq_esymm_roots_of_splits (IsAlgClosed.splits W) (by rw [hdeg]; exact hk),
    hW.leadingCoeff, one_mul, hdeg]

/-- **Weierstrass preparation with a continuous parameter, analytic case.**  A family of analytic
functions with no zero on the circle and a constant zero count inside it factors as a monic
polynomial of that degree times a zero-free analytic function, with the coefficients of the
polynomial continuous in the parameter.  This is Weierstrass preparation with a one-dimensional
continuous parameter. -/
theorem exists_continuous_analytic_preparation {X : Type*} [TopologicalSpace X] {c : ℂ} {R : ℝ}
    (hR : 0 < R) {f : X → ℂ → ℂ} {r : ℕ}
    (hf : ∀ u, AnalyticOnNhd ℂ (f u) (closedBall c R))
    (hns : ∀ u, ∀ z ∈ sphere c R, f u z ≠ 0)
    (hlog : Continuous fun p : X × ℝ =>
      deriv (f p.1) (circleMap c R p.2) / f p.1 (circleMap c R p.2))
    (hcard : ∀ u, zeroCount (f u) c R = r) :
    ∃ W : X → Polynomial ℂ, (∀ u, (W u).Monic) ∧ (∀ u, (W u).natDegree = r) ∧
      (∀ u, ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g (closedBall c R) ∧
        (∀ z ∈ closedBall c R, g z ≠ 0) ∧ ∀ z, f u z = (W u).eval z * g z) ∧
      ∀ k : ℕ, Continuous fun u => (W u).coeff k := by
  choose W g hmon hdeg hWmem hgan hgne hfac hps using
    fun u => exists_analytic_preparation hR (hf u) (hns u)
  have hdeg' : ∀ u, (W u).natDegree = r := fun u => (hdeg u).trans (hcard u)
  have hpow : ∀ j, Continuous fun u : X => powerSum (W u).roots j := by
    intro j
    have hI : Continuous fun u : X => ∮ z in C(c, R), z ^ j * (deriv (f u) z / f u z) :=
      continuous_circleIntegral_param' _
        ((((continuous_circleMap c R).comp continuous_snd).pow j).mul hlog)
    have hrepr : ∀ u : X, powerSum (W u).roots j
        = (2 * (Real.pi : ℂ) * I)⁻¹ * ∮ z in C(c, R), z ^ j * (deriv (f u) z / f u z) := by
      intro u
      rw [hps u j, inv_mul_cancel_left₀ two_pi_I_ne_zero]
    simp only [hrepr]
    exact continuous_const.mul hI
  refine ⟨W, hmon, hdeg', fun u => ⟨g u, hgan u, hgne u, hfac u⟩, fun k => ?_⟩
  by_cases hk : k ≤ r
  · have hco : ∀ u : X, (W u).coeff k = (-1) ^ (r - k) * (W u).roots.esymm (r - k) :=
      fun u => coeff_eq_esymm_roots_of_monic (hmon u) (hdeg' u) hk
    simp only [hco]
    exact continuous_const.mul (continuous_esymm_of_continuous_powerSum _ hpow (r - k))
  · have hco : ∀ u : X, (W u).coeff k = 0 := fun u =>
      Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hdeg' u]; omega)
    simp only [hco]
    exact continuous_const

/-- **Weierstrass preparation with a holomorphic parameter, analytic case.**  The holomorphic
counterpart of `exists_continuous_analytic_preparation`: on an open set of parameters over which the
logarithmic derivative is holomorphic along the contour, the coefficients of `W` are holomorphic.
The parameter is one-dimensional here; the several-parameter case is not proved. -/
theorem exists_differentiableOn_analytic_preparation {U : Set ℂ} (hU : IsOpen U) {c : ℂ} {R : ℝ}
    (hR : 0 < R) {f : ℂ → ℂ → ℂ} {r : ℕ}
    (hf : ∀ u, AnalyticOnNhd ℂ (f u) (closedBall c R))
    (hns : ∀ u, ∀ z ∈ sphere c R, f u z ≠ 0)
    (hlogc : Continuous fun p : ℂ × ℝ =>
      deriv (f p.1) (circleMap c R p.2) / f p.1 (circleMap c R p.2))
    (hlogh : ∀ θ : ℝ, DifferentiableOn ℂ
      (fun u => deriv (f u) (circleMap c R θ) / f u (circleMap c R θ)) U)
    (hcard : ∀ u, zeroCount (f u) c R = r) :
    ∃ W : ℂ → Polynomial ℂ, (∀ u, (W u).Monic) ∧ (∀ u, (W u).natDegree = r) ∧
      (∀ u, ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g (closedBall c R) ∧
        (∀ z ∈ closedBall c R, g z ≠ 0) ∧ ∀ z, f u z = (W u).eval z * g z) ∧
      ∀ k : ℕ, DifferentiableOn ℂ (fun u => (W u).coeff k) U := by
  choose W g hmon hdeg hWmem hgan hgne hfac hps using
    fun u => exists_analytic_preparation hR (hf u) (hns u)
  have hdeg' : ∀ u, (W u).natDegree = r := fun u => (hdeg u).trans (hcard u)
  have hpow : ∀ j, DifferentiableOn ℂ (fun u => powerSum (W u).roots j) U := by
    intro j
    have hI : DifferentiableOn ℂ
        (fun u => ∮ z in C(c, R), z ^ j * (deriv (f u) z / f u z)) U := by
      refine differentiableOn_circleIntegral_param hU _
        ((((continuous_circleMap c R).comp continuous_snd).pow j).mul hlogc) fun θ => ?_
      exact ((hlogh θ).const_mul _)
    have hrepr : ∀ u : ℂ, powerSum (W u).roots j
        = (2 * (Real.pi : ℂ) * I)⁻¹ * ∮ z in C(c, R), z ^ j * (deriv (f u) z / f u z) := by
      intro u
      rw [hps u j, inv_mul_cancel_left₀ two_pi_I_ne_zero]
    simp only [hrepr]
    exact hI.const_mul _
  refine ⟨W, hmon, hdeg', fun u => ⟨g u, hgan u, hgne u, hfac u⟩, fun k => ?_⟩
  by_cases hk : k ≤ r
  · have hco : ∀ u : ℂ, (W u).coeff k = (-1) ^ (r - k) * (W u).roots.esymm (r - k) :=
      fun u => coeff_eq_esymm_roots_of_monic (hmon u) (hdeg' u) hk
    simp only [hco]
    exact (differentiableOn_esymm_of_differentiableOn_powerSum _ hpow (r - k)).const_mul _
  · have hco : ∀ u : ℂ, (W u).coeff k = 0 := fun u =>
      Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hdeg' u]; omega)
    simp only [hco]
    exact differentiableOn_const 0

/-! ### Coalescence at the base point

The normalized form asks for more than preparation: it asks that the non-leading coefficients of `W`
vanish at the base parameter value, i.e. that `W(x, 0) = x^r`.  That is exactly the statement that
every zero of the packet sits at the origin there, and it needs nothing beyond the factorization. -/

/-- A monic complex polynomial whose roots are all `0` is `x^r`. -/
theorem eq_X_pow_of_monic_of_roots_eq_zero {W : Polynomial ℂ} (hW : W.Monic)
    (hr : ∀ u ∈ W.roots, u = 0) : W = X ^ W.natDegree := by
  have hcard : Multiset.card W.roots = W.natDegree :=
    splits_iff_card_roots.1 (IsAlgClosed.splits W)
  have hmap : (W.roots.map fun a => X - C a) = W.roots.map fun _ => (X : Polynomial ℂ) :=
    Multiset.map_congr rfl fun a ha => by rw [hr a ha, C_0, sub_zero]
  conv_lhs => rw [← prod_multiset_X_sub_C_of_monic_of_roots_card_eq hW hcard]
  rw [hmap, Multiset.map_const', Multiset.prod_replicate, hcard]

/-- Every non-leading coefficient of such a `W` vanishes. -/
theorem coeff_eq_zero_of_monic_of_roots_eq_zero {W : Polynomial ℂ} (hW : W.Monic)
    (hr : ∀ u ∈ W.roots, u = 0) {k : ℕ} (hk : k < W.natDegree) : W.coeff k = 0 := by
  rw [eq_X_pow_of_monic_of_roots_eq_zero hW hr, coeff_X_pow]
  exact if_neg hk.ne

/-- **The normalized form.**  If the only zero of `f` in the disc is at the origin, the monic factor
supplied by `exists_analytic_preparation` is `x^r`.  Together with
`coeff_eq_zero_of_monic_of_roots_eq_zero` this is the vanishing of the non-leading coefficients at
the base parameter value. -/
theorem eq_X_pow_of_preparation {f g : ℂ → ℂ} {W : Polynomial ℂ} {c : ℂ} {R : ℝ} (hW : W.Monic)
    (hWmem : ∀ u ∈ W.roots, u ∈ ball c R) (hfac : ∀ z, f z = W.eval z * g z)
    (h0 : ∀ z ∈ ball c R, f z = 0 → z = 0) : W = X ^ W.natDegree := by
  refine eq_X_pow_of_monic_of_roots_eq_zero hW fun u hu => h0 u (hWmem u hu) ?_
  have hroot : W.eval u = 0 := isRoot_of_mem_roots hu
  rw [hfac u, hroot, zero_mul]

end Shields
