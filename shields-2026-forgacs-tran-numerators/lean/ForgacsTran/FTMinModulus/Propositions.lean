/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib
import ForgacsTran.Geometry
import ForgacsTran.FTBranchPencil
import ForgacsTran.FTBranchProp1
import ForgacsTran.FTBranchEndpoint
import ForgacsTran.FTBranchLimitPoint
import ForgacsTran.Cluster

/-!
# Forgács--Tran Propositions 1 and 2, and the image of the branch value

The minimum-modulus half of `Forgacs2017RationalDenominator`: on the circle
`|t| = s` the modulus of a polynomial with positive real zeros is minimized at
the positive real point, and the first positive critical point of `-P(s)/s^r` is
where the branch value `z` stops being monotone.  Together these give the interval
`(a,b)` of `eq:ab-def` as the image of the viewing arc under `z`.

## Main statements

* `norm_eval_posRootPoly_le_of_norm_eq`, `norm_eval_posRootPoly_lt_of_norm_eq` —
  the magnitude comparison `Forgacs2017RationalDenominator` Prop. 1 opens with,
  its Eq. (28); strict at every non-real point of the circle.
* `ftCritical_eval_neg`, `strictMonoOn_negDivPow`, `negDivPow_lt_of_mem_Ioo` —
  below the first positive critical point `-P(s)/s^r` is strictly increasing.
* `norm_zeta_eq_norm_div`, `one_lt_norm_zeta_iff` — Prop. 2 is Prop. 1 in the
  normalized variable `ζ = t/τ`, so the two are one statement.
* `eval_div_pow_eq_of_isRoot`, `prod_norm_sub_le_of_norm_le`,
  `norm_sub_le_of_prod_le`, `sin_numerator_nonneg` — steps 1--3 of Prop. 1 and
  the angle bound that closes it.
* `image_Ioo_eq_Ioo_of_tendsto`, `image_Ioo_eq_Ioi_of_tendsto_atTop` — Lemma 6:
  a strictly monotone `z` with the two endpoint limits maps the arc onto `(a,b)`,
  or onto `(a,∞)` where the right limit is infinite.
* `tendsto_branchPoint_of_tendsto_tau`, `tendsto_ftZ_of_tendsto_branchPoint`,
  `tendsto_norm_ftZ_atTop_of_tendsto_zero` — the endpoint limits of `τ` transported
  to endpoint limits of `z`, which is what Lemma 6 consumes.

## References

* `../../shields-2026-forgacs-tran-numerators.tex`, «Spectral geometry, residues,
  and the principal amplitude» — `sec:geometry`, `thm:FT-geometry`, `eq:ab-def`.
* `Forgacs2017RationalDenominator`, Propositions 1 and 2 and Lemma 6.

## Tags

minimum modulus, positive real zeros, critical point, branch value, viewing arc
-/

namespace ForgacsTran

open Polynomial

/-! ### The magnitude comparison of `Forgacs2017RationalDenominator` Eq. (28) -/

/-- On the circle `|t| = s`, every distance to a positive real zero is at least
the distance from the positive real point of the circle. -/
theorem norm_sub_le_of_norm_eq {x s : ℝ} (hx : 0 < x) (hs : 0 < s) {t : ℂ}
    (hnorm : ‖t‖ = s) : ‖((s : ℝ) : ℂ) - ((x : ℝ) : ℂ)‖ ≤ ‖t - ((x : ℝ) : ℂ)‖ := by
  have habs : ‖t‖ = |s| := by rw [hnorm, abs_of_pos hs]
  have hkey := norm_sub_sq_sub x s habs
  have hre : t.re ≤ s := by
    have h1 : t.re ≤ ‖t‖ := Complex.re_le_norm t
    rwa [hnorm] at h1
  nlinarith [norm_nonneg (t - ((x : ℝ) : ℂ)), norm_nonneg (((s : ℝ) : ℂ) - ((x : ℝ) : ℂ)),
    hkey, hx, hre]

/-- **`Forgacs2017RationalDenominator` Prop. 1, the magnitude comparison.**  For a
polynomial whose zeros are positive reals, `|P|` on the circle `|t| = s` is
smallest at the positive real point `t = s`. -/
theorem norm_eval_posRootPoly_le_of_norm_eq (c : ℂ) {xs : Multiset ℝ}
    (hx : ∀ x ∈ xs, 0 < x) {s : ℝ} (hs : 0 < s) {t : ℂ} (hnorm : ‖t‖ = s) :
    ‖(posRootPoly c xs).eval ((s : ℝ) : ℂ)‖ ≤ ‖(posRootPoly c xs).eval t‖ := by
  rw [norm_eval_posRootPoly, norm_eval_posRootPoly]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg c)
  exact multiset_prod_le_prod _ _ xs (fun x _ => norm_nonneg _)
    fun x hxm => norm_sub_le_of_norm_eq (hx x hxm) hs hnorm

/-- The strict form: away from the positive real point the inequality is strict. -/
theorem norm_eval_posRootPoly_lt_of_norm_eq (c : ℂ) {xs : Multiset ℝ} (hxs : xs ≠ 0)
    (hc : c ≠ 0) (hx : ∀ x ∈ xs, 0 < x) {s : ℝ} (hs : 0 < s) {t : ℂ}
    (hnorm : ‖t‖ = s) (hne : t ≠ ((s : ℝ) : ℂ)) :
    ‖(posRootPoly c xs).eval ((s : ℝ) : ℂ)‖ < ‖(posRootPoly c xs).eval t‖ := by
  have habs : ‖t‖ = |s| := by rw [hnorm, abs_of_pos hs]
  have hre : t.re < s := by
    have h1 : t.re ≤ ‖t‖ := Complex.re_le_norm t
    rcases lt_or_eq_of_le (hnorm ▸ h1) with h | h
    · exact h
    · exfalso
      refine hne (Complex.ext (by simpa using h) ?_)
      have hsq : t.re ^ 2 + t.im ^ 2 = s ^ 2 := by
        have h2 : ‖t‖ ^ 2 = t.re ^ 2 + t.im ^ 2 := by
          rw [Complex.sq_norm, Complex.normSq_apply]; ring
        rw [← h2, hnorm]
      have him : t.im ^ 2 = 0 := by rw [h] at hsq; linarith
      simpa using pow_eq_zero_iff (n := 2) (by norm_num) |>.1 him
  rw [norm_eval_posRootPoly, norm_eval_posRootPoly]
  refine mul_lt_mul_of_pos_left ?_ (norm_pos_iff.mpr hc)
  refine multiset_prod_lt_prod _ _ xs hxs (fun x _ => norm_nonneg _) fun x hxm => ?_
  have hkey := norm_sub_sq_sub x s habs
  have hxpos := hx x hxm
  refine lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) ?_
  nlinarith [hkey, hxpos, hre]

/-! ### The first positive critical point -/

/-- **The sign below the first critical point.**  `sP'(s) - rP(s)` is negative on
`(0,T)` whenever it has no zero there and `P(0) > 0`: it starts at `-rP(0) < 0`
and cannot change sign.  This is
`Forgacs2017RationalDenominator` Prop. 1's "the derivative does not vanish on
`(0,t_a)`", and it is the same polynomial as `Geometry.ftCritical`. -/
theorem ftCritical_eval_neg {P : Polynomial ℝ} {r : ℕ} {T : ℝ} (hr : 1 ≤ r)
    (hP0 : 0 < P.eval 0)
    (hno : ∀ s ∈ Set.Ioo (0 : ℝ) T, s * (derivative P).eval s - r * P.eval s ≠ 0) :
    ∀ s ∈ Set.Ioo (0 : ℝ) T, s * (derivative P).eval s - r * P.eval s < 0 := by
  intro s hs
  set f : ℝ → ℝ := fun u => u * (derivative P).eval u - r * P.eval u with hf
  have hfc : Continuous f := by
    simp only [hf]
    exact (continuous_id.mul (Polynomial.continuous _)).sub
      (continuous_const.mul (Polynomial.continuous _))
  have hf0 : f 0 < 0 := by
    simp only [hf, zero_mul, zero_sub, neg_lt_zero]
    have hrpos : (0 : ℝ) < r := by exact_mod_cast hr
    positivity
  by_contra hcon
  push Not at hcon
  have hfs : 0 < f s := lt_of_le_of_ne hcon (Ne.symm (hno s hs))
  obtain ⟨u, hu, hfu⟩ :=
    intermediate_value_Ioo hs.1.le hfc.continuousOn (Set.mem_Ioo.2 ⟨hf0, hfs⟩)
  exact hno u ⟨hu.1, lt_trans hu.2 hs.2⟩ hfu

/-- The derivative of `-P(s)/s^r`. -/
theorem hasDerivAt_negDivPow (P : Polynomial ℝ) {r : ℕ} (hr : 1 ≤ r) {s : ℝ} (hs : s ≠ 0) :
    HasDerivAt (fun u : ℝ => -P.eval u / u ^ r)
      (-(s * (derivative P).eval s - r * P.eval s) / s ^ (r + 1)) s := by
  have hnum : HasDerivAt (fun u : ℝ => -P.eval u) (-(derivative P).eval s) s :=
    (P.hasDerivAt s).neg
  have hden : HasDerivAt (fun u : ℝ => u ^ r) ((r : ℝ) * s ^ (r - 1)) s := hasDerivAt_pow r s
  have h := hnum.div hden (pow_ne_zero r hs)
  have hA : s ^ r = s * s ^ (r - 1) := (mul_pow_sub_one (by omega) s).symm
  have hB : s ^ (r + 1) = s ^ 2 * s ^ (r - 1) := by
    rw [show r - 1 = r + 1 - 2 by omega]
    exact (pow_mul_pow_sub s (by omega)).symm
  have hval : (-(derivative P).eval s * s ^ r - -P.eval s * ((r : ℝ) * s ^ (r - 1)))
      / (s ^ r) ^ 2 = -(s * (derivative P).eval s - r * P.eval s) / s ^ (r + 1) := by
    rw [div_eq_div_iff (pow_ne_zero 2 (pow_ne_zero r hs)) (pow_ne_zero (r + 1) hs), hA, hB]
    ring
  rwa [hval] at h

/-- **`-P(s)/s^r` is strictly increasing below the first critical point.**  This
is the step `Forgacs2017RationalDenominator` Prop. 1 uses to place a real zero. -/
theorem strictMonoOn_negDivPow {P : Polynomial ℝ} {r : ℕ} (hr : 1 ≤ r) {T : ℝ} (_hT : 0 < T)
    (hneg : ∀ s ∈ Set.Ioo (0 : ℝ) T, s * (derivative P).eval s - r * P.eval s < 0) :
    StrictMonoOn (fun u : ℝ => -P.eval u / u ^ r) (Set.Ioc 0 T) := by
  refine strictMonoOn_of_deriv_pos (convex_Ioc 0 T) ?_ ?_
  · refine ContinuousOn.div (Polynomial.continuous _).continuousOn.neg
      ((continuous_pow r).continuousOn) fun u hu => pow_ne_zero _ (ne_of_gt hu.1)
  · intro u hu
    rw [interior_Ioc] at hu
    rw [(hasDerivAt_negDivPow P hr (ne_of_gt hu.1)).deriv]
    have h := hneg u hu
    have hpow : (0 : ℝ) < u ^ (r + 1) := pow_pos hu.1 _
    exact div_pos (by linarith) hpow

/-- The consequence: below the first critical point the fiber value stays under
its value there, so a parameter above it has no preimage in `(0,T)`. -/
theorem negDivPow_lt_of_mem_Ioo {P : Polynomial ℝ} {r : ℕ} (hr : 1 ≤ r) {T : ℝ} (hT : 0 < T)
    (hneg : ∀ s ∈ Set.Ioo (0 : ℝ) T, s * (derivative P).eval s - r * P.eval s < 0)
    {s : ℝ} (hs : s ∈ Set.Ioo (0 : ℝ) T) :
    -P.eval s / s ^ r < -P.eval T / T ^ r :=
  strictMonoOn_negDivPow hr hT hneg ⟨hs.1, hs.2.le⟩ ⟨hT, le_refl T⟩ hs.2

/-! ### `Forgacs2017RationalDenominator` Prop. 2 is Prop. 1 renormalized -/

/-- **`Forgacs2017RationalDenominator` Prop. 2.**  With `t₀` of modulus `τ` and
`ζ_k = (t_k/t₀)e^{-iθ}`, the modulus `|ζ_k|` is `|t_k|/τ`.  So "all `ζ_k` lie
outside the closed unit disk" and "all `t_k` lie outside the closed disk of
radius `τ`" are the same statement, which is why their proof records the two
propositions as equivalent. -/
theorem norm_zeta_eq_norm_div {τ θ : ℝ} (hτ : 0 < τ) (tk : ℂ) :
    ‖tk / (((τ : ℝ) : ℂ) * Complex.exp (((θ : ℝ) : ℂ) * Complex.I))
        * Complex.exp (-((θ : ℝ) : ℂ) * Complex.I)‖ = ‖tk‖ / τ := by
  have hexp : ‖Complex.exp (((θ : ℝ) : ℂ) * Complex.I)‖ = 1 :=
    Complex.norm_exp_ofReal_mul_I θ
  have hexp' : ‖Complex.exp (-((θ : ℝ) : ℂ) * Complex.I)‖ = 1 := by
    rw [show -((θ : ℝ) : ℂ) = (((-θ : ℝ)) : ℂ) by push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I (-θ)
  rw [norm_mul, hexp', mul_one, norm_div, norm_mul, hexp, mul_one, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hτ]

/-- The equivalence in the form the two propositions are used: outside the unit
circle for `ζ_k` is outside the circle of radius `τ` for `t_k`. -/
theorem one_lt_norm_zeta_iff {τ θ : ℝ} (hτ : 0 < τ) (tk : ℂ) :
    1 < ‖tk / (((τ : ℝ) : ℂ) * Complex.exp (((θ : ℝ) : ℂ) * Complex.I))
        * Complex.exp (-((θ : ℝ) : ℂ) * Complex.I)‖ ↔ τ < ‖tk‖ := by
  rw [norm_zeta_eq_norm_div hτ, lt_div_iff₀ hτ, one_mul]


/-! ### `Forgacs2017RationalDenominator` Prop. 1, steps 1--3 -/

/-- **`Forgacs2017RationalDenominator` Eq. (28).**  Two nonzero zeros of the same
pencil have the same value of `P(t)/t^r`, both being `-z`. -/
theorem eval_div_pow_eq_of_isRoot {P : Polynomial ℂ} {r : ℕ} {z t w : ℂ}
    (ht : t ≠ 0) (hw : w ≠ 0) (hrt : (ftDen P r z).eval t = 0)
    (hrw : (ftDen P r z).eval w = 0) :
    P.eval t / t ^ r = P.eval w / w ^ r := by
  rw [ftDen_eval] at hrt hrw
  rw [div_eq_div_iff (pow_ne_zero r ht) (pow_ne_zero r hw)]
  have h1 : P.eval t = -(z * t ^ r) := by linear_combination hrt
  have h2 : P.eval w = -(z * w ^ r) := by linear_combination hrw
  rw [h1, h2]; ring

/-- **The magnitude form of Eq. (28).**  If the zero `t` is no further from the
origin than the zero `w`, its product of distances to the zeros of `P` is no
larger.  This is the "interpreting the numerators as the products of the
distances" of their Prop. 1. -/
theorem prod_norm_sub_le_of_norm_le {c : ℂ} (hc : c ≠ 0) {xs : Multiset ℝ} {r : ℕ}
    {z t w : ℂ} (ht : t ≠ 0) (hw : w ≠ 0) (hnorm : ‖t‖ ≤ ‖w‖)
    (hrt : (ftDen (posRootPoly c xs) r z).eval t = 0)
    (hrw : (ftDen (posRootPoly c xs) r z).eval w = 0) :
    (xs.map (fun x : ℝ => ‖t - ((x : ℝ) : ℂ)‖)).prod
      ≤ (xs.map (fun x : ℝ => ‖w - ((x : ℝ) : ℂ)‖)).prod := by
  have hkey := eval_div_pow_eq_of_isRoot ht hw hrt hrw
  have hnormeq : ‖(posRootPoly c xs).eval t‖ * ‖w‖ ^ r
      = ‖(posRootPoly c xs).eval w‖ * ‖t‖ ^ r := by
    have h := congrArg (‖·‖) hkey
    simp only [norm_div, norm_pow] at h
    rw [div_eq_div_iff (by positivity) (by positivity)] at h
    exact h
  rw [norm_eval_posRootPoly, norm_eval_posRootPoly] at hnormeq
  have hcpos : (0 : ℝ) < ‖c‖ := norm_pos_iff.mpr hc
  have htpos : (0 : ℝ) < ‖t‖ := norm_pos_iff.mpr ht
  have hwpos : (0 : ℝ) < ‖w‖ := norm_pos_iff.mpr hw
  have hPw : (0 : ℝ) ≤ (xs.map (fun x : ℝ => ‖w - ((x : ℝ) : ℂ)‖)).prod :=
    Multiset.prod_nonneg fun y hy => by
      obtain ⟨x, _, rfl⟩ := Multiset.mem_map.1 hy; exact norm_nonneg _
  have hpow : ‖t‖ ^ r ≤ ‖w‖ ^ r := pow_le_pow_left₀ htpos.le hnorm r
  have h2 : (xs.map (fun x : ℝ => ‖t - ((x : ℝ) : ℂ)‖)).prod * ‖w‖ ^ r
      = (xs.map (fun x : ℝ => ‖w - ((x : ℝ) : ℂ)‖)).prod * ‖t‖ ^ r := by
    rw [mul_assoc, mul_assoc] at hnormeq
    exact mul_left_cancel₀ (ne_of_gt hcpos) hnormeq
  refine le_of_mul_le_mul_right ?_ (pow_pos hwpos r)
  calc (xs.map (fun x : ℝ => ‖t - ((x : ℝ) : ℂ)‖)).prod * ‖w‖ ^ r
      = (xs.map (fun x : ℝ => ‖w - ((x : ℝ) : ℂ)‖)).prod * ‖t‖ ^ r := h2
    _ ≤ (xs.map (fun x : ℝ => ‖w - ((x : ℝ) : ℂ)‖)).prod * ‖w‖ ^ r :=
        mul_le_mul_of_nonneg_left hpow hPw

/-- **`Forgacs2017RationalDenominator` Prop. 1, the containment.**  A zero `t` no
further from the origin than `w` lies in the closed disk about the *smallest*
zero `x₁` of `P` through `w` — their `C₂`.

Their text justifies this by "considering the magnitudes of both sides", which
alone gives only that *some* factor shrinks; a product inequality does not bound
any one factor.  What makes it the smallest zero is that
`‖t - x‖² - ‖w - x‖²  =  -2x(Re t - Re w) + (‖t‖² - ‖w‖²)`
is **affine in `x`** and nonpositive at `x = 0`.  So if it were positive at `x₁`
the slope would be positive and it would be positive at every larger zero too,
making the whole product strictly larger — which the magnitude inequality
forbids. -/
theorem norm_sub_le_of_prod_le {t w : ℂ} {xs : Multiset ℝ} (hxs : xs ≠ 0)
    (hx : ∀ x ∈ xs, 0 < x) (hnorm : ‖t‖ ≤ ‖w‖) {x₁ : ℝ} (hx₁ : x₁ ∈ xs)
    (hmin : ∀ x ∈ xs, x₁ ≤ x)
    (hprod : (xs.map (fun x : ℝ => ‖t - ((x : ℝ) : ℂ)‖)).prod
      ≤ (xs.map (fun x : ℝ => ‖w - ((x : ℝ) : ℂ)‖)).prod) :
    ‖t - ((x₁ : ℝ) : ℂ)‖ ≤ ‖w - ((x₁ : ℝ) : ℂ)‖ := by
  by_contra hcon
  push Not at hcon
  -- the affine difference of squared distances
  have hD : ∀ x : ℝ, ‖t - ((x : ℝ) : ℂ)‖ ^ 2 - ‖w - ((x : ℝ) : ℂ)‖ ^ 2
      = -2 * x * (t.re - w.re) + (‖t‖ ^ 2 - ‖w‖ ^ 2) := by
    intro x
    have hn : ∀ v : ℂ, ‖v‖ ^ 2 = v.re ^ 2 + v.im ^ 2 := fun v => by
      rw [Complex.sq_norm, Complex.normSq_apply]; ring
    rw [hn, hn, hn, hn]
    simp only [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  have h0 : ‖t‖ ^ 2 - ‖w‖ ^ 2 ≤ 0 := by nlinarith [norm_nonneg t, norm_nonneg w]
  have hpos1 : 0 < ‖t - ((x₁ : ℝ) : ℂ)‖ ^ 2 - ‖w - ((x₁ : ℝ) : ℂ)‖ ^ 2 := by
    nlinarith [norm_nonneg (t - ((x₁ : ℝ) : ℂ)), norm_nonneg (w - ((x₁ : ℝ) : ℂ)), hcon]
  have hslope : t.re - w.re < 0 := by
    have := hD x₁
    nlinarith [hx x₁ hx₁, hpos1, h0, this]
  -- so every zero sees the same strict inequality
  have hall : ∀ x ∈ xs, ‖w - ((x : ℝ) : ℂ)‖ < ‖t - ((x : ℝ) : ℂ)‖ := by
    intro x hxm
    have hxx : x₁ ≤ x := hmin x hxm
    have hDx := hD x
    have hDx₁ := hD x₁
    have hstep : 0 < ‖t - ((x : ℝ) : ℂ)‖ ^ 2 - ‖w - ((x : ℝ) : ℂ)‖ ^ 2 := by
      nlinarith [hpos1, hslope, hxx, hDx, hDx₁]
    refine lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) ?_
    linarith
  have := multiset_prod_lt_prod (fun x : ℝ => ‖w - ((x : ℝ) : ℂ)‖)
    (fun x : ℝ => ‖t - ((x : ℝ) : ℂ)‖) xs hxs (fun x _ => norm_nonneg _) hall
  linarith

/-! ### The angle bound of `Forgacs2017RationalDenominator` Prop. 1 -/

/-- The numerator of the derivative of `sin θ / sin((r-1)θ)` is nonnegative.
Their text says it "vanishes when `θ = 0` and it is nondecreasing"; the reason it
is nondecreasing is that its own derivative is `r(r-2)(cos((r-2)θ) - cos(rθ))`,
and `cos` is antitone on `[0,π]`, where `0 ≤ (r-2)θ ≤ rθ ≤ π`. -/
theorem sin_numerator_nonneg {r : ℕ} (hr : 2 ≤ r) {θ : ℝ}
    (hθ : θ ∈ Set.Icc (0 : ℝ) (Real.pi / r)) :
    0 ≤ (r : ℝ) * Real.sin (((r : ℝ) - 2) * θ) - ((r : ℝ) - 2) * Real.sin ((r : ℝ) * θ) := by
  have hrpos : (0 : ℝ) < r := by positivity
  have hr2 : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  set f : ℝ → ℝ := fun u => (r : ℝ) * Real.sin (((r : ℝ) - 2) * u)
    - ((r : ℝ) - 2) * Real.sin ((r : ℝ) * u) with hf
  have hd : ∀ u : ℝ, HasDerivAt f
      ((r : ℝ) * ((r : ℝ) - 2) * (Real.cos (((r : ℝ) - 2) * u) - Real.cos ((r : ℝ) * u))) u := by
    intro u
    have hlin1 : HasDerivAt (fun v : ℝ => ((r : ℝ) - 2) * v) ((r : ℝ) - 2) u := by
      simpa using (hasDerivAt_id u).const_mul ((r : ℝ) - 2)
    have hlin2 : HasDerivAt (fun v : ℝ => (r : ℝ) * v) ((r : ℝ)) u := by
      simpa using (hasDerivAt_id u).const_mul ((r : ℝ))
    have h1 : HasDerivAt (fun v : ℝ => Real.sin (((r : ℝ) - 2) * v))
        (Real.cos (((r : ℝ) - 2) * u) * ((r : ℝ) - 2)) u := by
      simpa [Function.comp_def] using (Real.hasDerivAt_sin (((r : ℝ) - 2) * u)).comp u hlin1
    have h2 : HasDerivAt (fun v : ℝ => Real.sin ((r : ℝ) * v))
        (Real.cos ((r : ℝ) * u) * (r : ℝ)) u := by
      simpa [Function.comp_def] using (Real.hasDerivAt_sin ((r : ℝ) * u)).comp u hlin2
    have hval : (r : ℝ) * (Real.cos (((r : ℝ) - 2) * u) * ((r : ℝ) - 2))
          - ((r : ℝ) - 2) * (Real.cos ((r : ℝ) * u) * (r : ℝ))
        = (r : ℝ) * ((r : ℝ) - 2)
          * (Real.cos (((r : ℝ) - 2) * u) - Real.cos ((r : ℝ) * u)) := by ring
    exact hval ▸ ((h1.const_mul ((r : ℝ))).sub (h2.const_mul ((r : ℝ) - 2)))
  have hmono : MonotoneOn f (Set.Icc (0 : ℝ) (Real.pi / r)) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc _ _)
      (fun u _ => (hd u).continuousAt.continuousWithinAt)
      (fun u _ => ((hd u).differentiableAt).differentiableWithinAt) ?_
    intro u hu
    rw [interior_Icc] at hu
    rw [(hd u).deriv]
    have hu0 : 0 ≤ u := hu.1.le
    have hru : (r : ℝ) * u ≤ Real.pi := by
      have := hu.2.le
      rw [le_div_iff₀ hrpos] at this
      linarith [this]
    have hcos : Real.cos ((r : ℝ) * u) ≤ Real.cos (((r : ℝ) - 2) * u) := by
      refine Real.cos_le_cos_of_nonneg_of_le_pi (by nlinarith) hru (by nlinarith)
    have hb : 0 ≤ Real.cos (((r : ℝ) - 2) * u) - Real.cos ((r : ℝ) * u) := by linarith
    exact mul_nonneg (mul_nonneg hrpos.le (by linarith : (0:ℝ) ≤ (r : ℝ) - 2)) hb
  have hf0 : f 0 = 0 := by simp [hf]
  have hle := hmono (Set.left_mem_Icc.2 (by positivity)) hθ hθ.1
  rw [hf0] at hle
  simpa [hf] using hle


/-! ### `Forgacs2017RationalDenominator` Lemma 6 — `z` maps onto `(a,b)`

Their proof is "`z(θ)` is continuous and monotone increasing, so it suffices to
show the endpoint limits are `a` and `b`".  Identifying those limits is a fact
about the branch and belongs with `FTBranchRegularity`; what is here is the
passage from the limits to surjectivity, in the two shapes `eq:ab-def` needs —
`b` finite, and `b = +∞` when `r > 1`. -/

private theorem le_of_tendsto_of_strictMonoOn {z : ℝ → ℝ} {p q a : ℝ}
    (hmono : StrictMonoOn z (Set.Ioo p q))
    (hp : Filter.Tendsto z (nhdsWithin p (Set.Ioo p q)) (nhds a))
    [(nhdsWithin p (Set.Ioo p q)).NeBot] {θ : ℝ} (hθ : θ ∈ Set.Ioo p q) :
    a ≤ z θ := by
  refine le_of_tendsto hp ?_
  filter_upwards [self_mem_nhdsWithin, eventually_nhdsWithin_of_eventually_nhds
    (eventually_lt_nhds hθ.1)] with s hs hlt
  exact (hmono hs hθ hlt).le

private theorem ge_of_tendsto_of_strictMonoOn {z : ℝ → ℝ} {p q b : ℝ}
    (hmono : StrictMonoOn z (Set.Ioo p q))
    (hq : Filter.Tendsto z (nhdsWithin q (Set.Ioo p q)) (nhds b))
    [(nhdsWithin q (Set.Ioo p q)).NeBot] {θ : ℝ} (hθ : θ ∈ Set.Ioo p q) :
    z θ ≤ b := by
  refine ge_of_tendsto hq ?_
  filter_upwards [self_mem_nhdsWithin, eventually_nhdsWithin_of_eventually_nhds
    (eventually_gt_nhds hθ.2)] with s hs hlt
  exact (hmono hθ hs hlt).le

/-- **`Forgacs2017RationalDenominator` Lemma 6, finite right endpoint.**  A
continuous strictly monotone function on `(p,q)` with one-sided limits `a` and
`b` maps `(p,q)` onto `(a,b)`. -/
theorem image_Ioo_eq_Ioo_of_tendsto {z : ℝ → ℝ} {p q a b : ℝ}
    (hcont : ContinuousOn z (Set.Ioo p q)) (hmono : StrictMonoOn z (Set.Ioo p q))
    (hp : Filter.Tendsto z (nhdsWithin p (Set.Ioo p q)) (nhds a))
    (hq : Filter.Tendsto z (nhdsWithin q (Set.Ioo p q)) (nhds b))
    [(nhdsWithin p (Set.Ioo p q)).NeBot] [(nhdsWithin q (Set.Ioo p q)).NeBot] :
    z '' Set.Ioo p q = Set.Ioo a b := by
  ext y
  constructor
  · rintro ⟨θ, hθ, rfl⟩
    obtain ⟨θ₁, hθ₁⟩ : (Set.Ioo p θ).Nonempty := Set.nonempty_Ioo.2 hθ.1
    obtain ⟨θ₂, hθ₂⟩ : (Set.Ioo θ q).Nonempty := Set.nonempty_Ioo.2 hθ.2
    have hm₁ : θ₁ ∈ Set.Ioo p q := ⟨hθ₁.1, lt_trans hθ₁.2 hθ.2⟩
    have hm₂ : θ₂ ∈ Set.Ioo p q := ⟨lt_trans hθ.1 hθ₂.1, hθ₂.2⟩
    exact ⟨lt_of_le_of_lt (le_of_tendsto_of_strictMonoOn hmono hp hm₁) (hmono hm₁ hθ hθ₁.2),
      lt_of_lt_of_le (hmono hθ hm₂ hθ₂.1) (ge_of_tendsto_of_strictMonoOn hmono hq hm₂)⟩
  · rintro ⟨hay, hyb⟩
    obtain ⟨θ₁, hθ₁mem, hθ₁⟩ : ∃ s ∈ Set.Ioo p q, z s < y := by
      have h : ∀ᶠ s in nhdsWithin p (Set.Ioo p q), z s < y := hp (Iio_mem_nhds hay)
      obtain ⟨s, hz, hs⟩ := (h.and self_mem_nhdsWithin).exists
      exact ⟨s, hs, hz⟩
    obtain ⟨θ₂, hθ₂mem, hθ₂⟩ : ∃ s ∈ Set.Ioo p q, y < z s := by
      have h : ∀ᶠ s in nhdsWithin q (Set.Ioo p q), y < z s := hq (Ioi_mem_nhds hyb)
      obtain ⟨s, hz, hs⟩ := (h.and self_mem_nhdsWithin).exists
      exact ⟨s, hs, hz⟩
    have hlt : θ₁ < θ₂ := by
      by_contra hcon
      push Not at hcon
      rcases lt_or_eq_of_le hcon with h | h
      · exact absurd (hmono hθ₂mem hθ₁mem h) (by linarith)
      · subst h; linarith
    have hsub : Set.Icc θ₁ θ₂ ⊆ Set.Ioo p q := fun s hs =>
      ⟨lt_of_lt_of_le hθ₁mem.1 hs.1, lt_of_le_of_lt hs.2 hθ₂mem.2⟩
    obtain ⟨θ, hθ, hzθ⟩ :=
      intermediate_value_Ioo hlt.le (hcont.mono hsub) (Set.mem_Ioo.2 ⟨hθ₁, hθ₂⟩)
    exact ⟨θ, hsub (Set.mem_Icc_of_Ioo hθ), hzθ⟩

/-- **`Forgacs2017RationalDenominator` Lemma 6, unbounded right endpoint.**  The
`r > 1` case of `eq:ab-def`, where `b = +∞`: the image is the ray `(a,∞)`. -/
theorem image_Ioo_eq_Ioi_of_tendsto_atTop {z : ℝ → ℝ} {p q a : ℝ}
    (hcont : ContinuousOn z (Set.Ioo p q)) (hmono : StrictMonoOn z (Set.Ioo p q))
    (hp : Filter.Tendsto z (nhdsWithin p (Set.Ioo p q)) (nhds a))
    (hq : Filter.Tendsto z (nhdsWithin q (Set.Ioo p q)) Filter.atTop)
    [(nhdsWithin p (Set.Ioo p q)).NeBot] [(nhdsWithin q (Set.Ioo p q)).NeBot] :
    z '' Set.Ioo p q = Set.Ioi a := by
  ext y
  constructor
  · rintro ⟨θ, hθ, rfl⟩
    obtain ⟨θ₁, hθ₁⟩ : (Set.Ioo p θ).Nonempty := Set.nonempty_Ioo.2 hθ.1
    have hm₁ : θ₁ ∈ Set.Ioo p q := ⟨hθ₁.1, lt_trans hθ₁.2 hθ.2⟩
    exact lt_of_le_of_lt (le_of_tendsto_of_strictMonoOn hmono hp hm₁) (hmono hm₁ hθ hθ₁.2)
  · intro hay
    obtain ⟨θ₁, hθ₁mem, hθ₁⟩ : ∃ s ∈ Set.Ioo p q, z s < y := by
      have h : ∀ᶠ s in nhdsWithin p (Set.Ioo p q), z s < y := hp (Iio_mem_nhds hay)
      obtain ⟨s, hz, hs⟩ := (h.and self_mem_nhdsWithin).exists
      exact ⟨s, hs, hz⟩
    obtain ⟨θ₂, hθ₂mem, hθ₂⟩ : ∃ s ∈ Set.Ioo p q, y < z s := by
      have h : ∀ᶠ s in nhdsWithin q (Set.Ioo p q), y < z s :=
        hq.eventually (Filter.eventually_gt_atTop y)
      obtain ⟨s, hz, hs⟩ := (h.and self_mem_nhdsWithin).exists
      exact ⟨s, hs, hz⟩
    have hlt : θ₁ < θ₂ := by
      by_contra hcon
      push Not at hcon
      rcases lt_or_eq_of_le hcon with h | h
      · exact absurd (hmono hθ₂mem hθ₁mem h) (by linarith)
      · subst h; linarith
    have hsub : Set.Icc θ₁ θ₂ ⊆ Set.Ioo p q := fun s hs =>
      ⟨lt_of_lt_of_le hθ₁mem.1 hs.1, lt_of_le_of_lt hs.2 hθ₂mem.2⟩
    obtain ⟨θ, hθ, hzθ⟩ :=
      intermediate_value_Ioo hlt.le (hcont.mono hsub) (Set.mem_Ioo.2 ⟨hθ₁, hθ₂⟩)
    exact ⟨θ, hsub (Set.mem_Icc_of_Ioo hθ), hzθ⟩


/-! ### From `τ`'s endpoint limits to `z`'s

`Forgacs2017RationalDenominator` Lemma 6 reduces to "the endpoint limits of `z`
are `a` and `b`", and gets those from the limits of `τ`, which converge to real
multiple zeros of the limiting pencil.  Identifying *those* is a fact about the
branch; the passage from them to `z` is composition of limits along
`z(θ) = -P(γ(θ))/γ(θ)^r`, and is what follows. -/

/-- The branch point `τ(θ)e^{-iθ}` converges wherever `τ` does. -/
theorem tendsto_branchPoint_of_tendsto_tau {τ : ℝ → ℝ} {p ta : ℝ} {S : Set ℝ}
    (hτ : Filter.Tendsto τ (nhdsWithin p S) (nhds ta)) :
    Filter.Tendsto (fun θ : ℝ => ((τ θ : ℝ) : ℂ) * Complex.exp (-((θ : ℝ) : ℂ) * Complex.I))
      (nhdsWithin p S) (nhds (((ta : ℝ) : ℂ) * Complex.exp (-((p : ℝ) : ℂ) * Complex.I))) := by
  have h1 : Filter.Tendsto (fun θ : ℝ => ((τ θ : ℝ) : ℂ)) (nhdsWithin p S)
      (nhds ((ta : ℝ) : ℂ)) := (Complex.continuous_ofReal.tendsto ta).comp hτ
  have h2 : Filter.Tendsto (fun θ : ℝ => Complex.exp (-((θ : ℝ) : ℂ) * Complex.I))
      (nhdsWithin p S) (nhds (Complex.exp (-((p : ℝ) : ℂ) * Complex.I))) := by
    refine (Complex.continuous_exp.tendsto _).comp ?_
    exact (((Complex.continuous_ofReal.neg).mul continuous_const).tendsto p).mono_left
      nhdsWithin_le_nhds
  exact h1.mul h2

/-- **`Forgacs2017RationalDenominator` Lemma 6, the finite-endpoint passage.**
`z(θ) = -P(γ(θ))/γ(θ)^r` converges to `-P(t_e)/t_e^r` wherever the branch point
converges to a nonzero `t_e`.  With `t_e = t_a` this is their `a`. -/
theorem tendsto_ftZ_of_tendsto_branchPoint {P : Polynomial ℂ} {r : ℕ} {γ : ℝ → ℂ}
    {p : ℝ} {S : Set ℝ} {te : ℂ} (hte : te ≠ 0)
    (hγ : Filter.Tendsto γ (nhdsWithin p S) (nhds te)) :
    Filter.Tendsto (fun θ : ℝ => -P.eval (γ θ) / (γ θ) ^ r) (nhdsWithin p S)
      (nhds (-P.eval te / te ^ r)) := by
  refine Filter.Tendsto.div ?_ ?_ (pow_ne_zero r hte)
  · exact (((Polynomial.continuous P).tendsto te).comp hγ).neg
  · exact ((continuous_pow r).tendsto te).comp hγ

/-- **`Forgacs2017RationalDenominator` Lemma 6, the unbounded-endpoint passage.**
When the branch point runs into the origin — their `t_b = 0` for `r > 1` — the
spectral parameter leaves every bound, since `P(0) ≠ 0`.  This is the `b = +∞`
of `eq:ab-def`, and it is why that endpoint cannot be a real number. -/
theorem tendsto_norm_ftZ_atTop_of_tendsto_zero {P : Polynomial ℂ} {r : ℕ} (hr : 1 ≤ r)
    (hP0 : P.eval 0 ≠ 0) {γ : ℝ → ℂ} {q : ℝ} {S : Set ℝ}
    (hne : ∀ᶠ θ in nhdsWithin q S, γ θ ≠ 0)
    (hγ : Filter.Tendsto γ (nhdsWithin q S) (nhds 0)) :
    Filter.Tendsto (fun θ : ℝ => ‖-P.eval (γ θ) / (γ θ) ^ r‖) (nhdsWithin q S)
      Filter.atTop := by
  have hnum : Filter.Tendsto (fun θ : ℝ => ‖P.eval (γ θ)‖) (nhdsWithin q S)
      (nhds ‖P.eval 0‖) := ((((Polynomial.continuous P).tendsto 0).comp hγ).norm)
  have hden : Filter.Tendsto (fun θ : ℝ => ‖γ θ‖ ^ r) (nhdsWithin q S)
      (nhdsWithin 0 (Set.Ioi 0)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have h0 : Filter.Tendsto (fun θ : ℝ => ‖γ θ‖) (nhdsWithin q S) (nhds 0) := by
        simpa using hγ.norm
      simpa [Function.comp_def, zero_pow (show r ≠ 0 by omega)] using
        ((continuous_pow r).tendsto (0 : ℝ)).comp h0
    · filter_upwards [hne] with θ hθ
      exact pow_pos (norm_pos_iff.mpr hθ) r
  have hinv : Filter.Tendsto (fun θ : ℝ => (‖γ θ‖ ^ r)⁻¹) (nhdsWithin q S) Filter.atTop :=
    hden.inv_tendsto_nhdsGT_zero
  have hkey : Filter.Tendsto (fun θ : ℝ => ‖P.eval (γ θ)‖ * (‖γ θ‖ ^ r)⁻¹)
      (nhdsWithin q S) Filter.atTop :=
    Filter.Tendsto.pos_mul_atTop (norm_pos_iff.mpr hP0) hnum hinv
  refine hkey.congr fun θ => ?_
  rw [norm_div, norm_neg, norm_pow, div_eq_mul_inv]

end ForgacsTran
