/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Sharp elementary bounds for the complex exponential and logarithm

Three estimates, each sharp and each unrestricted where Mathlib's counterpart is not.

* `\|\exp z - 1\| \le \exp\|z\| - 1`, for **every** `z`.  Mathlib's `Complex.norm_exp_sub_one_le`
  gives `2\|z\|` under `\|z\| \le 1`; this is the bound with no side condition, and it is exact on
  the positive reals.
* `\|\log(1-\zeta)\| \le -\log(1-\|\zeta\|)` for `\|\zeta\| < 1`, again exact on the positive
  reals.
* `\|\exp z_1 - \exp z_2\| \le \tfrac65\|z_1-z_2\|` on the disc of radius `\log(6/5)`, a Lipschitz
  bound of the shape a contraction argument consumes.

All three come from the mean value inequality applied along the segment, with the majorant
integrated in closed form.

## Main results

* `Shields.norm_cexp_sub_one_le`
* `Shields.norm_clog_one_sub_le`
* `Shields.norm_cexp_sub_cexp_le`

`Shields.norm_mul_cexp_le` and `Shields.norm_div_one_sub_mul_le` carry the estimate: each says
that the complex derivative along the segment is dominated by the derivative of the real majorant,
which is the only step of either proof that is not the mean value inequality.

`Shields.re_one_sub_mul_pos` and `Shields.one_sub_mul_norm_pos` carry the hypothesis: for
`‖ζ‖ < 1` the segment from `1` to `1 - ζ` stays in the open right half-plane, hence off the slit
`Complex.log` is cut along, and the real majorant `1 - t‖ζ‖` stays positive with it.  Weaken
`‖ζ‖ < 1` and it is these two that fail first.

## Tags

complex exponential, complex logarithm, mean value inequality, lipschitz
-/

open Complex Metric Set

namespace Shields

/-- **The exponential segment's derivative is dominated by the real majorant's.**  Along
`t ↦ exp (t z)` the derivative has modulus `‖z‖ exp (t ‖z‖ · cos θ)` with `θ = arg z`, and
`Re z ≤ ‖z‖` replaces the cosine by `1`.  This one inequality is the whole content of
`norm_cexp_sub_one_le`; the mean value inequality supplies the rest. -/
theorem norm_mul_cexp_le (z : ℂ) {t : ℝ} (ht : 0 ≤ t) :
    ‖z * Complex.exp ((t : ℂ) * z)‖ ≤ ‖z‖ * Real.exp (t * ‖z‖) := by
  have hre : ((t : ℂ) * z).re = t * z.re := by simp [Complex.mul_re]
  have h1 : z.re ≤ ‖z‖ := Complex.re_le_norm z
  calc ‖z * Complex.exp ((t : ℂ) * z)‖ = ‖z‖ * Real.exp (t * z.re) := by
        simp [Complex.norm_exp, hre]
    _ ≤ ‖z‖ * Real.exp (t * ‖z‖) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by nlinarith)) (norm_nonneg z)

/-- `‖exp z - 1‖ ≤ exp ‖z‖ - 1`, the sharp form of the exponential increment bound. -/
theorem norm_cexp_sub_one_le (z : ℂ) : ‖Complex.exp z - 1‖ ≤ Real.exp ‖z‖ - 1 := by
  set f : ℝ → ℂ := fun t => Complex.exp ((t : ℂ) * z) - 1 with hf_def
  set f' : ℝ → ℂ := fun t => z * Complex.exp ((t : ℂ) * z) with hf'_def
  set B : ℝ → ℝ := fun t => Real.exp (t * ‖z‖) - 1 with hB_def
  set B' : ℝ → ℝ := fun t => ‖z‖ * Real.exp (t * ‖z‖) with hB'_def
  have hderiv : ∀ t : ℝ, HasDerivAt f (f' t) t := by
    intro t
    have h : HasDerivAt (fun ζ : ℂ => Complex.exp (ζ * z) - 1) (z * Complex.exp ((t : ℂ) * z))
        (t : ℂ) := by
      have := ((hasDerivAt_id ((t : ℂ))).mul_const z).cexp
      simpa [mul_comm] using this.sub_const 1
    simpa [hf_def, hf'_def] using h.comp_ofReal
  have hBderiv : ∀ t : ℝ, HasDerivAt B (B' t) t := by
    intro t
    have hi : HasDerivAt (fun r : ℝ => r * ‖z‖) ‖z‖ t := by
      simpa using (hasDerivAt_id t).mul_const ‖z‖
    simpa [hB_def, hB'_def, mul_comm] using hi.exp.sub_const 1
  have key : ∀ ⦃t⦄, t ∈ Icc (0 : ℝ) 1 → ‖f t‖ ≤ B t := by
    refine image_norm_le_of_norm_deriv_right_le_deriv_boundary
      (fun t _ => (hderiv t).continuousAt.continuousWithinAt)
      (fun t _ => (hderiv t).hasDerivWithinAt) ?_ hBderiv ?_
    · simp [hf_def, hB_def]
    · intro t ht
      simpa [hf'_def, hB'_def] using norm_mul_cexp_le z ht.1
  simpa [hf_def, hB_def] using key (right_mem_Icc.2 zero_le_one)

/-- **The real majorant stays positive along the segment.**  For `‖ζ‖ < 1` and `t ∈ [0, 1]`,
`1 - t‖ζ‖ > 0`, which is what keeps `-log (1 - t‖ζ‖)` defined and increasing. -/
theorem one_sub_mul_norm_pos {ζ : ℂ} (hζ : ‖ζ‖ < 1) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    0 < 1 - t * ‖ζ‖ := by
  have hs0 : 0 ≤ ‖ζ‖ := norm_nonneg ζ
  have : t * ‖ζ‖ ≤ 1 * ‖ζ‖ := by nlinarith [ht.2, hs0]
  nlinarith [hζ]

/-- **The segment from `1` to `1 - ζ` never leaves the right half-plane**, when `‖ζ‖ < 1`.

This is the whole reason the estimate can be run along that segment: `Complex.log` is analytic on
the slit plane, and staying in the open right half-plane is a sufficient condition that survives
the whole path.  Weaken `‖ζ‖ < 1` and the segment can reach the slit. -/
theorem re_one_sub_mul_pos {ζ : ℂ} (hζ : ‖ζ‖ < 1) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    0 < (1 - (t : ℂ) * ζ).re := by
  have h1 : ((t : ℂ) * ζ).re ≤ ‖(t : ℂ) * ζ‖ := Complex.re_le_norm _
  have h2 : ‖(t : ℂ) * ζ‖ = t * ‖ζ‖ := by simp [abs_of_nonneg ht.1]
  have h3 := one_sub_mul_norm_pos hζ ht
  simp only [Complex.sub_re, Complex.one_re]
  linarith [h1, h2.symm ▸ h1]

/-- **The logarithmic segment's derivative is dominated by the real majorant's.**  The reverse
triangle inequality gives `‖1 - tζ‖ ≥ 1 - t‖ζ‖`, and the right-hand side is positive by
`one_sub_mul_norm_pos`, so the complex logarithmic derivative `-ζ / (1 - tζ)` is bounded by the
real one `‖ζ‖ / (1 - t‖ζ‖)`.  This is the counterpart of `norm_mul_cexp_le` for the logarithm,
and it is the whole content of `norm_clog_one_sub_le`. -/
theorem norm_div_one_sub_mul_le {ζ : ℂ} (hζ : ‖ζ‖ < 1) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖-ζ / (1 - (t : ℂ) * ζ)‖ ≤ ‖ζ‖ / (1 - t * ‖ζ‖) := by
  have hd0 : 0 < (1 : ℝ) - t * ‖ζ‖ := one_sub_mul_norm_pos hζ ht
  have hden : (1 : ℝ) - t * ‖ζ‖ ≤ ‖1 - (t : ℂ) * ζ‖ := by
    have h1 : ‖(1 : ℂ)‖ - ‖(t : ℂ) * ζ‖ ≤ ‖1 - (t : ℂ) * ζ‖ := norm_sub_norm_le _ _
    have habs : ‖((t : ℝ) : ℂ)‖ = t := by simp [abs_of_nonneg ht.1]
    rw [norm_one, norm_mul, habs] at h1
    linarith
  calc ‖-ζ / (1 - (t : ℂ) * ζ)‖ = ‖ζ‖ / ‖1 - (t : ℂ) * ζ‖ := by simp
    _ ≤ ‖ζ‖ / (1 - t * ‖ζ‖) := by gcongr

/-- `‖log (1 - ζ)‖ ≤ -log (1 - ‖ζ‖)` for `‖ζ‖ < 1`: the modulus of the complex logarithm is
dominated by the real logarithmic series with the same modulus. -/
theorem norm_clog_one_sub_le {ζ : ℂ} (hζ : ‖ζ‖ < 1) :
    ‖Complex.log (1 - ζ)‖ ≤ -Real.log (1 - ‖ζ‖) := by
  set s : ℝ := ‖ζ‖ with hs_def
  have hs0 : 0 ≤ s := norm_nonneg ζ
  set f : ℝ → ℂ := fun t => Complex.log (1 - (t : ℂ) * ζ) with hf_def
  set f' : ℝ → ℂ := fun t => -ζ / (1 - (t : ℂ) * ζ) with hf'_def
  set B : ℝ → ℝ := fun t => -Real.log (1 - t * s) with hB_def
  set B' : ℝ → ℝ := fun t => s / (1 - t * s) with hB'_def
  have hslit : ∀ t ∈ Icc (0 : ℝ) 1, (1 - (t : ℂ) * ζ) ∈ Complex.slitPlane := fun t ht =>
    Complex.mem_slitPlane_iff.2 (Or.inl (re_one_sub_mul_pos hζ ht))
  have hderiv : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt f (f' t) t := by
    intro t ht
    have hinner : HasDerivAt (fun ζ' : ℂ => 1 - ζ' * ζ) (-ζ) (t : ℂ) := by
      simpa using ((hasDerivAt_id ((t : ℂ))).mul_const ζ).const_sub 1
    have h := hinner.clog (hslit t ht)
    simpa [hf_def, hf'_def] using h.comp_ofReal
  have hBpos : ∀ t ∈ Icc (0 : ℝ) 1, 0 < 1 - t * s := fun t ht => one_sub_mul_norm_pos hζ ht
  have hBderiv : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt B (B' t) t := by
    intro t ht
    have hne : (1 - t * s) ≠ 0 := ne_of_gt (hBpos t ht)
    have h1 : HasDerivAt (fun r : ℝ => 1 - r * s) (-s) t := by
      simpa using ((hasDerivAt_id t).mul_const s).const_sub 1
    have h2 := (Real.hasDerivAt_log hne).comp t h1
    have : HasDerivAt (fun r : ℝ => -Real.log (1 - r * s)) (s / (1 - t * s)) t := by
      have := h2.neg
      convert! this using 1
      field_simp
    simpa [hB_def, hB'_def] using this
  have key : ∀ ⦃t⦄, t ∈ Icc (0 : ℝ) 1 → ‖f t‖ ≤ B t := by
    refine image_norm_le_of_norm_deriv_right_le_deriv_boundary' (B' := B')
      (fun t ht => (hderiv t ht).continuousAt.continuousWithinAt)
      (fun t ht => (hderiv t (Ico_subset_Icc_self ht)).hasDerivWithinAt) ?_ ?_ ?_ ?_
    · simp [hf_def, hB_def]
    · exact fun t ht => (hBderiv t ht).continuousAt.continuousWithinAt
    · exact fun t ht => (hBderiv t (Ico_subset_Icc_self ht)).hasDerivWithinAt
    · intro t ht
      simpa [hf'_def, hB'_def, hs_def] using norm_div_one_sub_mul_le hζ (Ico_subset_Icc_self ht)
  simpa [hf_def, hB_def] using key (right_mem_Icc.2 zero_le_one)

/-- `‖exp z₁ - exp z₂‖ ≤ (6/5)‖z₁ - z₂‖` on the convex disk `‖z‖ ≤ log (6/5)`, where
`‖exp‖ ≤ 6/5`. -/
theorem norm_cexp_sub_cexp_le {z₁ z₂ : ℂ} (h₁ : ‖z₁‖ ≤ Real.log (6 / 5))
    (h₂ : ‖z₂‖ ≤ Real.log (6 / 5)) :
    ‖Complex.exp z₁ - Complex.exp z₂‖ ≤ 6 / 5 * ‖z₁ - z₂‖ := by
  have hmem : ∀ v : ℂ, ‖v‖ ≤ Real.log (6 / 5) ↔ v ∈ closedBall (0 : ℂ) (Real.log (6 / 5)) := by
    intro v; simp
  refine Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := Complex.exp) (f' := Complex.exp) ?_ ?_ (convex_closedBall _ _) ((hmem z₂).1 h₂)
    ((hmem z₁).1 h₁)
  · intro v _
    exact (Complex.hasDerivAt_exp v).hasDerivWithinAt
  · intro v hv
    have hre : v.re ≤ Real.log (6 / 5) := le_trans (Complex.re_le_norm _) ((hmem v).2 hv)
    calc ‖Complex.exp v‖ = Real.exp v.re := Complex.norm_exp _
      _ ≤ Real.exp (Real.log (6 / 5)) := Real.exp_le_exp.2 hre
      _ = 6 / 5 := Real.exp_log (by norm_num)


/-! ### Axiom footprint -/

/-- info: 'Shields.norm_cexp_sub_one_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms norm_cexp_sub_one_le

/-- info: 'Shields.norm_clog_one_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms norm_clog_one_sub_le

/-- info: 'Shields.norm_cexp_sub_cexp_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms norm_cexp_sub_cexp_le

end Shields
