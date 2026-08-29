/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# The entire cardinal sine

`Real.sinc` is in Mathlib; its complex counterpart is not.  `Shields.csinc` is
`\sin z / z` with the removable value `1` at the origin, and it is **entire** — it is literally
`dslope \sin 0`, so differentiability comes from Mathlib's `dslope` API rather than from a case
split.

Two facts do the work wherever this function appears as a limit profile:

* its **zero set is exactly** `\pi\mathbb{Z}\setminus\{0\}`, and each zero is simple, since
  `\cos(j\pi)\ne 0`;
* `\operatorname{csinc}(\pi s)` depends on `s` **only through** `s^2`, because `csinc` is even.
  So a substitution `s=\sqrt{z}` produces a single-valued function of `z` and no branch has to be
  chosen.  The same holds over `\mathbb{R}`.

A window of radius below `\pi` about a lattice point contains no other zero, which is what lets a
zero-counting argument on such a disc see exactly one.

## Main results

* `Shields.csinc`, `Shields.csinc_of_ne_zero`, `Shields.csinc_ofReal`, `Shields.csinc_neg`
* `Shields.csinc_eq_dslope`, `Shields.differentiable_csinc`, `Shields.analyticOnNhd_csinc`
* `Shields.csinc_eq_zero_iff` — **the zero set**
* `Shields.hasDerivAt_csinc`, `Shields.deriv_csinc_intCast_mul_pi_ne_zero` — **the zeros are
  simple**
* `Shields.csinc_ne_zero_of_mem_closedBall` — a window of radius below `\pi` isolates its zero
* `Shields.csinc_pi_mul_congr_sq`, `Shields.sinc_pi_mul_congr_sq` — dependence on `s^2` only

## Implementation notes

The definition is `if z = 0 then 1 else sin z / z` rather than `dslope sin 0` directly, so that
the value away from the origin is definitionally the quotient; `csinc_eq_dslope` records that the
two agree, and every analytic statement is proved through it.

## References

* NIST Digital Library of Mathematical Functions, Chapter 4: Elementary Functions.

## Tags

sinc, cardinal sine, entire function, removable singularity, dslope, simple zero
-/

open Complex Metric Set

namespace Shields

/-- Away from the origin, `sinc x = 0 ↔ sin x = 0`: the zeros of `sinc` are the
nonzero zeros of `sin`.  The pinned Mathlib revision has no `iff` in this
form. -/
theorem sinc_eq_zero_iff {x : ℝ} (hx : x ≠ 0) : Real.sinc x = 0 ↔ Real.sin x = 0 := by
  rw [Real.sinc_of_ne_zero hx, div_eq_zero_iff, or_iff_left hx]

/-- **Branch independence over `ℝ`.**  `sinc(πs)` depends on `s` only through `s²`, so a
substitution `s = √x` gives a single-valued function of `x`. -/
theorem sinc_pi_mul_congr_sq {s t : ℝ} (h : s ^ 2 = t ^ 2) :
    Real.sinc (Real.pi * s) = Real.sinc (Real.pi * t) := by
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp h with rfl | rfl
  · rfl
  · rw [mul_neg, Real.sinc_neg]

/-- The complex cardinal sine `sin z / z`, with the removable value `1` at the
origin.  Mathlib has `Real.sinc` but no complex counterpart. -/
noncomputable def csinc (z : ℂ) : ℂ := if z = 0 then 1 else Complex.sin z / z

@[simp] theorem csinc_zero : csinc 0 = 1 := if_pos rfl

theorem csinc_of_ne_zero {z : ℂ} (hz : z ≠ 0) : csinc z = Complex.sin z / z := if_neg hz

/-- `csinc` restricted to the reals is `Real.sinc`. -/
theorem csinc_ofReal (x : ℝ) : csinc (x : ℂ) = (Real.sinc x : ℂ) := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · have hxC : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx
    rw [csinc_of_ne_zero hxC, Real.sinc_of_ne_zero hx, Complex.ofReal_div, Complex.ofReal_sin]

/-- **`csinc` is even.**  This is the whole content of the branch independence of
`sinc(π√(λ/𝒞_r))`: the two square roots of `λ/𝒞_r` differ by a sign. -/
@[simp] theorem csinc_neg (z : ℂ) : csinc (-z) = csinc z := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp
  · rw [csinc_of_ne_zero (neg_ne_zero.mpr hz), csinc_of_ne_zero hz, Complex.sin_neg,
      neg_div_neg_eq]

theorem csinc_eq_dslope : csinc = dslope Complex.sin 0 := by
  ext z
  simp [dslope, Function.update_apply, csinc, slope, div_eq_inv_mul]

/-- **The edge profile is entire.**  `csinc = dslope sin 0` and the removable
singularity theorem makes a `dslope` of a holomorphic function holomorphic. -/
theorem differentiable_csinc : Differentiable ℂ csinc := by
  rw [← differentiableOn_univ, csinc_eq_dslope]
  exact (Complex.differentiableOn_dslope (by simp)).mpr
    Complex.differentiable_sin.differentiableOn

/-- **The zero set of the entire cardinal sine** is `πℤ ∖ {0}`. -/
theorem csinc_eq_zero_iff {z : ℂ} : csinc z = 0 ↔ ∃ j : ℤ, j ≠ 0 ∧ z = (j : ℂ) * Real.pi := by
  constructor
  · intro h
    have hz : z ≠ 0 := by rintro rfl; simp at h
    rw [csinc_of_ne_zero hz, div_eq_zero_iff, or_iff_left hz, Complex.sin_eq_zero_iff] at h
    obtain ⟨j, hj⟩ := h
    refine ⟨j, ?_, hj⟩
    rintro rfl
    exact hz (by simpa using hj)
  · rintro ⟨j, hj, rfl⟩
    have hjC : (j : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hj
    have hpi : ((Real.pi : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    rw [csinc_of_ne_zero (mul_ne_zero hjC hpi),
      Complex.sin_eq_zero_iff.mpr ⟨j, rfl⟩, zero_div]

/-- **Branch independence.**  `csinc(πs)` depends on `s` only through `s²`, so a substitution
`s = √z` gives a single-valued function of `z` and no branch has to be chosen. -/
theorem csinc_pi_mul_congr_sq {s t : ℂ} (h : s ^ 2 = t ^ 2) :
    csinc ((Real.pi : ℂ) * s) = csinc ((Real.pi : ℂ) * t) := by
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp h with rfl | rfl
  · rfl
  · rw [mul_neg, csinc_neg]

theorem analyticOnNhd_csinc (s : Set ℂ) : AnalyticOnNhd ℂ csinc s :=
  ((differentiable_csinc.differentiableOn).analyticOnNhd isOpen_univ).mono (subset_univ s)

/-- Away from the origin `csinc` is `sin z / z`, with the quotient derivative. -/
theorem hasDerivAt_csinc {z : ℂ} (hz : z ≠ 0) :
    HasDerivAt csinc ((Complex.cos z * z - Complex.sin z) / z ^ 2) z := by
  have hquot : HasDerivAt (fun w : ℂ => Complex.sin w / w)
      ((Complex.cos z * z - Complex.sin z * 1) / z ^ 2) z :=
    (Complex.hasDerivAt_sin z).div (hasDerivAt_id z) hz
  have hev : csinc =ᶠ[nhds z] fun w : ℂ => Complex.sin w / w := by
    filter_upwards [eventually_ne_nhds hz] with w hw
    exact csinc_of_ne_zero hw
  rw [show (Complex.cos z * z - Complex.sin z) / z ^ 2
      = (Complex.cos z * z - Complex.sin z * 1) / z ^ 2 by ring]
  exact hquot.congr_of_eventuallyEq hev

/-- At a lattice point the sine vanishes, so the cosine has modulus one. -/
theorem cos_intCast_mul_pi_ne_zero (j : ℤ) : Complex.cos ((j : ℂ) * Real.pi) ≠ 0 := by
  have hsin : Complex.sin ((j : ℂ) * Real.pi) = 0 := Complex.sin_eq_zero_iff.mpr ⟨j, rfl⟩
  intro hcos
  have h := Complex.sin_sq_add_cos_sq ((j : ℂ) * Real.pi)
  rw [hsin, hcos] at h
  norm_num at h

/-- **The lattice zeros of the edge profile are simple.**  This is what makes the
Hurwitz count in each window exactly one: a double zero of the limit would let two
zeros of the approximant sit in the same disk. -/
theorem deriv_csinc_intCast_mul_pi_ne_zero {j : ℤ} (hj : j ≠ 0) :
    deriv csinc ((j : ℂ) * Real.pi) ≠ 0 := by
  have hpi : ((Real.pi : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hz : ((j : ℂ) * Real.pi) ≠ 0 := mul_ne_zero (Int.cast_ne_zero.mpr hj) hpi
  have hsin : Complex.sin ((j : ℂ) * Real.pi) = 0 := Complex.sin_eq_zero_iff.mpr ⟨j, rfl⟩
  rw [(hasDerivAt_csinc hz).deriv]
  refine div_ne_zero ?_ (pow_ne_zero 2 hz)
  rw [hsin, sub_zero]
  exact mul_ne_zero (cos_intCast_mul_pi_ne_zero j) hz

/-- **A window of radius below `π` isolates its lattice point.**  Consecutive
lattice points are `π` apart, so a disk of radius `r < π` about `jπ` carries no other zero of
`csinc`.  This holds at `j = 0` as well, where the punctured disk misses `±π`. -/
theorem csinc_ne_zero_of_mem_closedBall {j : ℤ} {r : ℝ} (hrpi : r < Real.pi)
    {z : ℂ} (hz : z ∈ Metric.closedBall ((j : ℂ) * Real.pi) r) (hzj : z ≠ (j : ℂ) * Real.pi) :
    csinc z ≠ 0 := by
  intro h0
  obtain ⟨m, hm, rfl⟩ := csinc_eq_zero_iff.1 h0
  -- the two lattice points are within `r < π` of each other, so they coincide
  have hdist : ‖(m : ℂ) * Real.pi - (j : ℂ) * Real.pi‖ ≤ r := by
    simpa [Complex.dist_eq] using Metric.mem_closedBall.mp hz
  have hfac : ((m : ℂ) * Real.pi - (j : ℂ) * Real.pi) = ((m - j : ℤ) : ℂ) * Real.pi := by
    push_cast; ring
  rw [hfac, norm_mul, Complex.norm_intCast, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos Real.pi_pos] at hdist
  have hmj : |((m - j : ℤ) : ℝ)| < 1 := by
    by_contra hcon
    push Not at hcon
    have : Real.pi ≤ |((m - j : ℤ) : ℝ)| * Real.pi := by nlinarith [Real.pi_pos]
    linarith
  have hlt : |m - j| < 1 := by exact_mod_cast hmj
  rw [abs_lt] at hlt
  exact hzj (by rw [show m = j by omega])


/-! ### Axiom footprint -/

/-- info: 'Shields.csinc_ofReal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms csinc_ofReal

/-- info: 'Shields.analyticOnNhd_csinc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms analyticOnNhd_csinc

/-- info: 'Shields.deriv_csinc_intCast_mul_pi_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms deriv_csinc_intCast_mul_pi_ne_zero

/-- info: 'Shields.csinc_ne_zero_of_mem_closedBall' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms csinc_ne_zero_of_mem_closedBall

/-- info: 'Shields.csinc_pi_mul_congr_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms csinc_pi_mul_congr_sq

/-- info: 'Shields.sinc_pi_mul_congr_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sinc_pi_mul_congr_sq

end Shields
