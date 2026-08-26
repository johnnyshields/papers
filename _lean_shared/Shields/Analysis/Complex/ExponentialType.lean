/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib.Analysis.Complex.JensenFormula
import Shields.Analysis.Complex.CanonicalProduct

/-!
# Entire functions of exponential type

An entire function has **exponential type** `c` when `‖f z‖ ≤ A exp (c‖z‖)` for some constant `A`.
The point of the definition is what Jensen's inequality then says about the zeros: their number in a
disc of radius `r` grows at most linearly in `r`, with an explicit constant.

## Main results

* `Shields.HasExpType`: the growth bound, with the normalization `1 ≤ A`.
* `Shields.HasExpType.sum_divisor_le`: **the zero-counting bound.**  For `f` entire of exponential
  type `c` with `f 0 ≠ 0`, the number of zeros in `closedBall 0 r`, with multiplicity, is at most
  `(log A + 2cr - log ‖f 0‖) / log 2`.
* `Shields.HasExpType.isBigO_sum_divisor`: the same statement as `n(r) = O(r)`.
* `Shields.hasExpType_canonicalProduct`: a canonical product over a family with summable inverse
  moduli has exponential type `ε` for **every** `ε > 0`, and
  `Shields.isLittleO_sum_divisor_canonicalProduct` turns that into `n(r) = o(r)` for its zeros.

## Implementation notes

`1 ≤ A` is part of the definition rather than a side condition, because
`AnalyticOnNhd.sum_divisor_le` requires its bound to be at least `1` and enlarging `A` weakens
nothing.

The counting bound compares the circle of radius `r` with the circle of radius `2r`; the ratio is
what produces the `log 2` in the denominator.  Any fixed ratio `> 1` would do, and `2` is chosen
because it makes the constant explicit.

Mathlib defines no predicate for exponential type at revision `8e45b05` — `exponentialType` and
`ExponentialType` have no occurrence — and carries no Hadamard factorization
(`Analysis/Complex/Hadamard.lean` is the three-lines theorem).  What it does carry, and what this
file is built on, is Jensen's formula and Jensen's inequality in
`Analysis/Complex/JensenFormula.lean`.

## Tags

entire function, exponential type, order of growth, Jensen inequality, zero counting
-/

open Filter Metric MeromorphicOn Set Topology

namespace Shields

/-- **Exponential type `c`**: `‖f z‖ ≤ A exp (c‖z‖)` for a constant `A ≥ 1`. -/
def HasExpType (f : ℂ → ℂ) (c : ℝ) : Prop :=
  ∃ A : ℝ, 1 ≤ A ∧ ∀ z, ‖f z‖ ≤ A * Real.exp (c * ‖z‖)

/-! ### Closure properties -/

/-- The type may always be increased. -/
theorem HasExpType.mono {f : ℂ → ℂ} {c d : ℝ} (h : HasExpType f c) (hcd : c ≤ d) :
    HasExpType f d := by
  obtain ⟨A, hA, hbd⟩ := h
  refine ⟨A, hA, fun z => (hbd z).trans ?_⟩
  exact mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hcd (norm_nonneg z))) (by linarith)

/-- A constant has exponential type `0`. -/
theorem hasExpType_const (a : ℂ) : HasExpType (fun _ => a) 0 :=
  ⟨max 1 ‖a‖, le_max_left _ _, fun z => by simp⟩

/-- Exponential types add under multiplication. -/
theorem HasExpType.mul {f g : ℂ → ℂ} {c d : ℝ} (hf : HasExpType f c) (hg : HasExpType g d) :
    HasExpType (fun z => f z * g z) (c + d) := by
  obtain ⟨A, hA, hbd⟩ := hf
  obtain ⟨B, hB, hbd'⟩ := hg
  refine ⟨A * B, one_le_mul_of_one_le_of_one_le hA hB, fun z => ?_⟩
  calc ‖f z * g z‖ = ‖f z‖ * ‖g z‖ := norm_mul _ _
    _ ≤ (A * Real.exp (c * ‖z‖)) * (B * Real.exp (d * ‖z‖)) := by
        exact mul_le_mul (hbd z) (hbd' z) (norm_nonneg _)
          (le_trans (norm_nonneg _) (hbd z))
    _ = A * B * Real.exp ((c + d) * ‖z‖) := by
        rw [add_mul, Real.exp_add]; ring

/-- Transport along a pointwise identity. -/
theorem HasExpType.congr {f g : ℂ → ℂ} {c : ℝ} (h : HasExpType f c) (hfg : ∀ z, g z = f z) :
    HasExpType g c := by
  obtain ⟨A, hA, hbd⟩ := h
  exact ⟨A, hA, fun z => by rw [hfg z]; exact hbd z⟩

/-- `exp (a z)` has exponential type `‖a‖`, which is sharp. -/
theorem hasExpType_exp_mul (a : ℂ) : HasExpType (fun z => Complex.exp (a * z)) ‖a‖ := by
  refine ⟨1, le_rfl, fun z => ?_⟩
  rw [Complex.norm_exp, one_mul]
  exact Real.exp_le_exp.mpr ((Complex.re_le_norm _).trans (by rw [norm_mul]))

/-! ### The zero-counting bound

Jensen's inequality bounds the number of zeros in a disc by the growth on a larger disc.  Feeding it
the exponential bound on the circle of radius `2r` gives a count linear in `r`.
-/

/-- **The zero-counting bound for an entire function of exponential type.**  With `f` entire, `f 0 ≠
0`, and `‖f z‖ ≤ A exp (c‖z‖)`, the number of zeros of `f` in `closedBall 0 r` counted with
multiplicity is at most `(log A + 2cr - log ‖f 0‖) / log 2`.

The constant is explicit rather than asymptotic because the comparison radius is fixed at `2r`. -/
theorem HasExpType.sum_divisor_le {f : ℂ → ℂ} {c A : ℝ} (hc : 0 ≤ c) (hA : 1 ≤ A)
    (hbd : ∀ z, ‖f z‖ ≤ A * Real.exp (c * ‖z‖))
    (hf : Differentiable ℂ f) (hf0 : f 0 ≠ 0) {r : ℝ} (hr : 0 < r) :
    ((∑ᶠ u, divisor f (closedBall (0 : ℂ) r) u : ℤ) : ℝ)
      ≤ (Real.log A + 2 * c * r - Real.log ‖f 0‖) / Real.log 2 := by
  have hR : (0 : ℝ) < 2 * r := by linarith
  have habsr : |r| = r := abs_of_pos hr
  have habsR : |2 * r| = 2 * r := abs_of_pos hR
  set M : ℝ := A * Real.exp (c * (2 * r)) with hM
  have hM1 : 1 ≤ M := by
    rw [hM]
    have : (1 : ℝ) ≤ Real.exp (c * (2 * r)) := Real.one_le_exp (by positivity)
    nlinarith
  have hana : AnalyticOnNhd ℂ f (closedBall (0 : ℂ) |2 * r|) := fun z _ =>
    hf.analyticAt z
  have hbound : ∀ z ∈ sphere (0 : ℂ) |2 * r|, ‖f z‖ ≤ M := by
    intro z hz
    have hznorm : ‖z‖ = 2 * r := by
      rw [mem_sphere_iff_norm, sub_zero] at hz
      rw [hz, habsR]
    rw [hM, ← hznorm]
    exact hbd z
  have key := AnalyticOnNhd.sum_divisor_le (c := (0 : ℂ)) (r := r) (R := 2 * r) (M := M)
    (by rw [habsr]; exact hr) (by rw [habsr, habsR]; linarith) hM1 hana hf0 hbound
  rw [habsr] at key
  refine key.trans ?_
  have hratio : 2 * r / r = 2 := by field_simp
  rw [hratio, hM]
  have hexp : Real.log (A * Real.exp (c * (2 * r))) = Real.log A + 2 * c * r := by
    rw [Real.log_mul (by linarith) (Real.exp_ne_zero _), Real.log_exp]
    ring
  rw [Real.log_div (by positivity) (norm_ne_zero_iff.mpr hf0), hexp]

/-- The counting bound with the constant packaged: a linear bound in `r`. -/
theorem HasExpType.exists_sum_divisor_le {f : ℂ → ℂ} {c : ℝ} (hc : 0 ≤ c) (h : HasExpType f c)
    (hf : Differentiable ℂ f) (hf0 : f 0 ≠ 0) :
    ∃ B : ℝ, ∀ r : ℝ, 0 < r →
      ((∑ᶠ u, divisor f (closedBall (0 : ℂ) r) u : ℤ) : ℝ)
        ≤ B + (2 * c / Real.log 2) * r := by
  obtain ⟨A, hA, hbd⟩ := h
  refine ⟨(Real.log A - Real.log ‖f 0‖) / Real.log 2, fun r hr => ?_⟩
  refine (HasExpType.sum_divisor_le hc hA hbd hf hf0 hr).trans (le_of_eq ?_)
  have hl : (0 : ℝ) < Real.log 2 := Real.log_pos one_lt_two
  field

/-- The zero count is nonnegative: an analytic function has a nonnegative divisor. -/
theorem sum_divisor_nonneg {f : ℂ → ℂ} (hf : Differentiable ℂ f) {r : ℝ} :
    0 ≤ ((∑ᶠ u, divisor f (closedBall (0 : ℂ) r) u : ℤ) : ℝ) := by
  have hana : AnalyticOnNhd ℂ f (closedBall (0 : ℂ) r) := fun z _ => hf.analyticAt z
  exact_mod_cast finsum_nonneg fun u => hana.divisor_nonneg u

/-- **The zero count of an entire function of exponential type is `O(r)`.** -/
theorem HasExpType.isBigO_sum_divisor {f : ℂ → ℂ} {c : ℝ} (hc : 0 ≤ c) (h : HasExpType f c)
    (hf : Differentiable ℂ f) (hf0 : f 0 ≠ 0) :
    (fun r : ℝ => ((∑ᶠ u, divisor f (closedBall (0 : ℂ) r) u : ℤ) : ℝ)) =O[atTop]
      fun r : ℝ => r := by
  obtain ⟨B, hB⟩ := h.exists_sum_divisor_le hc hf hf0
  refine Asymptotics.isBigO_iff.mpr ⟨|B| + 2 * c / Real.log 2, ?_⟩
  filter_upwards [eventually_gt_atTop (0 : ℝ), eventually_ge_atTop (1 : ℝ)] with r hr hr1
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sum_divisor_nonneg hf),
    abs_of_pos hr]
  refine (hB r hr).trans ?_
  have h1 : B ≤ |B| * r := le_trans (le_abs_self B) (le_mul_of_one_le_right (abs_nonneg B) hr1)
  have h2 : (0 : ℝ) ≤ 2 * c / Real.log 2 := by
    have := Real.log_pos one_lt_two
    positivity
  nlinarith

/-! ### The canonical product

A canonical product over a family with summable inverse moduli has *minimal* exponential type:
every positive `ε` is a type.  Its zero count is therefore `o(r)`.
-/

variable {a : ℕ → ℂ}

/-- **A canonical product has every positive exponential type.** -/
theorem hasExpType_canonicalProduct (ha : ∀ n, a n ≠ 0) (hsum : Summable fun n => ‖a n‖⁻¹)
    {ε : ℝ} (hε : 0 < ε) : HasExpType (canonicalProduct a) ε := by
  obtain ⟨M, hM, hbd⟩ := exists_bound_of_minimalType ha hsum hε
  refine ⟨max 1 M, le_max_left _ _, fun z => (hbd z).trans ?_⟩
  exact mul_le_mul_of_nonneg_right (le_max_right 1 M) (Real.exp_nonneg _)

/-- **The zero count of a canonical product is `o(r)`.**  The bound is `2ε/log 2` for every
`ε > 0`, so the limit superior of `n(r)/r` is `0`. -/
theorem isLittleO_sum_divisor_canonicalProduct (ha : ∀ n, a n ≠ 0)
    (hsum : Summable fun n => ‖a n‖⁻¹) :
    (fun r : ℝ => ((∑ᶠ u, divisor (canonicalProduct a) (closedBall (0 : ℂ) r) u : ℤ) : ℝ))
      =o[atTop] fun r : ℝ => r := by
  have hdiff : Differentiable ℂ (canonicalProduct a) := differentiable_canonicalProduct hsum
  have hne : canonicalProduct a 0 ≠ 0 :=
    canonicalProduct_ne_zero ha hsum fun n => ha n
  rw [Asymptotics.isLittleO_iff]
  intro δ hδ
  -- choose `ε` so that `2ε/log 2 ≤ δ/2`
  set ε : ℝ := δ * Real.log 2 / 8 with hεdef
  have hlog : (0 : ℝ) < Real.log 2 := Real.log_pos one_lt_two
  have hε : 0 < ε := by rw [hεdef]; positivity
  obtain ⟨B, hB⟩ := (hasExpType_canonicalProduct ha hsum hε).exists_sum_divisor_le hε.le hdiff hne
  have hcoef : 2 * ε / Real.log 2 = δ / 4 := by
    rw [hεdef]; field_simp; ring
  filter_upwards [eventually_gt_atTop (0 : ℝ), eventually_ge_atTop (4 * |B| / δ)] with r hr hrB
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sum_divisor_nonneg hdiff),
    abs_of_pos hr]
  refine (hB r hr).trans ?_
  rw [hcoef]
  have h1 : B ≤ δ / 4 * r := by
    refine le_trans (le_abs_self B) ?_
    rw [div_le_iff₀ hδ] at hrB
    nlinarith [abs_nonneg B]
  nlinarith

/-! ### Axiom footprint -/

/-- info: 'Shields.HasExpType.sum_divisor_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HasExpType.sum_divisor_le

/-- info: 'Shields.isLittleO_sum_divisor_canonicalProduct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms isLittleO_sum_divisor_canonicalProduct

end Shields
