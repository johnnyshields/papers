/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import TuranBessel.Digamma

/-!
# Gamma-ratio asymptotics, and the exact inputs to `lem:central-moments`

Formalizes `shields-2026-turan-bessel.tex`, «Critical wall fan and equivalence of
ensembles» (`sec:scaling`, `lem:central-moments`, `eq:Sm-asymptotic`,
`eq:hypergeom-moments`).

`Scaling.sweight_eq_gamma_ratio` is the exact identity `eq:Sm-gamma-ratio`; what
the paper then quotes from DLMF §5.11(iii) is the expansion of the two gamma
ratios it leaves behind,

```
  S_m = C_a (4^m/(m!)²) m^b (1 + s_a/m + O_a(m^{-2})),
  C_a = 2^{2a-2}/√π,  b = 3/2 - 2a,  s_a = -2a² + 5a/2 - 5/8.
```

The route here is elementary and carries written-out constants rather than an
`O`-symbol.

* `Λ(t) = t log t - t - (log t)/2 + 1/(12t)` has derivative exactly
  `log t - 1/(2t) - 1/(12t²)`, so `log Γ - Λ` has derivative the digamma gap of
  `Digamma.digamma_sandwich`.  That gap is nonnegative and at most `1/(60t³)`, so
  `log Γ - Λ` is monotone and `log Γ - Λ + 1/(120t²)` is antitone: for `0<x≤y`,
  `0 ≤ (log Γ(y) - log Γ(x)) - (Λ(y) - Λ(x)) ≤ 1/(120x²)`.  Stirling's additive
  constant never appears, because only differences are ever taken.
* `Λ(m+c) = Λ(m) + c log m + W(m,c)` is an identity, with
  `W(m,c) = (m+c-1/2)log(1+c/m) - c + 1/(12(m+c)) - 1/(12m)`, and
  `|W(m,c) - (c²-c)/(2m)| ≤ 5(|c|+1)³/m²` once `m ≥ 4|c|+4`, from Mathlib's
  `Real.abs_log_sub_add_sum_range_le` at two terms.
* The four shifts `a-1/2, a, 1, 2a-1` of `eq:Sm-gamma-ratio` carry signs
  `+,-,+,-`.  Their signed sum is `0`, which is why the `m log m` terms and the
  Stirling constant both cancel; `Σεc = b` gives the exponent and
  `Σε(c²-c)/2 = s_a` the `1/m` coefficient.

`scripts/check_gamma_ratio_expansion.py` measures each of these steps and the
final constants against the exact `S_m`.

The last section is the other exact input to `lem:central-moments`: the variance
`n²/(4(2n-1))` of the symmetric hypergeometric base law `eq:hypergeom-moments`,
from Chu–Vandermonde.  Everything else in `lem:central-moments` — the fourth and
sixth moments, `eq:tilt-comparison`, `eq:tilted-tail` — rests on Hoeffding's
sampling-without-replacement inequality, which Mathlib does not carry, and is not
attempted.

Sorry-free.
-/

namespace TuranBessel

open Filter Topology

variable {x y c m : ℝ}

/-! ### Stirling's three-term primitive -/

/-- `Λ(t) = t log t - t - (log t)/2 + 1/(12t)`, a primitive of the three-term
asymptotic form of `ψ`.  Stirling's additive constant is deliberately absent: every
use below is a difference, in which it would cancel. -/
noncomputable def stirlingLam (t : ℝ) : ℝ :=
  t * Real.log t - t - Real.log t / 2 + 1 / (12 * t)

theorem hasDerivAt_stirlingLam (hx : 0 < x) :
    HasDerivAt stirlingLam (Real.log x - 1 / (2 * x) - 1 / (12 * x ^ 2)) x := by
  have hne : x ≠ 0 := hx.ne'
  have hlog : HasDerivAt Real.log x⁻¹ x := Real.hasDerivAt_log hne
  have h1 : HasDerivAt (fun t : ℝ => t * Real.log t) (Real.log x + 1) x := by
    refine ((hasDerivAt_id x).mul hlog).congr_deriv ?_
    simp only [id_eq]
    field_simp
  have h2 : HasDerivAt (fun t : ℝ => Real.log t / 2) (1 / (2 * x)) x := by
    refine (hlog.div_const 2).congr_deriv ?_
    field_simp
  have h3 : HasDerivAt (fun t : ℝ => 1 / (12 * t)) (-(1 / (12 * x ^ 2))) x := by
    have hg : HasDerivAt (fun t : ℝ => 12 * t) 12 x := by
      simpa using (hasDerivAt_id x).const_mul (12 : ℝ)
    have h12 : (12 : ℝ) * x ≠ 0 := by positivity
    refine ((hasDerivAt_const x (1 : ℝ)).div hg h12).congr_deriv ?_
    field
  refine (((h1.sub (hasDerivAt_id x)).sub h2).add h3).congr_deriv ?_
  ring

/-- `log Γ - Λ`, the quantity whose differences are the Stirling sandwich. -/
noncomputable def stirlingGap (t : ℝ) : ℝ := Real.log (Real.Gamma t) - stirlingLam t

theorem hasDerivAt_stirlingGap (hx : 0 < x) :
    HasDerivAt stirlingGap (digammaGap x) x := by
  have hlg : HasDerivAt (fun t : ℝ => Real.log (Real.Gamma t)) (realDigamma x) x :=
    (differentiableAt_log_Gamma hx).hasDerivAt
  refine (hlg.sub (hasDerivAt_stirlingLam hx)).congr_deriv ?_
  rw [digammaGap]
  ring

theorem stirlingGap_monotoneOn : MonotoneOn stirlingGap (Set.Ioi (0 : ℝ)) := by
  refine monotoneOn_of_deriv_nonneg (convex_Ioi 0) (fun t ht => ?_) (fun t ht => ?_)
    (fun t ht => ?_)
  · exact (hasDerivAt_stirlingGap (Set.mem_Ioi.1 ht)).continuousAt.continuousWithinAt
  · rw [interior_Ioi] at ht
    exact (hasDerivAt_stirlingGap (Set.mem_Ioi.1 ht)).differentiableAt.differentiableWithinAt
  · rw [interior_Ioi] at ht
    have ht0 : (0 : ℝ) < t := Set.mem_Ioi.1 ht
    rw [(hasDerivAt_stirlingGap ht0).deriv]
    exact digammaGap_nonneg ht0

/-- The gap with the remainder added; antitone rather than monotone. -/
noncomputable def stirlingGap' (t : ℝ) : ℝ := stirlingGap t + 1 / (120 * t ^ 2)

theorem hasDerivAt_stirlingGap' (hx : 0 < x) :
    HasDerivAt stirlingGap' (digammaGap x - 1 / (60 * x ^ 3)) x := by
  have hg : HasDerivAt (fun t : ℝ => 120 * t ^ 2) (240 * x) x := by
    refine ((hasDerivAt_pow 2 x).const_mul (120 : ℝ)).congr_deriv ?_
    push_cast
    ring
  have h120 : (120 : ℝ) * x ^ 2 ≠ 0 := by positivity
  have h2 : HasDerivAt (fun t : ℝ => 1 / (120 * t ^ 2)) (-(1 / (60 * x ^ 3))) x := by
    refine ((hasDerivAt_const x (1 : ℝ)).div hg h120).congr_deriv ?_
    field
  refine ((hasDerivAt_stirlingGap hx).add h2).congr_deriv ?_
  ring

theorem stirlingGap'_antitoneOn : AntitoneOn stirlingGap' (Set.Ioi (0 : ℝ)) := by
  refine antitoneOn_of_deriv_nonpos (convex_Ioi 0) (fun t ht => ?_) (fun t ht => ?_)
    (fun t ht => ?_)
  · exact (hasDerivAt_stirlingGap' (Set.mem_Ioi.1 ht)).continuousAt.continuousWithinAt
  · rw [interior_Ioi] at ht
    exact (hasDerivAt_stirlingGap' (Set.mem_Ioi.1 ht)).differentiableAt.differentiableWithinAt
  · rw [interior_Ioi] at ht
    have ht0 : (0 : ℝ) < t := Set.mem_Ioi.1 ht
    rw [(hasDerivAt_stirlingGap' ht0).deriv]
    linarith [digammaGap_le ht0]

/-- **The two-point Stirling sandwich.**  For `0 < x ≤ y`,
`0 ≤ (log Γ(y) - log Γ(x)) - (Λ(y) - Λ(x)) ≤ 1/(120x²)`.  The additive constant of
Stirling's series is not needed, and not identified. -/
theorem stirling_diff_sandwich (hx : 0 < x) (hxy : x ≤ y) :
    0 ≤ stirlingGap y - stirlingGap x ∧ stirlingGap y - stirlingGap x ≤ 1 / (120 * x ^ 2) := by
  have hy : (0 : ℝ) < y := lt_of_lt_of_le hx hxy
  refine ⟨?_, ?_⟩
  · have := stirlingGap_monotoneOn (Set.mem_Ioi.2 hx) (Set.mem_Ioi.2 hy) hxy
    linarith
  · have h := stirlingGap'_antitoneOn (Set.mem_Ioi.2 hx) (Set.mem_Ioi.2 hy) hxy
    rw [stirlingGap', stirlingGap'] at h
    have hpos : (0 : ℝ) < 1 / (120 * y ^ 2) :=
      div_pos one_pos (by positivity)
    linarith

/-- The sandwich in absolute-value form, against a common lower bound on the two
points, which is what the four-shift assembly needs. -/
theorem abs_stirlingGap_sub_le (hc : 0 < c) (hx : c ≤ x) (hy : c ≤ y) :
    |stirlingGap y - stirlingGap x| ≤ 1 / (120 * c ^ 2) := by
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le hc hx
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le hc hy
  have hmono : ∀ z : ℝ, c ≤ z → 1 / (120 * z ^ 2) ≤ 1 / (120 * c ^ 2) := by
    intro z hz
    have hz0 : (0 : ℝ) < z := lt_of_lt_of_le hc hz
    refine alg_div_le (by positivity) (by positivity) ?_
    nlinarith [hc, hz]
  rcases le_total x y with h | h
  · obtain ⟨h1, h2⟩ := stirling_diff_sandwich hx0 h
    rw [abs_of_nonneg h1]
    exact le_trans h2 (hmono x hx)
  · obtain ⟨h1, h2⟩ := stirling_diff_sandwich hy0 h
    rw [abs_of_nonpos (by linarith)]
    have := le_trans h2 (hmono y hy)
    linarith

/-! ### The per-shift expansion -/

private theorem abs_sub_le_add (p q : ℝ) : |p - q| ≤ |p| + |q| := by
  rw [sub_eq_add_neg]
  refine le_trans (abs_add_le _ _) ?_
  rw [abs_neg]

/-- `W(m,c) = (m+c-1/2)log(1+c/m) - c + 1/(12(m+c)) - 1/(12m)`, the whole
`m`-dependence of `Λ(m+c) - Λ(m) - c log m`. -/
noncomputable def shiftRem (m c : ℝ) : ℝ :=
  (m + c - 1 / 2) * Real.log (1 + c / m) - c + 1 / (12 * (m + c)) - 1 / (12 * m)

/-- **`Λ(m+c) = Λ(m) + c log m + W(m,c)`**: an identity, not an estimate.  It is what
makes both `Λ(m)` and the Stirling constant cancel in a signed sum whose signs add
to zero. -/
theorem stirlingLam_add (hm : 0 < m) (hmc : 0 < m + c) :
    stirlingLam (m + c) = stirlingLam m + c * Real.log m + shiftRem m c := by
  have h1c : (0 : ℝ) < 1 + c / m := by
    rw [show (1 : ℝ) + c / m = (m + c) / m from by field_simp]
    exact div_pos hmc hm
  have hfac : m + c = m * (1 + c / m) := by field_simp
  have hlog : Real.log (m + c) = Real.log m + Real.log (1 + c / m) := by
    rw [hfac, Real.log_mul hm.ne' h1c.ne']
  simp only [stirlingLam, shiftRem, hlog]
  ring

/-- Two terms of `log(1+c/m)` with the remainder written out, from Mathlib's
`Real.abs_log_sub_add_sum_range_le` at `n = 2`. -/
theorem abs_log_one_add_div_sub (hm : 4 * |c| + 4 ≤ m) :
    |Real.log (1 + c / m) - (c / m - c ^ 2 / (2 * m ^ 2))| ≤ 2 * |c| ^ 3 / m ^ 3 := by
  have hca : (0 : ℝ) ≤ |c| := abs_nonneg c
  have hm0 : (0 : ℝ) < m := by linarith
  have hm3 : (0 : ℝ) < m ^ 3 := pow_pos hm0 3
  set u : ℝ := -c / m with hu
  have habs : |u| = |c| / m := by rw [hu, abs_div, abs_neg, abs_of_pos hm0]
  have hq : |c| / m ≤ 1 / 4 := by
    rw [div_le_div_iff₀ hm0 (by norm_num : (0:ℝ) < 4)]; linarith
  have hlt : |u| < 1 := by rw [habs]; linarith
  have h := Real.abs_log_sub_add_sum_range_le hlt 2
  have hsum : (∑ i ∈ Finset.range 2, u ^ (i + 1) / ((i : ℝ) + 1)) = u + u ^ 2 / 2 := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    norm_num
  have hone : (1 : ℝ) - u = 1 + c / m := by rw [hu]; ring
  rw [hsum, hone] at h
  have hlhs : u + u ^ 2 / 2 + Real.log (1 + c / m)
      = Real.log (1 + c / m) - (c / m - c ^ 2 / (2 * m ^ 2)) := by
    rw [hu]; field_simp; ring
  rw [hlhs] at h
  refine le_trans h ?_
  -- `|u|³/(1-|u|) ≤ 2|c|³/m³`, since `1-|u| ≥ 3/4`
  have hden : (3 : ℝ) / 4 ≤ 1 - |u| := by rw [habs]; linarith
  have hnum : |u| ^ 3 = |c| ^ 3 / m ^ 3 := by
    rw [habs, div_pow]
  rw [hnum]
  refine alg_div_le (by linarith) hm3 ?_
  have hc3 : (0 : ℝ) ≤ |c| ^ 3 := by positivity
  have hcancel : |c| ^ 3 / m ^ 3 * m ^ 3 = |c| ^ 3 := by field_simp
  rw [hcancel]
  nlinarith [hc3, hden]

/-- **The per-shift bound.**  `|W(m,c) - (c²-c)/(2m)| ≤ 5(|c|+1)³/m²` once
`m ≥ 4|c|+4`.  The three contributions are the second-order part of the exact
product, the `1/(12t)` difference, and the log remainder. -/
theorem abs_shiftRem_sub_le (hm : 4 * |c| + 4 ≤ m) :
    |shiftRem m c - (c ^ 2 - c) / (2 * m)| ≤ 5 * (|c| + 1) ^ 3 / m ^ 2 := by
  have hca : (0 : ℝ) ≤ |c| := abs_nonneg c
  have hm0 : (0 : ℝ) < m := by linarith
  have hm2 : (0 : ℝ) < m ^ 2 := pow_pos hm0 2
  have hm3 : (0 : ℝ) < m ^ 3 := pow_pos hm0 3
  have hcup : c ≤ |c| := le_abs_self c
  have hclow : -|c| ≤ c := neg_abs_le c
  have hmc : 3 * m / 4 ≤ m + c := by linarith
  have hmc0 : (0 : ℝ) < m + c := by linarith
  set A : ℝ := (|c| + 1) ^ 3 with hA
  have hA0 : (0 : ℝ) < A := by rw [hA]; positivity
  have hA1 : c ^ 2 ≤ A := by rw [hA]; nlinarith [sq_abs c, hca]
  have hA2 : |c| ^ 3 ≤ A := by rw [hA]; nlinarith [hca]
  have hA3 : |c| ≤ A := by rw [hA]; nlinarith [hca]
  set r : ℝ := Real.log (1 + c / m) - (c / m - c ^ 2 / (2 * m ^ 2)) with hrdef
  have hrb : |r| ≤ 2 * |c| ^ 3 / m ^ 3 := abs_log_one_add_div_sub hm
  have hlogeq : Real.log (1 + c / m) = r + (c / m - c ^ 2 / (2 * m ^ 2)) := by
    rw [hrdef]; ring
  have hid : shiftRem m c - (c ^ 2 - c) / (2 * m)
      = (c ^ 2 / 4 - c ^ 3 / 2) / m ^ 2 - c / (12 * m * (m + c)) + (m + c - 1 / 2) * r := by
    rw [shiftRem, hlogeq]
    field
  -- the three pieces
  have hb1 : |(c ^ 2 / 4 - c ^ 3 / 2) / m ^ 2| ≤ 3 / 4 * A / m ^ 2 := by
    rw [abs_div, abs_of_pos hm2]
    refine alg_div_le hm2 hm2 ?_
    have e1 : |c ^ 2 / 4| = c ^ 2 / 4 := abs_of_nonneg (by positivity)
    have e2 : |c ^ 3 / 2| = |c| ^ 3 / 2 := by
      rw [abs_div, abs_pow, abs_of_nonneg (by norm_num : (0:ℝ) ≤ (2:ℝ))]
    have h1 : |c ^ 2 / 4 - c ^ 3 / 2| ≤ c ^ 2 / 4 + |c| ^ 3 / 2 := by
      have := abs_sub_le_add (c ^ 2 / 4) (c ^ 3 / 2)
      rw [e1, e2] at this
      exact this
    have h2 : |c ^ 2 / 4 - c ^ 3 / 2| ≤ 3 / 4 * A := by linarith
    exact mul_le_mul_of_nonneg_right h2 hm2.le
  have hden : (0 : ℝ) < 12 * m * (m + c) :=
    mul_pos (mul_pos (by norm_num) hm0) hmc0
  have hb2 : |c / (12 * m * (m + c))| ≤ A / (9 * m ^ 2) := by
    rw [abs_div, abs_of_pos hden]
    refine alg_div_le hden (by linarith) ?_
    have s0 : m * (3 * m / 4) ≤ m * (m + c) := mul_le_mul_of_nonneg_left hmc hm0.le
    have s1 : 9 * m ^ 2 ≤ 12 * m * (m + c) := by nlinarith [s0]
    have s2 : |c| * (9 * m ^ 2) ≤ A * (9 * m ^ 2) :=
      mul_le_mul_of_nonneg_right hA3 (by linarith)
    have s3 : A * (9 * m ^ 2) ≤ A * (12 * m * (m + c)) :=
      mul_le_mul_of_nonneg_left s1 hA0.le
    linarith
  have hb3 : |(m + c - 1 / 2) * r| ≤ 5 / 2 * A / m ^ 2 := by
    rw [abs_mul, abs_of_nonneg (by linarith : (0:ℝ) ≤ m + c - 1 / 2)]
    have hup : m + c - 1 / 2 ≤ 5 * m / 4 := by linarith
    have hstep : (m + c - 1 / 2) * |r| ≤ 5 * m / 4 * (2 * |c| ^ 3 / m ^ 3) :=
      mul_le_mul hup hrb (abs_nonneg r) (by linarith)
    refine le_trans hstep ?_
    have heq : 5 * m / 4 * (2 * |c| ^ 3 / m ^ 3) = 5 / 2 * |c| ^ 3 / m ^ 2 := by
      field_simp; ring
    rw [heq]
    refine alg_div_le hm2 hm2 ?_
    exact mul_le_mul_of_nonneg_right (by linarith : (5:ℝ) / 2 * |c| ^ 3 ≤ 5 / 2 * A) hm2.le
  -- assemble
  have hsum : |shiftRem m c - (c ^ 2 - c) / (2 * m)|
      ≤ 3 / 4 * A / m ^ 2 + A / (9 * m ^ 2) + 5 / 2 * A / m ^ 2 := by
    rw [hid]
    refine le_trans (abs_add_le _ _) ?_
    have h12 := abs_sub_le_add ((c ^ 2 / 4 - c ^ 3 / 2) / m ^ 2) (c / (12 * m * (m + c)))
    linarith
  refine le_trans hsum ?_
  have h9 : A / (9 * m ^ 2) ≤ A / m ^ 2 / 9 := by
    rw [div_div]
    refine alg_div_le (by linarith) (by linarith) ?_
    nlinarith [hA0, hm2]
  have hfin : 3 / 4 * A / m ^ 2 + A / m ^ 2 / 9 + 5 / 2 * A / m ^ 2 ≤ 5 * A / m ^ 2 := by
    have : (0 : ℝ) < A / m ^ 2 := div_pos hA0 hm2
    have e : 3 / 4 * A / m ^ 2 = 3 / 4 * (A / m ^ 2) := by ring
    have e2 : 5 / 2 * A / m ^ 2 = 5 / 2 * (A / m ^ 2) := by ring
    have e3 : 5 * A / m ^ 2 = 5 * (A / m ^ 2) := by ring
    rw [e, e2, e3]
    linarith
  linarith

/-! ### The four-shift assembly

`eq:Sm-gamma-ratio` leaves four gammas at shifts `c₁,c₂,c₃,c₄` carrying signs
`+,-,+,-`.  Because the signs add to zero, `Λ(m)` cancels — and with it Stirling's
additive constant, which is why none of this needs the constant identified.  What
survives is `(Σεc)log m` and `Σε W(m,c)`, and the latter is `(Σε(c²-c)/2)/m` to
order `m⁻²`. -/

theorem abs_four_shift_sub_le {M d₁ d₂ d₃ d₄ B : ℝ} (hM : 0 < M)
    (h₁ : 4 * |d₁| + 4 ≤ M) (h₂ : 4 * |d₂| + 4 ≤ M)
    (h₃ : 4 * |d₃| + 4 ≤ M) (h₄ : 4 * |d₄| + 4 ≤ M)
    (hB₁ : |d₁| ≤ B) (hB₂ : |d₂| ≤ B) (hB₃ : |d₃| ≤ B) (hB₄ : |d₄| ≤ B)
    (hBM : 2 * B ≤ M) :
    |(Real.log (Real.Gamma (M + d₁)) - Real.log (Real.Gamma (M + d₂))
        + (Real.log (Real.Gamma (M + d₃)) - Real.log (Real.Gamma (M + d₄)))
        - (d₁ - d₂ + d₃ - d₄) * Real.log M)
      - ((d₁ ^ 2 - d₁) - (d₂ ^ 2 - d₂) + (d₃ ^ 2 - d₃) - (d₄ ^ 2 - d₄)) / (2 * M)|
      ≤ (20 * (B + 1) ^ 3 + 1 / 15) / M ^ 2 := by
  have hM2 : (0 : ℝ) < M ^ 2 := pow_pos hM 2
  have hB0 : (0 : ℝ) ≤ B := le_trans (abs_nonneg d₁) hB₁
  have hhalf : ∀ d : ℝ, |d| ≤ B → M / 2 ≤ M + d := by
    intro d hd
    have := neg_abs_le d
    linarith
  have hposd : ∀ d : ℝ, |d| ≤ B → 0 < M + d := by
    intro d hd
    exact lt_of_lt_of_le (by linarith) (hhalf d hd)
  -- each `log Γ` split into gap + primitive
  have hsplit : ∀ d : ℝ, |d| ≤ B →
      Real.log (Real.Gamma (M + d))
        = stirlingGap (M + d) + (stirlingLam M + d * Real.log M + shiftRem M d) := by
    intro d hd
    have h := stirlingLam_add (m := M) (c := d) hM (hposd d hd)
    rw [stirlingGap, ← h]
    ring
  -- the gap part
  have hMhalf : (0 : ℝ) < M / 2 := by linarith
  have hval : 1 / (120 * (M / 2) ^ 2) = 1 / (30 * M ^ 2) := by
    rw [div_pow]; field_simp; ring
  have b1 := abs_stirlingGap_sub_le (c := M / 2) (x := M + d₂) (y := M + d₁)
    hMhalf (hhalf d₂ hB₂) (hhalf d₁ hB₁)
  have b2 := abs_stirlingGap_sub_le (c := M / 2) (x := M + d₄) (y := M + d₃)
    hMhalf (hhalf d₄ hB₄) (hhalf d₃ hB₃)
  rw [hval] at b1 b2
  rw [abs_le] at b1 b2
  -- the `W` part
  have hwb : ∀ d : ℝ, 4 * |d| + 4 ≤ M → |d| ≤ B →
      |shiftRem M d - (d ^ 2 - d) / (2 * M)| ≤ 5 * (B + 1) ^ 3 / M ^ 2 := by
    intro d hd hdB
    refine le_trans (abs_shiftRem_sub_le hd) ?_
    refine alg_div_le hM2 hM2 ?_
    have hcube : (|d| + 1) ^ 3 ≤ (B + 1) ^ 3 :=
      pow_le_pow_left₀ (by linarith [abs_nonneg d]) (by linarith) 3
    nlinarith [hM2, hcube]
  have w1 := hwb d₁ h₁ hB₁
  have w2 := hwb d₂ h₂ hB₂
  have w3 := hwb d₃ h₃ hB₃
  have w4 := hwb d₄ h₄ hB₄
  rw [abs_le] at w1 w2 w3 w4
  -- assemble
  have hid : (Real.log (Real.Gamma (M + d₁)) - Real.log (Real.Gamma (M + d₂))
        + (Real.log (Real.Gamma (M + d₃)) - Real.log (Real.Gamma (M + d₄)))
        - (d₁ - d₂ + d₃ - d₄) * Real.log M)
      - ((d₁ ^ 2 - d₁) - (d₂ ^ 2 - d₂) + (d₃ ^ 2 - d₃) - (d₄ ^ 2 - d₄)) / (2 * M)
      = ((stirlingGap (M + d₁) - stirlingGap (M + d₂))
          + (stirlingGap (M + d₃) - stirlingGap (M + d₄)))
        + ((shiftRem M d₁ - (d₁ ^ 2 - d₁) / (2 * M))
            - (shiftRem M d₂ - (d₂ ^ 2 - d₂) / (2 * M))
            + (shiftRem M d₃ - (d₃ ^ 2 - d₃) / (2 * M))
            - (shiftRem M d₄ - (d₄ ^ 2 - d₄) / (2 * M))) := by
    rw [hsplit d₁ hB₁, hsplit d₂ hB₂, hsplit d₃ hB₃, hsplit d₄ hB₄]
    field
  rw [hid, abs_le]
  have hbig : 5 * (B + 1) ^ 3 / M ^ 2 * 4 + 1 / (30 * M ^ 2) * 2
      ≤ (20 * (B + 1) ^ 3 + 1 / 15) / M ^ 2 := by
    have he : 5 * (B + 1) ^ 3 / M ^ 2 * 4 + 1 / (30 * M ^ 2) * 2
        = (20 * (B + 1) ^ 3 + 1 / 15) / M ^ 2 := by field_simp; ring
    linarith [he]
  constructor <;> linarith

/-! ### `eq:Sm-asymptotic` -/

/-- `C_a = 2^{2a-2}/√π`, the constant of `eq:Sm-asymptotic`.  It is the prefactor of
the exact identity `eq:Sm-gamma-ratio`, not an asymptotic constant: the gamma-ratio
product below tends to `1` after division by `m^b`. -/
noncomputable def smConst (a : ℝ) : ℝ := (2 : ℝ) ^ (2 * a - 2) / Real.sqrt Real.pi

/-- `b = 3/2 - 2a`, the exponent of `eq:Sm-asymptotic`; the signed sum of the four
shifts of `eq:Sm-gamma-ratio`. -/
noncomputable def smExp (a : ℝ) : ℝ := 3 / 2 - 2 * a

/-- `s_a = -2a² + 5a/2 - 5/8`, the `1/m` coefficient of `eq:Sm-asymptotic`; the signed
sum of `(c²-c)/2` over those shifts. -/
noncomputable def smCoef (a : ℝ) : ℝ := -2 * a ^ 2 + 5 / 2 * a - 5 / 8

/-- The pair of gamma ratios `eq:Sm-gamma-ratio` leaves behind. -/
noncomputable def gammaRatioFactor (a s : ℝ) : ℝ :=
  Real.Gamma (a + s - 1 / 2) / Real.Gamma (a + s)
    * (Real.Gamma (s + 1) / Real.Gamma (2 * a + s - 1))

/-- The four gamma arguments of `gammaRatioFactor` are positive above the threshold, so
the product is. -/
theorem gammaRatioFactor_pos {a s : ℝ} (h₁ : 0 < a + s - 1 / 2) (h₂ : 0 < a + s)
    (h₃ : 0 < s + 1) (h₄ : 0 < 2 * a + s - 1) : 0 < gammaRatioFactor a s := by
  rw [gammaRatioFactor]
  exact mul_pos (div_pos (Real.Gamma_pos_of_pos h₁) (Real.Gamma_pos_of_pos h₂))
    (div_pos (Real.Gamma_pos_of_pos h₃) (Real.Gamma_pos_of_pos h₄))

/-- `log G(a,s)` is the signed sum of `log Γ` over the four shifts of
`eq:Sm-gamma-ratio`.  This is what turns the product into the four-shift Stirling
difference the expansion is read off. -/
theorem log_gammaRatioFactor {a s : ℝ} (h₁ : 0 < a + s - 1 / 2) (h₂ : 0 < a + s)
    (h₃ : 0 < s + 1) (h₄ : 0 < 2 * a + s - 1) :
    Real.log (gammaRatioFactor a s)
      = Real.log (Real.Gamma (a + s - 1 / 2)) - Real.log (Real.Gamma (a + s))
        + (Real.log (Real.Gamma (s + 1)) - Real.log (Real.Gamma (2 * a + s - 1))) := by
  have g1 := Real.Gamma_pos_of_pos h₁
  have g2 := Real.Gamma_pos_of_pos h₂
  have g3 := Real.Gamma_pos_of_pos h₃
  have g4 := Real.Gamma_pos_of_pos h₄
  rw [gammaRatioFactor, Real.log_mul (div_pos g1 g2).ne' (div_pos g3 g4).ne',
    Real.log_div g1.ne' g2.ne', Real.log_div g3.ne' g4.ne']

/-- The `1/t` coefficient of `eq:Sm-asymptotic` is bounded by the same `(a+2)` scale the
remainder is written in. -/
theorem abs_smCoef_le {a : ℝ} (ha : 0 < a) : |smCoef a| ≤ 3 * (a + 2) ^ 2 := by
  rw [smCoef]
  exact abs_le.2 ⟨by nlinarith [sq_nonneg a], by nlinarith [sq_nonneg a]⟩

/-- **`eq:Sm-asymptotic`, the gamma-ratio half, with the remainder written out.**  For
`a>0` and `t ≥ 1000(a+2)³`,
`|G(a,t)/t^b - (1 + s_a/t)| ≤ 250(a+2)⁴/t²`, where `G` is the gamma-ratio product of
`eq:Sm-gamma-ratio`.  Neither the threshold nor the constant is sharp; both are chosen
so that every comparison below is a single step
(`scripts/check_gamma_ratio_expansion.py` measures the sharp order, and confirms it is
exactly `t⁻²`). -/
theorem abs_gammaRatioFactor_div_rpow_sub_le {a t : ℝ} (ha : 0 < a)
    (ht : 1000 * (a + 2) ^ 3 ≤ t) :
    |gammaRatioFactor a t / t ^ smExp a - (1 + smCoef a / t)|
      ≤ 250 * (a + 2) ^ 4 / t ^ 2 := by
  have hap : (2 : ℝ) < a + 2 := by linarith
  have hsq : (4 : ℝ) ≤ (a + 2) ^ 2 := by nlinarith [sq_nonneg a]
  have hcb : (8 : ℝ) ≤ (a + 2) ^ 3 := by nlinarith [sq_nonneg a, mul_pos ha (mul_pos ha ha)]
  have hstep : 4 * (a + 2) ≤ (a + 2) ^ 3 := by
    nlinarith [mul_le_mul_of_nonneg_left hsq (by linarith : (0:ℝ) ≤ a + 2)]
  have h4000 : 4000 * (a + 2) ≤ t := by linarith
  have ht0 : (0 : ℝ) < t := by linarith
  have ht2 : (0 : ℝ) < t ^ 2 := pow_pos ht0 2
  have htne : t ≠ 0 := ht0.ne'
  have hGpos : 0 < gammaRatioFactor a t :=
    gammaRatioFactor_pos (by linarith) (by linarith) (by linarith) (by linarith)
  have hlogG := log_gammaRatioFactor (a := a) (s := t)
    (by linarith) (by linarith) (by linarith) (by linarith)
  -- the shift bounds
  have hb1 : |a - 1 / 2| ≤ 2 * a + 1 := abs_le.2 ⟨by linarith, by linarith⟩
  have hb2 : |a| ≤ 2 * a + 1 := abs_le.2 ⟨by linarith, by linarith⟩
  have hb3 : |(1 : ℝ)| ≤ 2 * a + 1 := by rw [abs_one]; linarith
  have hb4 : |2 * a - 1| ≤ 2 * a + 1 := abs_le.2 ⟨by linarith, by linarith⟩
  have hthr : ∀ d : ℝ, |d| ≤ 2 * a + 1 → 4 * |d| + 4 ≤ t := fun d hd => by linarith
  have hfour := abs_four_shift_sub_le (M := t) (d₁ := a - 1 / 2) (d₂ := a)
    (d₃ := 1) (d₄ := 2 * a - 1) (B := 2 * a + 1) ht0
    (hthr _ hb1) (hthr _ hb2) (hthr _ hb3) (hthr _ hb4) hb1 hb2 hb3 hb4 (by linarith)
  rw [show t + (a - 1 / 2) = a + t - 1 / 2 from by ring,
    show t + a = a + t from by ring,
    show t + (2 * a - 1) = 2 * a + t - 1 from by ring] at hfour
  -- name the normalized log, and identify the two constants
  set u : ℝ := Real.log (gammaRatioFactor a t) - smExp a * Real.log t with hudef
  have hueq : Real.log (Real.Gamma (a + t - 1 / 2)) - Real.log (Real.Gamma (a + t))
        + (Real.log (Real.Gamma (t + 1)) - Real.log (Real.Gamma (2 * a + t - 1)))
        - (a - 1 / 2 - a + 1 - (2 * a - 1)) * Real.log t = u := by
    rw [hudef, hlogG, smExp]; ring
  have hqeq : ((a - 1 / 2) ^ 2 - (a - 1 / 2) - (a ^ 2 - a) + ((1 : ℝ) ^ 2 - 1)
      - ((2 * a - 1) ^ 2 - (2 * a - 1))) / (2 * t) = smCoef a / t := by
    rw [smCoef]; field_simp; ring
  rw [hueq, hqeq] at hfour
  -- the four-shift bound, in the paper's constants
  have hu1 : |u - smCoef a / t| ≤ 161 * (a + 2) ^ 3 / t ^ 2 := by
    refine le_trans hfour ?_
    refine alg_div_le ht2 ht2 ?_
    have hcube : (2 * a + 1 + 1) ^ 3 ≤ 8 * (a + 2) ^ 3 := by
      have h1 : (2 * a + 1 + 1) ^ 3 = 8 * (a + 1) ^ 3 := by ring
      have h2 : (a + 1) ^ 3 ≤ (a + 2) ^ 3 :=
        pow_le_pow_left₀ (by linarith) (by linarith) 3
      linarith only [h1, h2]
    have hnum : 20 * (2 * a + 1 + 1) ^ 3 + 1 / 15 ≤ 161 * (a + 2) ^ 3 := by
      linarith only [hcube, hcb]
    exact mul_le_mul_of_nonneg_right hnum ht2.le
  -- the size of `u`
  have hcoefb : |smCoef a| ≤ 3 * (a + 2) ^ 2 := abs_smCoef_le ha
  have hu2 : |u| ≤ 4 * (a + 2) ^ 2 / t := by
    have hsplit : |u| ≤ |smCoef a / t| + |u - smCoef a / t| := by
      have h2 := abs_add_le (smCoef a / t) (u - smCoef a / t)
      rw [show smCoef a / t + (u - smCoef a / t) = u from by ring] at h2
      exact h2
    have hsc : |smCoef a / t| ≤ 3 * (a + 2) ^ 2 / t := by
      rw [abs_div, abs_of_pos ht0]
      exact alg_div_le ht0 ht0 (mul_le_mul_of_nonneg_right hcoefb ht0.le)
    have hrest : 161 * (a + 2) ^ 3 / t ^ 2 ≤ (a + 2) ^ 2 / t := by
      refine alg_div_le ht2 ht0 ?_
      have hkey : 161 * (a + 2) ≤ t := by linarith
      have hpos : (0 : ℝ) ≤ (a + 2) ^ 2 * t := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hkey hpos]
    have hcomb : 3 * (a + 2) ^ 2 / t + (a + 2) ^ 2 / t = 4 * (a + 2) ^ 2 / t := by ring
    linarith only [hsplit, hsc, hrest, hu1, hcomb]
  have hu3 : |u| ≤ 1 := by
    refine le_trans hu2 ?_
    rw [div_le_one ht0]
    have hz : (0 : ℝ) ≤ (a + 2) ^ 2 := by positivity
    have h1 : (a + 2) ^ 2 * 4 ≤ (a + 2) ^ 2 * (1000 * (a + 2)) :=
      mul_le_mul_of_nonneg_left (by linarith) hz
    have h2 : (a + 2) ^ 2 * (1000 * (a + 2)) = 1000 * (a + 2) ^ 3 := by ring
    linarith only [h1, h2, ht]
  have husq : u ^ 2 ≤ 16 * (a + 2) ^ 4 / t ^ 2 := by
    have h1 : |u| ^ 2 ≤ (4 * (a + 2) ^ 2 / t) ^ 2 := pow_le_pow_left₀ (abs_nonneg u) hu2 2
    rw [sq_abs] at h1
    have h2 : (4 * (a + 2) ^ 2 / t) ^ 2 = 16 * (a + 2) ^ 4 / t ^ 2 := by
      rw [div_pow]; ring
    linarith only [h1, h2]
  -- `G/t^b = exp u`
  have hquot : gammaRatioFactor a t / t ^ smExp a = Real.exp u := by
    rw [hudef, Real.exp_sub, Real.exp_log hGpos, Real.rpow_def_of_pos ht0,
      mul_comm (Real.log t) (smExp a)]
  rw [hquot]
  have hexpb := Real.abs_exp_sub_one_sub_id_le hu3
  have hkey : |Real.exp u - (1 + smCoef a / t)|
      ≤ |Real.exp u - 1 - u| + |u - smCoef a / t| := by
    have h2 := abs_add_le (Real.exp u - 1 - u) (u - smCoef a / t)
    rw [show Real.exp u - 1 - u + (u - smCoef a / t)
        = Real.exp u - (1 + smCoef a / t) from by ring] at h2
    exact h2
  refine le_trans hkey ?_
  have hfin : 16 * (a + 2) ^ 4 / t ^ 2 + 161 * (a + 2) ^ 3 / t ^ 2
      ≤ 250 * (a + 2) ^ 4 / t ^ 2 := by
    rw [show 16 * (a + 2) ^ 4 / t ^ 2 + 161 * (a + 2) ^ 3 / t ^ 2
        = (16 * (a + 2) ^ 4 + 161 * (a + 2) ^ 3) / t ^ 2 from by ring]
    refine alg_div_le ht2 ht2 ?_
    have hnum : 16 * (a + 2) ^ 4 + 161 * (a + 2) ^ 3 ≤ 250 * (a + 2) ^ 4 := by
      have hz : (0 : ℝ) ≤ (a + 2) ^ 3 := by positivity
      have h1 : (a + 2) ^ 3 * 161 ≤ (a + 2) ^ 3 * (234 * (a + 2)) :=
        mul_le_mul_of_nonneg_left (by linarith) hz
      have h2 : (a + 2) ^ 3 * (234 * (a + 2)) = 234 * (a + 2) ^ 4 := by ring
      linarith only [h1, h2]
    exact mul_le_mul_of_nonneg_right hnum ht2.le
  exact le_trans (add_le_add (le_trans hexpb husq) hu1) hfin

/-- **`eq:Sm-asymptotic`.**  `S_m = C_a (4^m/(m!)²) m^b (1 + s_a/m + O_a(m^{-2}))`, with
the remainder two-sided and its constant written down: for `a>0` and
`m ≥ 1000(a+2)³`,
`|S_m/(C_a (4^m/(m!)²) m^b) - (1 + s_a/m)| ≤ 250(a+2)⁴/m²`.  Composed from the exact
identity `eq:Sm-gamma-ratio` and the gamma-ratio expansion above. -/
theorem abs_sweight_div_sub_le {a : ℝ} {k : ℕ} (ha : 0 < a)
    (hk : 1000 * (a + 2) ^ 3 ≤ (k : ℝ)) :
    |sweight a k / (smConst a * ((4 : ℝ) ^ k / (Nat.factorial k : ℝ) ^ 2)
        * (k : ℝ) ^ smExp a) - (1 + smCoef a / (k : ℝ))|
      ≤ 250 * (a + 2) ^ 4 / (k : ℝ) ^ 2 := by
  have hap : (2 : ℝ) < a + 2 := by linarith
  have hcb : (8 : ℝ) ≤ (a + 2) ^ 3 := by nlinarith [sq_nonneg a, mul_pos ha (mul_pos ha ha)]
  have hk0 : (8000 : ℝ) ≤ (k : ℝ) := by linarith
  have hk1 : 1 ≤ k := by
    have h : (1 : ℝ) ≤ (k : ℝ) := by linarith
    exact_mod_cast h
  have hfac : (0 : ℝ) < (Nat.factorial k : ℝ) := by exact_mod_cast Nat.factorial_pos k
  have hpi : (0 : ℝ) < Real.sqrt Real.pi := Real.sqrt_pos.2 Real.pi_pos
  have hC : (0 : ℝ) < smConst a := by
    rw [smConst]; exact div_pos (Real.rpow_pos_of_pos (by norm_num) _) hpi
  have hpow : (0 : ℝ) < (4 : ℝ) ^ k / (Nat.factorial k : ℝ) ^ 2 := by positivity
  have hP : (0 : ℝ) < (k : ℝ) ^ smExp a := Real.rpow_pos_of_pos (by linarith) _
  have hid : sweight a k = smConst a * ((4 : ℝ) ^ k / (Nat.factorial k : ℝ) ^ 2)
      * gammaRatioFactor a (k : ℝ) := by
    rw [sweight_eq_gamma_ratio ha hk1, smConst, gammaRatioFactor]
    ring
  have hsplit : sweight a k / (smConst a * ((4 : ℝ) ^ k / (Nat.factorial k : ℝ) ^ 2)
      * (k : ℝ) ^ smExp a) = gammaRatioFactor a (k : ℝ) / (k : ℝ) ^ smExp a := by
    rw [hid, div_eq_div_iff (by positivity) hP.ne']
    ring
  rw [hsplit]
  exact abs_gammaRatioFactor_div_rpow_sub_le ha hk

/-! ### `eq:hypergeom-moments`: the exact variance of the base law

`lem:central-moments` compares the law of `K_n` against the symmetric hypergeometric
law `π_{n,k} = C(n,k)²/C(2n,n)` — drawing `n` points without replacement from a
population of `2n` containing `n` marked ones — and the comparison consumes that
law's exact second moment.  That much is unconditional and is proved here, from
Chu–Vandermonde (`Nat.sum_range_choose_sq`) and `k C(n,k) = n C(n-1,k-1)`.

The rest of `lem:central-moments` is **not** proved here: the fourth and sixth
moments, the tilt comparison `eq:tilt-comparison` and the tail estimate
`eq:tilted-tail` all need Hoeffding's sampling-without-replacement inequality, and
Mathlib carries no concentration inequality for a hypergeometric law. -/

/-- The symmetric hypergeometric weight `π_{n,k} = C(n,k)²/C(2n,n)` of
`lem:central-moments`. -/
noncomputable def hyperWeight (n k : ℕ) : ℝ :=
  (Nat.choose n k : ℝ) ^ 2 / (Nat.choose (2 * n) n : ℝ)

theorem hyperWeight_denom_pos (n : ℕ) : (0 : ℝ) < (Nat.choose (2 * n) n : ℝ) := by
  have : 0 < Nat.choose (2 * n) n := Nat.choose_pos (by omega)
  exact_mod_cast this

/-- `C(2m+2,m+1) = 2C(2m+1,m)`, from `Nat.succ_mul_choose_eq`. -/
private theorem central_eq_two_mul (m : ℕ) :
    Nat.choose (2 * m + 2) (m + 1) = 2 * Nat.choose (2 * m + 1) m := by
  refine (Nat.eq_of_mul_eq_mul_left (Nat.succ_pos m) ?_).symm
  have h := Nat.add_one_mul_choose_eq (2 * m + 1) m
  rw [show 2 * m + 1 + 1 = 2 * m + 2 from by ring] at h
  calc (m + 1) * (2 * Nat.choose (2 * m + 1) m)
      = (2 * m + 2) * Nat.choose (2 * m + 1) m := by ring
    _ = Nat.choose (2 * m + 2) (m + 1) * (m + 1) := h
    _ = (m + 1) * Nat.choose (2 * m + 2) (m + 1) := by ring

/-- `(m+1)C(2m+2,m+1) = 2(2m+1)C(2m,m)`: the ratio of two consecutive central
binomials, which is what turns the second moment into a closed form. -/
private theorem hyper_central_ratio (m : ℕ) :
    (m + 1) * Nat.choose (2 * m + 2) (m + 1) = 2 * (2 * m + 1) * Nat.choose (2 * m) m := by
  have hsym : Nat.choose (2 * m + 1) (m + 1) = Nat.choose (2 * m + 1) m := by
    have h := Nat.choose_symm (n := 2 * m + 1) (k := m + 1) (by omega)
    rw [show 2 * m + 1 - (m + 1) = m from by omega] at h
    exact h.symm
  have hB := Nat.add_one_mul_choose_eq (2 * m) m
  rw [hsym] at hB
  -- hB : (2m+1) * C(2m,m) = C(2m+1,m) * (m+1)
  rw [central_eq_two_mul m]
  calc (m + 1) * (2 * Nat.choose (2 * m + 1) m)
      = 2 * (Nat.choose (2 * m + 1) m * (m + 1)) := by ring
    _ = 2 * ((2 * m + 1) * Nat.choose (2 * m) m) := by rw [hB]
    _ = 2 * (2 * m + 1) * Nat.choose (2 * m) m := by ring

/-- `∑_k k²C(n,k)² = n²C(2n-2,n-1)`: `kC(n,k) = nC(n-1,k-1)` termwise, then
Chu–Vandermonde on the shifted row. -/
private theorem sum_sq_mul_choose_sq (m : ℕ) :
    ∑ k ∈ Finset.range (m + 2), k ^ 2 * Nat.choose (m + 1) k ^ 2
      = (m + 1) ^ 2 * Nat.choose (2 * m) m := by
  rw [Finset.sum_range_succ' (fun k => k ^ 2 * Nat.choose (m + 1) k ^ 2) (m + 1)]
  have hterm : ∀ j ∈ Finset.range (m + 1),
      (j + 1) ^ 2 * Nat.choose (m + 1) (j + 1) ^ 2
        = (m + 1) ^ 2 * Nat.choose m j ^ 2 := by
    intro j _
    have h := Nat.add_one_mul_choose_eq m j
    calc (j + 1) ^ 2 * Nat.choose (m + 1) (j + 1) ^ 2
        = (Nat.choose (m + 1) (j + 1) * (j + 1)) ^ 2 := by ring
      _ = ((m + 1) * Nat.choose m j) ^ 2 := by rw [← h]
      _ = (m + 1) ^ 2 * Nat.choose m j ^ 2 := by ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, Nat.sum_range_choose_sq]
  simp

theorem hyperWeight_sum (n : ℕ) : ∑ k ∈ Finset.range (n + 1), hyperWeight n k = 1 := by
  have hden := hyperWeight_denom_pos n
  simp only [hyperWeight]
  rw [← Finset.sum_div]
  have hnum : ∑ k ∈ Finset.range (n + 1), (Nat.choose n k : ℝ) ^ 2
      = (Nat.choose (2 * n) n : ℝ) := by
    calc ∑ k ∈ Finset.range (n + 1), (Nat.choose n k : ℝ) ^ 2
        = ((∑ k ∈ Finset.range (n + 1), Nat.choose n k ^ 2 : ℕ) : ℝ) := by push_cast; ring
      _ = (Nat.choose (2 * n) n : ℝ) := by rw [Nat.sum_range_choose_sq n]
  rw [hnum, div_self hden.ne']

/-- The first moment is `n/2`, by the reflection `k ↦ n-k`. -/
theorem hyperWeight_first_moment (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), (k : ℝ) * hyperWeight n k = (n : ℝ) / 2 := by
  have hden := hyperWeight_denom_pos n
  set T : ℝ := ∑ k ∈ Finset.range (n + 1), (k : ℝ) * hyperWeight n k with hT
  have hrefl : T = ∑ k ∈ Finset.range (n + 1), ((n : ℝ) - k) * hyperWeight n k := by
    rw [hT]
    have h := Finset.sum_range_reflect
      (fun k => ((n : ℝ) - (k : ℝ)) * hyperWeight n k) (n + 1)
    rw [← h]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjn : j ≤ n := Finset.mem_range_succ_iff.mp hj
    rw [show n + 1 - 1 - j = n - j from by omega]
    have hchoose : Nat.choose n (n - j) = Nat.choose n j := Nat.choose_symm hjn
    have hcast : ((n - j : ℕ) : ℝ) = (n : ℝ) - (j : ℝ) := Nat.cast_sub hjn
    rw [hyperWeight, hyperWeight, hchoose, hcast]
    ring
  have hsplit : ∑ k ∈ Finset.range (n + 1), ((n : ℝ) - k) * hyperWeight n k
      = (n : ℝ) * (∑ k ∈ Finset.range (n + 1), hyperWeight n k) - T := by
    rw [hT, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [hsplit, hyperWeight_sum n, mul_one] at hrefl
  linarith

/-- The second moment is `n³/(2(2n-1))`. -/
theorem hyperWeight_second_moment {n : ℕ} (hn : 1 ≤ n) :
    ∑ k ∈ Finset.range (n + 1), (k : ℝ) ^ 2 * hyperWeight n k
      = (n : ℝ) ^ 3 / (2 * (2 * (n : ℝ) - 1)) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hnum : ∑ k ∈ Finset.range (m + 1 + 1), ((k : ℝ) ^ 2 * (Nat.choose (m + 1) k : ℝ) ^ 2)
      = ((m : ℝ) + 1) ^ 2 * (Nat.choose (2 * m) m : ℝ) := by
    calc ∑ k ∈ Finset.range (m + 1 + 1), ((k : ℝ) ^ 2 * (Nat.choose (m + 1) k : ℝ) ^ 2)
        = ((∑ k ∈ Finset.range (m + 2), k ^ 2 * Nat.choose (m + 1) k ^ 2 : ℕ) : ℝ) := by
          push_cast; ring
      _ = (((m + 1) ^ 2 * Nat.choose (2 * m) m : ℕ) : ℝ) := by rw [sum_sq_mul_choose_sq m]
      _ = ((m : ℝ) + 1) ^ 2 * (Nat.choose (2 * m) m : ℝ) := by push_cast; ring
  have hratio : ((m : ℝ) + 1) * (Nat.choose (2 * m + 2) (m + 1) : ℝ)
      = 2 * (2 * (m : ℝ) + 1) * (Nat.choose (2 * m) m : ℝ) := by
    calc ((m : ℝ) + 1) * (Nat.choose (2 * m + 2) (m + 1) : ℝ)
        = (((m + 1) * Nat.choose (2 * m + 2) (m + 1) : ℕ) : ℝ) := by push_cast; ring
      _ = ((2 * (2 * m + 1) * Nat.choose (2 * m) m : ℕ) : ℝ) := by rw [hyper_central_ratio m]
      _ = 2 * (2 * (m : ℝ) + 1) * (Nat.choose (2 * m) m : ℝ) := by push_cast; ring
  have hstep : ∀ k ∈ Finset.range (m + 1 + 1), (k : ℝ) ^ 2 * hyperWeight (m + 1) k
      = ((k : ℝ) ^ 2 * (Nat.choose (m + 1) k : ℝ) ^ 2)
        / (Nat.choose (2 * (m + 1)) (m + 1) : ℝ) := by
    intro k _; rw [hyperWeight]; ring
  rw [Finset.sum_congr rfl hstep, ← Finset.sum_div, hnum,
    show 2 * (m + 1) = 2 * m + 2 from by ring]
  have hden : (0 : ℝ) < (Nat.choose (2 * m + 2) (m + 1) : ℝ) := by
    have : 0 < Nat.choose (2 * m + 2) (m + 1) := Nat.choose_pos (by omega)
    exact_mod_cast this
  have hpos : (0 : ℝ) < 2 * (2 * ((m : ℝ) + 1) - 1) := by
    have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  push_cast
  rw [div_eq_div_iff hden.ne' hpos.ne']
  linear_combination (-(((m : ℝ) + 1) ^ 2)) * hratio

private theorem hyper_variance_algebra {x : ℝ} (hx : 0 < 2 * x - 1) :
    x ^ 3 / (2 * (2 * x - 1)) - x * (x / 2) + x ^ 2 / 4 * 1
      = x ^ 2 / (4 * (2 * x - 1)) := by
  have h2 : (2 : ℝ) * (2 * x - 1) ≠ 0 := (by linarith : (0:ℝ) < 2 * (2 * x - 1)).ne'
  have h4 : (4 : ℝ) * (2 * x - 1) ≠ 0 := (by linarith : (0:ℝ) < 4 * (2 * x - 1)).ne'
  have key : x ^ 3 / (2 * (2 * x - 1)) - x ^ 2 / (4 * (2 * x - 1))
      = x * (x / 2) - x ^ 2 / 4 * 1 := by
    rw [div_sub_div _ _ h2 h4, div_eq_iff (mul_ne_zero h2 h4)]
    ring
  linarith [key]

/-- **`eq:hypergeom-moments`, the exact variance.**  Under the symmetric
hypergeometric law, `Var K = n²/(4(2n-1))`. -/
theorem hyperWeight_variance {n : ℕ} (hn : 1 ≤ n) :
    ∑ k ∈ Finset.range (n + 1), ((k : ℝ) - (n : ℝ) / 2) ^ 2 * hyperWeight n k
      = (n : ℝ) ^ 2 / (4 * (2 * (n : ℝ) - 1)) := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hd : (0 : ℝ) < 2 * (n : ℝ) - 1 := by linarith
  have hterm : ∀ k ∈ Finset.range (n + 1),
      ((k : ℝ) - (n : ℝ) / 2) ^ 2 * hyperWeight n k
        = (k : ℝ) ^ 2 * hyperWeight n k
          - (n : ℝ) * ((k : ℝ) * hyperWeight n k)
          + (n : ℝ) ^ 2 / 4 * hyperWeight n k := fun k _ => by ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, hyperWeight_second_moment hn,
    hyperWeight_first_moment n, hyperWeight_sum n]
  exact hyper_variance_algebra hd

/-- **`eq:hypergeom-moments`** in the paper's normalization: with
`X = (K - n/2)/√n`, `E₀X² = n/(4(2n-1))`. -/
theorem hyperWeight_second_moment_scaled {n : ℕ} (hn : 1 ≤ n) :
    ∑ k ∈ Finset.range (n + 1),
        (((k : ℝ) - (n : ℝ) / 2) / Real.sqrt (n : ℝ)) ^ 2 * hyperWeight n k
      = (n : ℝ) / (4 * (2 * (n : ℝ) - 1)) := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hsq : Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) := Real.sq_sqrt (by linarith)
  have hne : (n : ℝ) ≠ 0 := by linarith
  have hd : (0 : ℝ) < 2 * (n : ℝ) - 1 := by linarith
  have hterm : ∀ k ∈ Finset.range (n + 1),
      (((k : ℝ) - (n : ℝ) / 2) / Real.sqrt (n : ℝ)) ^ 2 * hyperWeight n k
        = (1 / (n : ℝ)) * (((k : ℝ) - (n : ℝ) / 2) ^ 2 * hyperWeight n k) := by
    intro k _
    rw [div_pow, hsq]
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, hyperWeight_variance hn]
  field_simp

end TuranBessel
