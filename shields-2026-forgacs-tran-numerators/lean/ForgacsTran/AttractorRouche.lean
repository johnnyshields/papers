/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib
import Shields.Analysis.Complex.Rouche

/-!
# The panel-B reduced numerator has exactly two zeros in the half disk

The canonical Laurent restriction of `rem:cancellation-meaning` sends the
panel-B numerator to `N(t, g(t)) = t^{-2} B(t)` with

  `64 B(t) = t^6 - 22t^5 + 141t^4 - 252t^3 + 548t^2 - 288t + 64`,

and `cor:panel-B-attractor` splits it as `64B = 𝒬 + ℋ` with
`𝒬 = 548t^2 - 288t + 64` and `ℋ = t^6 - 22t^5 + 141t^4 - 252t^3`.  On `|t| = 1/2`
the split is a Rouché split: `‖ℋ‖ ≤ 2625/64` termwise, while `‖𝒬‖^2` is the
quadratic `140288 x^2 - 115776 x + 26065` in `x = Re t`, minimized at
`x = 1809/4384` with value `298424/137`; the gap `298424/137 - (2625/64)^2`
is `278329079/561152 > 0`.

## Main statements

* `panelQ_two_zeros` — `𝒬` factors over the disk with its two roots
  `(36 ± 8i√14)/137` displayed, both of modulus `4/√137 < 1/2`.
* `panelB64_two_zeros` — Rouché transfers the count: `64B` has exactly two
  zeros in `|t| < 1/2`, with multiplicity.
* `panelB64_pos_of_abs_le` — `64B > 0` on `[-1/2, 1/2]`, so neither zero is
  real.
* `panelB64_conj_pair` — the two zeros are a conjugate pair, and
  `exists_panelRoot` names the one in the upper half plane.

## Implementation notes

Sorry-free.

## References

Formalizes `../shields-2026-forgacs-tran-numerators.tex`, «Global and local zero
laws» (`sec:consequences`, `subsec:isolated-attractors`, `cor:panel-B-attractor`).

## Tags

Rouche theorem, zero counting, half disk, reduced numerator
-/

namespace ForgacsTran

open Complex Metric Shields ComplexConjugate

/-! ### The three polynomials -/

/-- Paper `cor:panel-B-attractor` — `64 B(t)`, the reduced numerator of the
panel-B data scaled to integer coefficients. -/
def panelB64 (t : ℂ) : ℂ :=
  t ^ 6 - 22 * t ^ 5 + 141 * t ^ 4 - 252 * t ^ 3 + 548 * t ^ 2 - 288 * t + 64

/-- Paper `cor:panel-B-attractor` — the dominant part `𝒬 = 548t^2 - 288t + 64`
of the Rouché split. -/
def panelQ (t : ℂ) : ℂ := 548 * t ^ 2 - 288 * t + 64

/-- Paper `cor:panel-B-attractor` — the perturbation
`ℋ = t^6 - 22t^5 + 141t^4 - 252t^3` of the Rouché split. -/
def panelH (t : ℂ) : ℂ := t ^ 6 - 22 * t ^ 5 + 141 * t ^ 4 - 252 * t ^ 3

theorem panelB64_eq_add (t : ℂ) : panelB64 t = panelQ t + panelH t := by
  simp only [panelB64, panelQ, panelH]; ring

/-! ### The estimates on `|t| = 1/2` -/

private theorem norm_sq_eq (z : ℂ) : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
  simp only [Complex.norm_def, Complex.normSq_apply]
  rw [Real.sq_sqrt (by nlinarith [sq_nonneg z.re, sq_nonneg z.im])]
  ring

/-- Paper `cor:panel-B-attractor` — on `|t| = 1/2`, `‖𝒬(t)‖^2` is the quadratic
`140288 x^2 - 115776 x + 26065` in `x = Re t`.  This is the paper's
`|𝒬(½e^{iθ})|^2 = 35072 cos^2 θ - 57888 cos θ + 26065`, written in `x = ½cos θ`. -/
theorem panelQ_norm_sq {t : ℂ} (ht : ‖t‖ = 1 / 2) :
    ‖panelQ t‖ ^ 2 = 140288 * t.re ^ 2 - 115776 * t.re + 26065 := by
  have hcirc : t.re ^ 2 + t.im ^ 2 = 1 / 4 := by
    have h := norm_sq_eq t
    rw [ht] at h; nlinarith [h]
  have hre : (panelQ t).re = 548 * (t.re ^ 2 - t.im ^ 2) - 288 * t.re + 64 := by
    simp only [panelQ, Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.mul_im,
      pow_two]
    norm_num
    try ring
  have him : (panelQ t).im = 1096 * t.re * t.im - 288 * t.im := by
    simp only [panelQ, Complex.sub_im, Complex.add_im, Complex.mul_re, Complex.mul_im,
      pow_two]
    norm_num
    try ring
  rw [norm_sq_eq, hre, him]
  nlinarith [hcirc, sq_nonneg t.re, sq_nonneg t.im]

/-- Paper `cor:panel-B-attractor` — the exact minimum of `‖𝒬‖^2` on `|t| = 1/2`,
attained where `cos θ = 1809/2192`. -/
theorem panelQ_norm_sq_ge {t : ℂ} (ht : ‖t‖ = 1 / 2) :
    (298424 : ℝ) / 137 ≤ ‖panelQ t‖ ^ 2 := by
  rw [panelQ_norm_sq ht]
  nlinarith [sq_nonneg (4384 * t.re - 1809)]

/-- Paper `cor:panel-B-attractor` — the termwise bound `‖ℋ‖ ≤ 2625/64` on
`|t| = 1/2`. -/
theorem panelH_norm_le {t : ℂ} (ht : ‖t‖ = 1 / 2) : ‖panelH t‖ ≤ 2625 / 64 := by
  have h6 : ‖t ^ 6‖ = 1 / 64 := by rw [norm_pow, ht]; norm_num
  have h5 : ‖(22 : ℂ) * t ^ 5‖ = 22 / 32 := by
    rw [norm_mul, norm_pow, ht]; norm_num
  have h4 : ‖(141 : ℂ) * t ^ 4‖ = 141 / 16 := by
    rw [norm_mul, norm_pow, ht]; norm_num
  have h3 : ‖(252 : ℂ) * t ^ 3‖ = 252 / 8 := by
    rw [norm_mul, norm_pow, ht]; norm_num
  calc ‖panelH t‖ ≤ ‖t ^ 6 - 22 * t ^ 5 + 141 * t ^ 4‖ + ‖(252 : ℂ) * t ^ 3‖ :=
        norm_sub_le _ _
    _ ≤ (‖t ^ 6 - 22 * t ^ 5‖ + ‖(141 : ℂ) * t ^ 4‖) + ‖(252 : ℂ) * t ^ 3‖ := by
        gcongr; exact norm_add_le _ _
    _ ≤ ((‖t ^ 6‖ + ‖(22 : ℂ) * t ^ 5‖) + ‖(141 : ℂ) * t ^ 4‖) + ‖(252 : ℂ) * t ^ 3‖ := by
        gcongr; exact norm_sub_le _ _
    _ = 2625 / 64 := by rw [h6, h5, h4, h3]; norm_num

/-- **Paper `cor:panel-B-attractor`, the Rouché inequality.**  On `|t| = 1/2` the
perturbation is dominated: `‖ℋ‖ ≤ 2625/64 < √(298424/137) ≤ ‖𝒬‖`. -/
theorem panelH_norm_lt_panelQ {t : ℂ} (ht : t ∈ sphere (0 : ℂ) (1 / 2)) :
    ‖panelH t‖ < ‖panelQ t‖ := by
  have ht' : ‖t‖ = 1 / 2 := by simpa [Complex.dist_eq] using ht
  have hH := panelH_norm_le ht'
  have hQ := panelQ_norm_sq_ge ht'
  have hQ0 : (0 : ℝ) ≤ ‖panelQ t‖ := norm_nonneg _
  nlinarith [hH, hQ, hQ0, norm_nonneg (panelH t)]


/-! ### The two zeros of `𝒬` -/

/-- Paper `cor:panel-B-attractor` — the zero `(36 + 8i√14)/137` of `𝒬`. -/
noncomputable def panelQRoot : ℂ := ((36 / 137 : ℝ) : ℂ) + ((8 * Real.sqrt 14 / 137 : ℝ) : ℂ) * I

/-- Paper `cor:panel-B-attractor` — the zero `(36 - 8i√14)/137` of `𝒬`. -/
noncomputable def panelQRoot' : ℂ := ((36 / 137 : ℝ) : ℂ) - ((8 * Real.sqrt 14 / 137 : ℝ) : ℂ) * I

private theorem sqrt14_sq : ((Real.sqrt 14 : ℝ) : ℂ) ^ 2 = 14 := by
  norm_cast
  exact Real.sq_sqrt (by norm_num)

/-- Paper `cor:panel-B-attractor` — `𝒬 = 548(t - α)(t - ᾱ)` with
`α = (36 + 8i√14)/137`. -/
theorem panelQ_factor (t : ℂ) :
    panelQ t = (t - panelQRoot) * (t - panelQRoot') * 548 := by
  have hw : (((8 * Real.sqrt 14 / 137 : ℝ) : ℂ) * I) ^ 2 = -(896 / 18769) := by
    rw [mul_pow, Complex.I_sq]
    push_cast
    rw [div_pow, mul_pow, sqrt14_sq]
    norm_num
  have hc : ((36 / 137 : ℝ) : ℂ) = 36 / 137 := by push_cast; ring
  simp only [panelQ, panelQRoot, panelQRoot', hc]
  linear_combination (548 : ℂ) * hw

/-- Paper `cor:panel-B-attractor` — both zeros of `𝒬` have modulus
`4/√137 < 1/2`. -/
theorem panelQRoot_norm_sq : ‖panelQRoot‖ ^ 2 = 16 / 137 := by
  have h14 : Real.sqrt 14 ^ 2 = 14 := Real.sq_sqrt (by norm_num)
  have hre : panelQRoot.re = 36 / 137 := by simp [panelQRoot]
  have him : panelQRoot.im = 8 * Real.sqrt 14 / 137 := by simp [panelQRoot]
  rw [norm_sq_eq, hre, him]
  field_simp
  nlinarith [h14]

theorem panelQRoot'_norm_sq : ‖panelQRoot'‖ ^ 2 = 16 / 137 := by
  have h14 : Real.sqrt 14 ^ 2 = 14 := Real.sq_sqrt (by norm_num)
  have hre : panelQRoot'.re = 36 / 137 := by simp [panelQRoot']
  have him : panelQRoot'.im = -(8 * Real.sqrt 14 / 137) := by simp [panelQRoot']
  rw [norm_sq_eq, hre, him]
  field_simp
  nlinarith [h14]

theorem panelQRoot_mem_ball : panelQRoot ∈ ball (0 : ℂ) (1 / 2) := by
  have h := panelQRoot_norm_sq
  have h0 : (0 : ℝ) ≤ ‖panelQRoot‖ := norm_nonneg _
  simp only [mem_ball, Complex.dist_eq, sub_zero]
  nlinarith [h, h0]

theorem panelQRoot'_mem_ball : panelQRoot' ∈ ball (0 : ℂ) (1 / 2) := by
  have h := panelQRoot'_norm_sq
  have h0 : (0 : ℝ) ≤ ‖panelQRoot'‖ := norm_nonneg _
  simp only [mem_ball, Complex.dist_eq, sub_zero]
  nlinarith [h, h0]


/-! ### The Rouché count -/

theorem analyticOnNhd_panelQ : AnalyticOnNhd ℂ panelQ (closedBall (0 : ℂ) (1 / 2)) := by
  intro z _
  rw [show panelQ = fun t : ℂ => 548 * t ^ 2 - 288 * t + 64 from rfl]
  fun_prop

theorem analyticOnNhd_panelH : AnalyticOnNhd ℂ panelH (closedBall (0 : ℂ) (1 / 2)) := by
  intro z _
  rw [show panelH = fun t : ℂ => t ^ 6 - 22 * t ^ 5 + 141 * t ^ 4 - 252 * t ^ 3 from rfl]
  fun_prop

/-- **Paper `cor:panel-B-attractor`.**  `𝒬` factors over `|t| ≤ 1/2` with exactly
its two roots displayed, both strictly inside. -/
theorem factoredOn_panelQ :
    FactoredOn panelQ 0 (1 / 2) 2
      (fun j => if j = 0 then panelQRoot else panelQRoot') (fun _ => 548) where
  mem_ball := by
    intro j _
    by_cases h : j = 0
    · simpa [h] using panelQRoot_mem_ball
    · simpa [h] using panelQRoot'_mem_ball
  analytic := fun _ _ => analyticAt_const
  ne_zero := fun _ _ => by norm_num
  eq := fun z => by
    simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul,
      if_neg (by norm_num : ¬(1 : ℕ) = 0)]
    exact panelQ_factor z

/-- **Paper `cor:panel-B-attractor` — Rouché gives exactly two zeros of `B` in
`|t| < 1/2`.**  The count is displayed as a factorization, so it is the count
with multiplicity. -/
theorem panelB64_two_zeros :
    ∃ (a : ℕ → ℂ) (G : ℂ → ℂ), FactoredOn panelB64 0 (1 / 2) 2 a G := by
  have hR : (0 : ℝ) < 1 / 2 := by norm_num
  have hsum : AnalyticOnNhd ℂ (fun w => panelQ w + panelH w) (closedBall (0 : ℂ) (1 / 2)) :=
    fun z hz => (analyticOnNhd_panelQ z hz).add (analyticOnNhd_panelH z hz)
  have hne : ∀ z ∈ sphere (0 : ℂ) (1 / 2), panelQ z + panelH z ≠ 0 := by
    intro z hz h
    have hlt := panelH_norm_lt_panelQ hz
    have hQz : panelQ z = -panelH z := by linear_combination h
    rw [hQz, norm_neg] at hlt
    exact lt_irrefl _ hlt
  obtain ⟨n', a', G', hfac'⟩ := exists_factoredOn hR hsum hne
  have hn : 2 = n' :=
    rouche hR analyticOnNhd_panelQ analyticOnNhd_panelH
      (fun z hz => panelH_norm_lt_panelQ hz) factoredOn_panelQ hfac'
  refine ⟨a', G', ?_⟩
  rw [hn]
  exact hfac'.congr (fun z => panelB64_eq_add z)


/-! ### The two zeros are a nonreal conjugate pair -/

/-- Paper `cor:panel-B-attractor` — `64B > 0` on `[-1/2, 1/2]`, so `B` has no
real zero there. -/
theorem panelB64_real_pos {x : ℝ} (h₁ : -(1 / 2) ≤ x) (h₂ : x ≤ 1 / 2) :
    0 < x ^ 6 - 22 * x ^ 5 + 141 * x ^ 4 - 252 * x ^ 3 + 548 * x ^ 2 - 288 * x + 64 := by
  nlinarith [sq_nonneg x, sq_nonneg (x - 1 / 2), sq_nonneg (x + 1 / 2), sq_nonneg (x ^ 2),
    sq_nonneg (x ^ 3), sq_nonneg (x ^ 2 - x), sq_nonneg (137 * x - 36),
    mul_nonneg (sub_nonneg.mpr h₂) (sub_nonneg.mpr h₁)]

theorem panelB64_ofReal_ne_zero {x : ℝ} (h₁ : -(1 / 2) ≤ x) (h₂ : x ≤ 1 / 2) :
    panelB64 (x : ℂ) ≠ 0 := by
  have hpos := panelB64_real_pos h₁ h₂
  have : panelB64 (x : ℂ) =
      ((x ^ 6 - 22 * x ^ 5 + 141 * x ^ 4 - 252 * x ^ 3 + 548 * x ^ 2 - 288 * x + 64 : ℝ) : ℂ) := by
    simp only [panelB64]; push_cast; ring
  rw [this]
  exact Complex.ofReal_ne_zero.mpr hpos.ne'

/-- Paper `cor:panel-B-attractor` — `B` has real coefficients, so its zero set is
closed under conjugation. -/
theorem panelB64_conj (t : ℂ) : panelB64 (conj t) = conj (panelB64 t) := by
  simp only [panelB64]
  simp [map_add, map_sub, map_mul, map_pow, map_ofNat]

/-- **Paper `cor:panel-B-attractor`.**  The two zeros of `B` in `|t| < 1/2` are a
simple nonreal conjugate pair; `t_*` is the one in the upper half plane. -/
theorem exists_panelRoot :
    ∃ t : ℂ, 0 < t.im ∧ ‖t‖ < 1 / 2 ∧ panelB64 t = 0 ∧
      ∀ w ∈ closedBall (0 : ℂ) (1 / 2), panelB64 w = 0 ↔ (w = t ∨ w = conj t) := by
  obtain ⟨a, G, hfac⟩ := panelB64_two_zeros
  have hmem0 : a 0 ∈ ball (0 : ℂ) (1 / 2) := hfac.mem_ball 0 (by norm_num)
  have hmem1 : a 1 ∈ ball (0 : ℂ) (1 / 2) := hfac.mem_ball 1 (by norm_num)
  have hnorm0 : ‖a 0‖ < 1 / 2 := by simpa [Complex.dist_eq] using hmem0
  have hnorm1 : ‖a 1‖ < 1 / 2 := by simpa [Complex.dist_eq] using hmem1
  have hzero : ∀ w ∈ closedBall (0 : ℂ) (1 / 2), panelB64 w = 0 ↔ (w = a 0 ∨ w = a 1) := by
    intro w hw
    rw [hfac.eq_zero_iff hw]
    constructor
    · rintro ⟨j, hj, rfl⟩
      interval_cases j
      · exact Or.inl rfl
      · exact Or.inr rfl
    · rintro (rfl | rfl)
      · exact ⟨0, by norm_num, rfl⟩
      · exact ⟨1, by norm_num, rfl⟩
  have hball0 : a 0 ∈ closedBall (0 : ℂ) (1 / 2) := ball_subset_closedBall hmem0
  have hval0 : panelB64 (a 0) = 0 := (hzero _ hball0).mpr (Or.inl rfl)
  -- the zero is not real
  have him0 : (a 0).im ≠ 0 := by
    intro h
    have hre : ((a 0).re : ℂ) = a 0 := by
      apply Complex.ext <;> simp [h]
    have habs : |(a 0).re| ≤ ‖a 0‖ := Complex.abs_re_le_norm _
    have h₁ : -(1 / 2) ≤ (a 0).re := by
      have := abs_le.mp habs
      linarith [this.1, hnorm0]
    have h₂ : (a 0).re ≤ 1 / 2 := by
      have := abs_le.mp habs
      linarith [this.2, hnorm0]
    exact panelB64_ofReal_ne_zero h₁ h₂ (by rw [hre]; exact hval0)
  -- the second zero is the conjugate of the first
  have hconjball : conj (a 0) ∈ closedBall (0 : ℂ) (1 / 2) := by
    simp only [mem_closedBall, Complex.dist_eq, sub_zero, RCLike.norm_conj]
    exact hnorm0.le
  have hconjzero : panelB64 (conj (a 0)) = 0 := by
    rw [panelB64_conj, hval0, map_zero]
  have hne : conj (a 0) ≠ a 0 := by
    intro h
    apply him0
    have := congrArg Complex.im h
    simp only [Complex.conj_im] at this
    linarith
  have ha1 : a 1 = conj (a 0) := by
    rcases (hzero _ hconjball).mp hconjzero with h | h
    · exact absurd h hne
    · exact h.symm
  rcases lt_or_gt_of_ne him0 with hlt | hgt
  · refine ⟨conj (a 0), by simpa using (by linarith : (0:ℝ) < -(a 0).im), ?_, hconjzero, ?_⟩
    · simpa [RCLike.norm_conj] using hnorm0
    · intro w hw
      rw [hzero w hw, ha1]
      simp [or_comm]
  · refine ⟨a 0, hgt, hnorm0, hval0, ?_⟩
    intro w hw
    rw [hzero w hw, ha1]

end ForgacsTran
