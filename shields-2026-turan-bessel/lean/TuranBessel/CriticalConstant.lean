/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import TuranBessel.Digamma
import TuranBessel.Tetragamma

/-!
# The critical constant: endpoint limits and exact range

`shields-2026-turan-bessel.tex`, `sec:scaling` (`prop:c-monotone`,
`eq:c-critical`, `eq:c-range`).

`c(a) = 4/ψ₁(a) - 4a + 7/2`.  `Scaling.cCrit_mem` puts it strictly inside
`(3/2, 7/2)`; what is added here is that both endpoints are attained in the
limit, quantitatively:

```
  |c(a) - 3/2| ≤ 1/a        (a ≥ 1)
  |c(a) - 7/2| ≤ 8a         (0 < a ≤ 1)
```

The first is the three-term trigamma sandwich rearranged — `1 - ψ₁(a)(a-1/2)`
is `1/(12a²) + O(a⁻³)`, and dividing by `ψ₁(a) > 1/a` costs one power of `a`.
The second needs only `a²ψ₁(a) > 1`.  With continuity of `ψ₁` the intermediate
value theorem then gives the exact range, so `eq:c-range` is sharp at both ends.

Strict monotonicity closes the rest of `prop:c-monotone`: `c'(a)` is
`-4(ψ₁(a)²+ψ₂(a))/ψ₁(a)²`, so it is negative exactly by the polygamma inequality
`Tetragamma.polygammaCombo_pos`.  The range statement does not use it — the
intermediate value theorem gives the range from the two endpoint bounds alone —
so the two halves of the proposition are independent here.

Sorry-free.
-/

namespace TuranBessel

open Filter Topology

variable {a : ℝ}

/-! ### The large-`a` end -/

/-- `1 - ψ₁(a)(a - 1/2) = 1/(12a²) + 1/(12a³) - θ(a)(a-1/2)` with
`|θ(a)| ≤ 1/(20a⁴)`: the sandwich rearranged around the value `a - 1/2` that
`1/ψ₁(a)` approaches. -/
theorem abs_one_sub_trigamma_mul (ha : 1 ≤ a) :
    |1 - trigamma a * (a - 1 / 2)| ≤ 13 / 60 / a ^ 2 := by
  have ha0 : (0 : ℝ) < a := by linarith
  have hsand := abs_trigamma_sub_cubic_le ha0
  rw [abs_le] at hsand
  set P : ℝ := 1 / a + 1 / (2 * a ^ 2) + 1 / (6 * a ^ 3) with hP
  have hid : 1 - P * (a - 1 / 2) = 1 / (12 * a ^ 2) + 1 / (12 * a ^ 3) := by
    rw [hP]; field_simp; ring
  have hfac : (0 : ℝ) ≤ a - 1 / 2 := by linarith
  -- the `θ(a)(a-1/2)` term
  have hE : |(trigamma a - P) * (a - 1 / 2)| ≤ 1 / 20 / a ^ 2 := by
    have hth : |trigamma a - P| ≤ 1 / (20 * a ^ 4) := by
      rw [abs_le]; exact ⟨hsand.1, hsand.2⟩
    have hmul : |(trigamma a - P) * (a - 1 / 2)| ≤ 1 / (20 * a ^ 4) * (a - 1 / 2) := by
      rw [abs_mul, abs_of_nonneg hfac]
      exact mul_le_mul_of_nonneg_right hth hfac
    have hb1 : 1 / (20 * a ^ 4) * (a - 1 / 2) ≤ 1 / 20 / a ^ 2 := by
      rw [show 1 / (20 * a ^ 4) * (a - 1 / 2) = (a - 1 / 2) / (20 * a ^ 4) from by ring]
      refine alg_div_le (by positivity) (by positivity) ?_
      nlinarith [pow_pos ha0 2, pow_pos ha0 3, pow_pos ha0 4]
    linarith
  rw [abs_le] at hE
  -- the two leading terms
  have hD0 : (0 : ℝ) ≤ 1 / (12 * a ^ 2) + 1 / (12 * a ^ 3) := by positivity
  have hD1 : 1 / (12 * a ^ 2) ≤ 1 / 12 / a ^ 2 := by
    have hne : (a : ℝ) ≠ 0 := ha0.ne'
    rw [show (1 : ℝ) / 12 / a ^ 2 = 1 / (12 * a ^ 2) from by field_simp]
  have hD2 : 1 / (12 * a ^ 3) ≤ 1 / 12 / a ^ 2 := by
    refine alg_div_le (by positivity) (by positivity) ?_
    nlinarith [pow_pos ha0 2, pow_pos ha0 3]
  have hsplit : 1 - trigamma a * (a - 1 / 2)
      = (1 / (12 * a ^ 2) + 1 / (12 * a ^ 3)) - (trigamma a - P) * (a - 1 / 2) := by
    rw [show (1 : ℝ) / (12 * a ^ 2) + 1 / (12 * a ^ 3) = 1 - P * (a - 1 / 2) from hid.symm]
    ring
  rw [hsplit, abs_le]
  constructor
  · have : (0 : ℝ) < 1 / 20 / a ^ 2 := by positivity
    have h30 : (1 : ℝ) / 20 / a ^ 2 ≤ 13 / 60 / a ^ 2 := by
      refine alg_div_le (by positivity) (by positivity) ?_
      nlinarith [pow_pos ha0 2]
    linarith [hE.2, hD0]
  · have h30 : (1 : ℝ) / 12 / a ^ 2 + 1 / 12 / a ^ 2 + 1 / 20 / a ^ 2 = 13 / 60 / a ^ 2 := by
      field
    linarith [hE.1, hD1, hD2, h30]

/-- **`|c(a) - 3/2| ≤ 1/a` for `a ≥ 1`.**  `c(a) - 3/2 = 4(1 - ψ₁(a)(a-1/2))/ψ₁(a)`,
and `ψ₁(a) > 1/a`. -/
theorem abs_cCrit_sub_three_halves_le (ha : 1 ≤ a) : |cCrit a - 3 / 2| ≤ 1 / a := by
  have ha0 : (0 : ℝ) < a := by linarith
  have hg : 0 < trigamma a := trigamma_pos ha0
  have hlow : 1 / a < trigamma a := by
    have h := a_trigamma_gt_one ha0
    rw [div_lt_iff₀ ha0]; linarith
  have h4 : (4 : ℝ) / trigamma a * trigamma a = 4 := div_mul_cancel₀ _ hg.ne'
  have hid : cCrit a - 3 / 2 = 4 * (1 - trigamma a * (a - 1 / 2)) / trigamma a := by
    rw [cCrit, eq_div_iff hg.ne']
    linear_combination h4
  rw [hid, abs_div, abs_of_pos hg, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ (4:ℝ))]
  refine alg_div_le hg ha0 ?_
  have hb := abs_one_sub_trigamma_mul ha
  have hA : (0 : ℝ) ≤ |1 - trigamma a * (a - 1 / 2)| := abs_nonneg _
  have h1 : 4 * |1 - trigamma a * (a - 1 / 2)| * a ≤ 4 * (13 / 60 / a ^ 2) * a := by
    have hs := mul_le_mul_of_nonneg_left hb (by norm_num : (0:ℝ) ≤ (4:ℝ))
    exact mul_le_mul_of_nonneg_right hs ha0.le
  have h2 : 4 * (13 / 60 / a ^ 2) * a = 13 / 15 / a := by
    field
  have h3 : (13 : ℝ) / 15 / a ≤ 1 / a := by
    refine alg_div_le ha0 ha0 ?_
    nlinarith
  linarith [h1, h2, h3, hlow]

theorem tendsto_cCrit_atTop : Tendsto cCrit atTop (𝓝 (3 / 2)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt (max (1 / ε) 1)
  refine ⟨max ((N : ℝ)) 1, fun a ha => ?_⟩
  have ha1 : (1 : ℝ) ≤ a := le_trans (le_max_right _ _) ha
  have haN : (N : ℝ) ≤ a := le_trans (le_max_left _ _) ha
  have hNe : 1 / ε < (N : ℝ) := lt_of_le_of_lt (le_max_left _ _) hN
  have ha0 : (0 : ℝ) < a := by linarith
  have hb := abs_cCrit_sub_three_halves_le ha1
  rw [Real.dist_eq]
  have : 1 / a < ε := by
    rw [div_lt_iff₀ ha0]
    rw [div_lt_iff₀ hε] at hNe
    nlinarith
  linarith

/-! ### The small-`a` end -/

/-- **`|c(a) - 7/2| ≤ 8a` for `0 < a ≤ 1`**, from `a²ψ₁(a) > 1` alone. -/
theorem abs_cCrit_sub_seven_halves_le (ha : 0 < a) (ha1 : a ≤ 1) :
    |cCrit a - 7 / 2| ≤ 8 * a := by
  have hg : 0 < trigamma a := trigamma_pos ha
  have hsq := sq_mul_trigamma_gt_one ha
  have hinv : 4 / trigamma a ≤ 4 * a ^ 2 := by
    rw [div_le_iff₀ hg]
    nlinarith [pow_pos ha 2]
  have hpos : (0 : ℝ) < 4 / trigamma a := by positivity
  have hid : cCrit a - 7 / 2 = 4 / trigamma a - 4 * a := by rw [cCrit]; ring
  rw [hid, abs_le]
  constructor
  · nlinarith [hpos, ha]
  · nlinarith [hinv, ha, ha1, pow_pos ha 2]

theorem tendsto_cCrit_zero : Tendsto cCrit (nhdsWithin 0 (Set.Ioi 0)) (𝓝 (7 / 2)) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  refine ⟨min (ε / 9) 1, by positivity, fun {a} ha hd => ?_⟩
  have ha0 : (0 : ℝ) < a := Set.mem_Ioi.1 ha
  rw [Real.dist_eq, sub_zero, abs_of_pos ha0] at hd
  have ha1 : a ≤ 1 := le_of_lt (lt_of_lt_of_le hd (min_le_right _ _))
  have haε : a < ε / 9 := lt_of_lt_of_le hd (min_le_left _ _)
  rw [Real.dist_eq]
  have hb := abs_cCrit_sub_seven_halves_le ha0 ha1
  have habs : |cCrit a - 7 / 2| ≤ 8 * a := hb
  nlinarith [habs, haε, hε, abs_nonneg (cCrit a - 7 / 2)]

/-! ### The exact range -/

/-- `ψ₁` is continuous on every compact subinterval of `(0,∞)`: the defining series
is dominated there by the summable `(c+n)⁻²`.  `Anomaly.continuousOn_trigamma` is
the `[1/4,1/2]` case; the argument never used the endpoints. -/
theorem continuousOn_trigamma_Icc {c d : ℝ} (hc : 0 < c) :
    ContinuousOn trigamma (Set.Icc c d) := by
  have hu : Summable (fun n : ℕ => (c + (n : ℝ))⁻¹ ^ 2) := trigamma_summable hc
  refine continuousOn_tsum (u := fun n : ℕ => (c + (n : ℝ))⁻¹ ^ 2) ?_ hu ?_
  · intro n
    refine ContinuousOn.pow (ContinuousOn.inv₀ ?_ ?_) 2
    · exact (continuous_id.add continuous_const).continuousOn
    · intro y hy
      have h1 : c ≤ y := hy.1
      have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      have : (0 : ℝ) < y + (n : ℝ) := by linarith
      exact this.ne'
  · intro n y hy
    have hy1 : c ≤ y := hy.1
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hq : (0 : ℝ) < c + (n : ℝ) := by positivity
    have hy0 : (0 : ℝ) < y + (n : ℝ) := by linarith
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    simp only [inv_pow]
    exact inv_anti₀ (by positivity) (by nlinarith)

theorem continuousOn_cCrit {c d : ℝ} (hc : 0 < c) : ContinuousOn cCrit (Set.Icc c d) := by
  refine ContinuousOn.add (ContinuousOn.sub ?_ ?_) continuousOn_const
  · exact continuousOn_const.div (continuousOn_trigamma_Icc hc)
      (fun y hy => (trigamma_pos (lt_of_lt_of_le hc hy.1)).ne')
  · exact continuousOn_const.mul continuousOn_id

/-- **`eq:c-range` is sharp.**  Every value strictly between `3/2` and `7/2` is
attained by `c` on `(0,∞)`, so the range is exactly `(3/2, 7/2)`.  The two
endpoint bounds put `c` above `v` near `0` and below `v` far out, and the
intermediate value theorem does the rest — no monotonicity is used. -/
theorem exists_cCrit_eq {v : ℝ} (hv : v ∈ Set.Ioo (3 / 2 : ℝ) (7 / 2)) :
    ∃ a > 0, cCrit a = v := by
  obtain ⟨hv1, hv2⟩ := hv
  -- a point where `c` is above `v`
  obtain ⟨a₀, ha₀, hlt⟩ : ∃ a₀ > 0, v < cCrit a₀ := by
    have h : Tendsto cCrit (nhdsWithin 0 (Set.Ioi 0)) (𝓝 (7 / 2)) := tendsto_cCrit_zero
    have hev : ∀ᶠ a in nhdsWithin (0:ℝ) (Set.Ioi 0), v < cCrit a :=
      h.eventually (eventually_gt_nhds hv2)
    obtain ⟨a₀, ha₀mem, hgt⟩ := (hev.and self_mem_nhdsWithin).exists
    exact ⟨a₀, Set.mem_Ioi.1 hgt, ha₀mem⟩
  -- a point beyond it where `c` is below `v`
  obtain ⟨a₁, hlt01, hgt⟩ : ∃ a₁ > a₀, cCrit a₁ < v := by
    have hev : ∀ᶠ a in atTop, cCrit a < v :=
      tendsto_cCrit_atTop.eventually (eventually_lt_nhds hv1)
    obtain ⟨a₁, h1, h2⟩ := (hev.and (eventually_gt_atTop a₀)).exists
    exact ⟨a₁, h2, h1⟩
  have hcont : ContinuousOn cCrit (Set.Icc a₀ a₁) := continuousOn_cCrit ha₀
  have hmem : v ∈ Set.Icc (cCrit a₁) (cCrit a₀) := ⟨hgt.le, hlt.le⟩
  obtain ⟨y, hy, hyv⟩ := intermediate_value_Icc' hlt01.le hcont hmem
  exact ⟨y, lt_of_lt_of_le ha₀ hy.1, hyv⟩

/-! ### Strict monotonicity -/

/-- `c'(a) = -4ψ₂(a)/ψ₁(a)²-4`, from `ψ₁' = ψ₂`. -/
theorem hasDerivAt_cCrit (ha : 0 < a) :
    HasDerivAt cCrit (-(4 * tetragamma a) / trigamma a ^ 2 - 4) a := by
  have hg : 0 < trigamma a := trigamma_pos ha
  have hnum : HasDerivAt (fun _ : ℝ => (4 : ℝ)) 0 a := hasDerivAt_const a 4
  have hden : HasDerivAt trigamma (tetragamma a) a := hasDerivAt_trigamma ha
  have hlin : HasDerivAt (fun x : ℝ => 4 * x) 4 a := by
    simpa using (hasDerivAt_id a).const_mul (4 : ℝ)
  have h : HasDerivAt (fun x : ℝ => 4 / trigamma x - 4 * x + 7 / 2)
      ((0 * trigamma a - 4 * tetragamma a) / trigamma a ^ 2 - 4) a :=
    ((hnum.div hden hg.ne').sub hlin).add_const (7 / 2)
  have hfun : cCrit = fun x : ℝ => 4 / trigamma x - 4 * x + 7 / 2 := by
    funext x; rw [cCrit]
  rw [hfun]
  refine h.congr_deriv ?_
  rw [zero_mul, zero_sub]

/-- `c' < 0` on `(0,∞)`: `c'(a) = -4(ψ₁(a)²+ψ₂(a))/ψ₁(a)²` and the numerator is
positive by `prop:c-monotone`'s polygamma inequality. -/
theorem deriv_cCrit_neg (ha : 0 < a) : deriv cCrit a < 0 := by
  have hg : 0 < trigamma a := trigamma_pos ha
  have hP : 0 < trigamma a ^ 2 + tetragamma a := trigamma_sq_add_tetragamma_pos ha
  rw [(hasDerivAt_cCrit ha).deriv]
  have hid : -(4 * tetragamma a) / trigamma a ^ 2 - 4
      = -(4 * (trigamma a ^ 2 + tetragamma a)) / trigamma a ^ 2 := by
    field
  rw [hid]
  exact div_neg_of_neg_of_pos (by linarith) (by positivity)

theorem continuousOn_cCrit_Ioi : ContinuousOn cCrit (Set.Ioi (0 : ℝ)) :=
  fun _ hx =>
    ((hasDerivAt_cCrit (Set.mem_Ioi.1 hx)).differentiableAt).continuousAt.continuousWithinAt

/-- **`prop:c-monotone`, the monotonicity half.**  `c(a) = 4/ψ₁(a)-4a+7/2` is strictly
decreasing on `(0,∞)`. -/
theorem strictAntiOn_cCrit : StrictAntiOn cCrit (Set.Ioi (0 : ℝ)) := by
  refine strictAntiOn_of_deriv_neg (convex_Ioi 0) continuousOn_cCrit_Ioi ?_
  intro x hx
  rw [interior_Ioi] at hx
  exact deriv_cCrit_neg (Set.mem_Ioi.1 hx)

/-- **`prop:c-monotone`.**  `c` is strictly decreasing on `(0,∞)`, tends to `7/2` at
`0` and to `3/2` at infinity, and therefore has exact range `(3/2,7/2)`. -/
theorem cCrit_strictAnti_and_range :
    StrictAntiOn cCrit (Set.Ioi (0 : ℝ))
      ∧ Tendsto cCrit (nhdsWithin 0 (Set.Ioi 0)) (𝓝 (7 / 2))
      ∧ Tendsto cCrit atTop (𝓝 (3 / 2))
      ∧ ∀ v ∈ Set.Ioo (3 / 2 : ℝ) (7 / 2), ∃ a > 0, cCrit a = v :=
  ⟨strictAntiOn_cCrit, tendsto_cCrit_zero, tendsto_cCrit_atTop, fun _ hv => exists_cCrit_eq hv⟩

end TuranBessel
