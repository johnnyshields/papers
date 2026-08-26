/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import TuranBessel.Trigamma

/-!
# The tetragamma function, and `ψ₁² + ψ₂ > 0`

Formalizes `shields-2026-turan-bessel.tex`, «Critical wall fan and equivalence of
ensembles» (`sec:scaling`, `prop:c-monotone`).

`Trigamma` builds `ψ₁(y) = ∑_{n≥0}(y+n)⁻²` from the series and proves the two
sharp bounds `eq:trig-lower` and `eq:trig-upper-half`.  This module does the same
one derivative further, `ψ₂(y) = -2∑_{n≥0}(y+n)⁻³`, and proves the single fact
about the pair that `prop:c-monotone` consumes:

```
  ψ₁(y)² + ψ₂(y) > 0        (y > 0).
```

`ψ₂` is also identified as `ψ₁'` (`hasDerivAt_trigamma`), by differentiating the
defining series term by term; that is what turns the inequality into the sign of
`c'`.

Sorry-free.
-/

namespace TuranBessel

open Filter Topology

variable {y : ℝ}

/-! ### The series -/

/-- Tetragamma function `ψ₂(y) = -2∑_{n≥0}(y+n)⁻³`. -/
noncomputable def tetragamma (y : ℝ) : ℝ := -2 * ∑' n : ℕ, (y + (n : ℝ))⁻¹ ^ 3

theorem tetragamma_summable (hy : 0 < y) :
    Summable (fun n : ℕ => (y + (n : ℝ))⁻¹ ^ 3) := by
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    ((trigamma_summable hy).mul_left y⁻¹)
  have hyn : (0 : ℝ) < y + (n : ℝ) := by
    have := Nat.cast_nonneg (α := ℝ) n; linarith
  have h1 : (y + (n : ℝ))⁻¹ ≤ y⁻¹ := inv_anti₀ hy (by linarith)
  have h2 : (0 : ℝ) ≤ (y + (n : ℝ))⁻¹ ^ 2 := by positivity
  calc (y + (n : ℝ))⁻¹ ^ 3 = (y + (n : ℝ))⁻¹ * (y + (n : ℝ))⁻¹ ^ 2 := by ring
    _ ≤ y⁻¹ * (y + (n : ℝ))⁻¹ ^ 2 := mul_le_mul_of_nonneg_right h1 h2

/-- `ψ₂ < 0` on `(0,∞)`: every term of the series is positive. -/
theorem tetragamma_neg (hy : 0 < y) : tetragamma y < 0 := by
  have hpos : 0 < ∑' n : ℕ, (y + (n : ℝ))⁻¹ ^ 3 := by
    refine (tetragamma_summable hy).tsum_pos (fun n => by positivity) 0 ?_
    positivity
  rw [tetragamma]; nlinarith

/-- `|ψ₂(y)| ≤ 2ψ₁(y)/y`: the extra factor over the trigamma series is `(y+n)⁻¹`,
bounded by `y⁻¹`. -/
theorem neg_tetragamma_le (hy : 0 < y) : -tetragamma y ≤ 2 * trigamma y / y := by
  have hle : (∑' n : ℕ, (y + (n : ℝ))⁻¹ ^ 3) ≤ y⁻¹ * trigamma y := by
    refine (tetragamma_summable hy).tsum_le_tsum (fun n => ?_)
      ((trigamma_summable hy).mul_left y⁻¹) |>.trans_eq ?_
    · have hyn : (0 : ℝ) < y + (n : ℝ) := by
        have := Nat.cast_nonneg (α := ℝ) n; linarith
      have h1 : (y + (n : ℝ))⁻¹ ≤ y⁻¹ := inv_anti₀ hy (by linarith)
      have h2 : (0 : ℝ) ≤ (y + (n : ℝ))⁻¹ ^ 2 := by positivity
      calc (y + (n : ℝ))⁻¹ ^ 3 = (y + (n : ℝ))⁻¹ * (y + (n : ℝ))⁻¹ ^ 2 := by ring
        _ ≤ y⁻¹ * (y + (n : ℝ))⁻¹ ^ 2 := mul_le_mul_of_nonneg_right h1 h2
    · rw [tsum_mul_left]; rfl
  rw [tetragamma]
  have : y⁻¹ * trigamma y = 2 * trigamma y / y / 2 := by
    field_simp
  nlinarith [hle, this]

/-- Recurrence `ψ₂(y) = -2y⁻³ + ψ₂(y+1)`. -/
theorem tetragamma_succ (hy : 0 < y) :
    tetragamma y = -2 * (y⁻¹) ^ 3 + tetragamma (y + 1) := by
  have hsum := tetragamma_summable hy
  rw [tetragamma, hsum.tsum_eq_zero_add, tetragamma]
  have hshift : (∑' n : ℕ, (y + ((n + 1 : ℕ) : ℝ))⁻¹ ^ 3)
      = ∑' n : ℕ, (y + 1 + (n : ℝ))⁻¹ ^ 3 :=
    tsum_congr (fun n => by
      rw [show y + ((n + 1 : ℕ) : ℝ) = y + 1 + (n : ℝ) from by push_cast; ring])
  rw [hshift]
  norm_num
  ring

/-! ### The positivity of `ψ₁² + ψ₂`

**Differs from the paper's route.**  `prop:c-monotone` proves `ψ₁²+ψ₂>0` from the
Laplace representations of `ψ₁` and `ψ₂`, through a convolution identity for
`k(t)=t/(1-e^{-t})` and the inequality `x\coth x>1`.  What is done here needs no
integral at all: the two recurrences give the exact one-step drop
`P(y)-P(y+1) = y⁻⁴ - 2y⁻³ + 2ψ₁(y+1)y⁻²`, and `eq:trig-lower` at `y+1` makes it
positive, by the exact margin `(2y+3)y² - (2y-1)(y+1)² = 1`.  So `P` strictly
decreases by unit steps to its limit `0`, which is the whole proof.  The margin is
one, not more: the crude `ψ₁(y+1)>1/(y+1)` fails for every `y>1`, so the sharp
lower bound is load-bearing here (`scripts/check_polygamma_positivity.py`). -/

/-- `P(y) = ψ₁(y)² + ψ₂(y)`, the combination whose sign is the sign of `-c'`. -/
noncomputable def polygammaCombo (y : ℝ) : ℝ := trigamma y ^ 2 + tetragamma y

/-- The one-step descent `P(y+1) < P(y)`, the whole content of the positivity. -/
theorem polygammaCombo_succ_lt (hy : 0 < y) : polygammaCombo (y + 1) < polygammaCombo y := by
  have hy1 : (0 : ℝ) < y + 1 := by linarith
  have hT := trigamma_succ hy
  have hU := tetragamma_succ hy
  have hsharp := trigamma_gt_inv_sharp hy1
  set T : ℝ := trigamma (y + 1) with hTdef
  -- `eq:trig-lower` at `y+1`, cleared of inverses
  have hlow : (2 * y + 3) ≤ 2 * (y + 1) ^ 2 * T := by
    have h1 : (y + 1)⁻¹ = 1 / (y + 1) := by rw [one_div]
    have h2 : ((y + 1) ^ 2)⁻¹ = 1 / (y + 1) ^ 2 := by rw [one_div]
    rw [h1, h2] at hsharp
    have hpos : (0 : ℝ) < (y + 1) ^ 2 := by positivity
    have := mul_lt_mul_of_pos_left hsharp (by positivity : (0:ℝ) < 2 * (y + 1) ^ 2)
    have hid : 2 * (y + 1) ^ 2 * (1 / (y + 1) + 1 / 2 * (1 / (y + 1) ^ 2)) = 2 * y + 3 := by
      field_simp; ring
    linarith [hid ▸ this]
  -- the requirement, cleared: `2 T y² ≥ 2y - 1`, with margin `1/((y+1)²)`
  have hyinv : y⁻¹ = 1 / y := by rw [one_div]
  have hkey : 2 * y - 1 < 2 * y ^ 2 * T := by
    have hmargin : (2 * y + 3) * y ^ 2 - (2 * y - 1) * (y + 1) ^ 2 = 1 := by ring
    have hp1 : (0 : ℝ) < (y + 1) ^ 2 := by positivity
    have hy2 : (0 : ℝ) < y ^ 2 := by positivity
    nlinarith [hlow, hmargin, hp1, hy2]
  -- assemble
  have hdrop : polygammaCombo y - polygammaCombo (y + 1)
      = (y⁻¹) ^ 4 + 2 * (y⁻¹) ^ 2 * T - 2 * (y⁻¹) ^ 3 := by
    rw [polygammaCombo, polygammaCombo, hT, hU, ← hTdef]
    ring
  have hpos : 0 < (y⁻¹) ^ 4 + 2 * (y⁻¹) ^ 2 * T - 2 * (y⁻¹) ^ 3 := by
    rw [hyinv]
    have hy4 : (0 : ℝ) < y ^ 4 := by positivity
    have hexp : (1 / y) ^ 4 + 2 * (1 / y) ^ 2 * T - 2 * (1 / y) ^ 3
        = (1 + 2 * y ^ 2 * T - 2 * y) / y ^ 4 := by field_simp
    rw [hexp]
    exact div_pos (by linarith) hy4
  linarith [hdrop, hpos]

theorem polygammaCombo_add_nat_le (hy : 0 < y) (n : ℕ) :
    polygammaCombo (y + (n : ℝ)) ≤ polygammaCombo y := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hyn : (0 : ℝ) < y + (n : ℝ) := by
        have := Nat.cast_nonneg (α := ℝ) n; linarith
      have hstep := polygammaCombo_succ_lt hyn
      rw [show y + ((n + 1 : ℕ) : ℝ) = y + (n : ℝ) + 1 from by push_cast; ring]
      linarith

/-! ### The limit at infinity -/

private theorem tendsto_add_nat (hy : 0 < y) :
    Tendsto (fun n : ℕ => y + (n : ℝ)) atTop atTop :=
  tendsto_atTop_mono (fun n => by linarith [Nat.cast_nonneg (α := ℝ) n] :
    ∀ n : ℕ, (n : ℝ) ≤ y + (n : ℝ)) tendsto_natCast_atTop_atTop

theorem tendsto_trigamma_add_nat (hy : 0 < y) :
    Tendsto (fun n : ℕ => trigamma (y + (n : ℝ))) atTop (𝓝 0) := by
  have hmaj : Tendsto (fun n : ℕ => (y + (n : ℝ) - 1 / 2)⁻¹) atTop (𝓝 0) := by
    refine Tendsto.inv_tendsto_atTop ?_
    exact tendsto_atTop_add_const_right _ _ (tendsto_add_nat hy)
  refine squeeze_zero' ?_ ?_ hmaj
  · filter_upwards with n
    have hyn : (0 : ℝ) < y + (n : ℝ) := by
      have := Nat.cast_nonneg (α := ℝ) n; linarith
    exact (trigamma_pos hyn).le
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    exact (trigamma_lt_upper (by linarith : (1:ℝ)/2 < y + (n : ℝ))).le

theorem tendsto_tetragamma_add_nat (hy : 0 < y) :
    Tendsto (fun n : ℕ => tetragamma (y + (n : ℝ))) atTop (𝓝 0) := by
  have hneg : Tendsto (fun n : ℕ => -tetragamma (y + (n : ℝ))) atTop (𝓝 0) := by
    have hmaj : Tendsto (fun n : ℕ => 2 * trigamma (y + (n : ℝ))) atTop (𝓝 0) := by
      simpa using (tendsto_trigamma_add_nat hy).const_mul 2
    refine squeeze_zero' ?_ ?_ hmaj
    · filter_upwards with n
      have hyn : (0 : ℝ) < y + (n : ℝ) := by
        have := Nat.cast_nonneg (α := ℝ) n; linarith
      linarith [tetragamma_neg hyn]
    · filter_upwards [eventually_ge_atTop 1] with n hn
      have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      have hyn : (1 : ℝ) ≤ y + (n : ℝ) := by linarith
      have hyn0 : (0 : ℝ) < y + (n : ℝ) := by linarith
      have h := neg_tetragamma_le hyn0
      have hT : 0 < trigamma (y + (n : ℝ)) := trigamma_pos hyn0
      have : 2 * trigamma (y + (n : ℝ)) / (y + (n : ℝ)) ≤ 2 * trigamma (y + (n : ℝ)) := by
        rw [div_le_iff₀ hyn0]; nlinarith
      linarith
  simpa using hneg.neg

theorem tendsto_polygammaCombo_add_nat (hy : 0 < y) :
    Tendsto (fun n : ℕ => polygammaCombo (y + (n : ℝ))) atTop (𝓝 0) := by
  have h := ((tendsto_trigamma_add_nat hy).pow 2).add (tendsto_tetragamma_add_nat hy)
  simpa [polygammaCombo] using h

/-- **`ψ₁(a)² + ψ₂(a) > 0` for `a > 0`** (`prop:c-monotone`).  `P` drops strictly at
every unit step and its limit along `y + ℕ` is `0`, so `P(y) > P(y+1) ≥ 0`. -/
theorem polygammaCombo_pos (hy : 0 < y) : 0 < polygammaCombo y := by
  have hy1 : (0 : ℝ) < y + 1 := by linarith
  have hnn : 0 ≤ polygammaCombo (y + 1) :=
    le_of_tendsto (tendsto_polygammaCombo_add_nat hy1)
      (Eventually.of_forall fun n => polygammaCombo_add_nat_le hy1 n)
  linarith [polygammaCombo_succ_lt hy]

/-- `ψ₁(y)² + ψ₂(y) > 0`, written out. -/
theorem trigamma_sq_add_tetragamma_pos (hy : 0 < y) :
    0 < trigamma y ^ 2 + tetragamma y := polygammaCombo_pos hy

/-! ### `ψ₁' = ψ₂` -/

private theorem hasDerivAt_inv_sq_term (n : ℕ) {z : ℝ} (hz : 0 < z) :
    HasDerivAt (fun w : ℝ => (w + (n : ℝ))⁻¹ ^ 2) (-2 * (z + (n : ℝ))⁻¹ ^ 3) z := by
  have hzn : (0 : ℝ) < z + (n : ℝ) := by
    have := Nat.cast_nonneg (α := ℝ) n; linarith
  have hlin : HasDerivAt (fun w : ℝ => w + (n : ℝ)) 1 z := (hasDerivAt_id z).add_const _
  have hne : z + (n : ℝ) ≠ 0 := hzn.ne'
  have hinv : HasDerivAt (fun w : ℝ => (w + (n : ℝ))⁻¹) (-1 / (z + (n : ℝ)) ^ 2) z :=
    hlin.inv hne
  refine (hinv.pow 2).congr_deriv ?_
  push_cast
  field_simp

/-- **`ψ₁' = ψ₂`.**  The defining series of `ψ₁` differentiates term by term: on any
`(c,∞)` with `c>0` the derivatives are dominated by the summable `2(c+n)⁻³`. -/
theorem hasDerivAt_trigamma (hy : 0 < y) : HasDerivAt trigamma (tetragamma y) y := by
  set c : ℝ := y / 2 with hc
  have hc0 : 0 < c := by rw [hc]; linarith
  have hyc : y ∈ Set.Ioi c := by rw [Set.mem_Ioi, hc]; linarith
  have hu : Summable (fun n : ℕ => 2 * (c + (n : ℝ))⁻¹ ^ 3) :=
    (tetragamma_summable hc0).mul_left 2
  have hkey : HasDerivAt (fun w : ℝ => ∑' n : ℕ, (w + (n : ℝ))⁻¹ ^ 2)
      (∑' n : ℕ, -2 * (y + (n : ℝ))⁻¹ ^ 3) y := by
    refine hasDerivAt_tsum_of_isPreconnected hu isOpen_Ioi isPreconnected_Ioi
      (fun n z hz => hasDerivAt_inv_sq_term n (lt_trans hc0 hz)) (fun n z hz => ?_)
      hyc (trigamma_summable (lt_trans hc0 hyc)) hyc
    have hz0 : 0 < z := lt_trans hc0 hz
    have hzn : (0 : ℝ) < z + (n : ℝ) := by
      have := Nat.cast_nonneg (α := ℝ) n; linarith
    have hcn : (0 : ℝ) < c + (n : ℝ) := by
      have := Nat.cast_nonneg (α := ℝ) n; linarith
    have hnp : -2 * (z + (n : ℝ))⁻¹ ^ 3 ≤ 0 := by
      have : (0 : ℝ) < (z + (n : ℝ))⁻¹ ^ 3 := by positivity
      linarith
    rw [Real.norm_eq_abs, abs_of_nonpos hnp]
    have hmono : (z + (n : ℝ))⁻¹ ^ 3 ≤ (c + (n : ℝ))⁻¹ ^ 3 := by
      have : (z + (n : ℝ))⁻¹ ≤ (c + (n : ℝ))⁻¹ :=
        inv_anti₀ hcn (by linarith [Set.mem_Ioi.1 hz])
      exact pow_le_pow_left₀ (by positivity) this 3
    linarith
  have hval : (∑' n : ℕ, -2 * (y + (n : ℝ))⁻¹ ^ 3) = tetragamma y := by
    rw [tetragamma, ← tsum_mul_left]
  rw [hval] at hkey
  exact hkey.congr_deriv rfl

end TuranBessel
