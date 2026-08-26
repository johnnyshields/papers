/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import TuranBessel.WallOrder

/-!
# Critical scaling: what is exact, and what the asymptotics still owe

`shields-2026-turan-bessel.tex`, `sec:scaling`
(`subsec:asymptotics-degree-thresholds`, `eq:Sm-gamma-ratio`,
`eq:alpha-asymptotic`, `eq:c-range`, `thm:critical-scaling`,
`lem:central-moments`).

`thm:critical-scaling` runs on three inputs.  Two of the three have exact
substitutes here and the third does not:

* **`eq:Sm-gamma-ratio` is an identity, not an estimate** — Legendre duplication
  rewrites `S_m` as a pair of gamma ratios (`sweight_eq_gamma_ratio`).  Mathlib
  carries the duplication formula, so this whole step is unconditional.
* **`eq:alpha-asymptotic` is available two terms deep** with an explicit
  constant, because the sharp trigamma bounds already proved sandwich `ψ₁` between
  `x⁻¹ + x⁻²/2` and `x⁻¹ + x⁻²/2 + x⁻³/6` (`abs_alpha_sub_two_term_le`).  The
  paper's third term needs the *next* order of that sandwich.
* **`eq:Sm-asymptotic` has no substrate.**  It is the gamma-ratio expansion
  `Γ(m+α)/Γ(m+β) = m^{α-β}(1 + c/m + O(m^{-2}))` (DLMF §5.11(iii)), which the
  pinned Mathlib does not carry in any form: `Analysis/SpecialFunctions/Stirling`
  gives the leading equivalence for factorials and nothing about a next-order
  coefficient, and there is no digamma or log-gamma asymptotic expansion to
  integrate.  Nor is there Laplace-type concentration for the tilted
  hypergeometric law that `lem:central-moments` needs.  So `eq:X2-asymptotic`,
  `eq:tilted-tail`, `eq:kappa-n-two-term` and `cor:eventual-negative-tail` are
  not attempted.

`eq:c-range` closes here in both directions: `Phase.cCrit_gt` had the lower half,
and the upper half is `aψ₁(a) > 1`, already proved.

Sorry-free.
-/

namespace TuranBessel

open Real

variable {a : ℝ} {m : ℕ}

/-! ### `eq:c-range` -/

/-- **`c(a) < 7/2`** (`eq:c-range`).  `c(a) = 4/ψ₁(a) - 4a + 7/2`, so this is
exactly `aψ₁(a) > 1`. -/
theorem cCrit_lt (ha : 0 < a) : cCrit a < 7 / 2 := by
  have hg : 0 < trigamma a := trigamma_pos ha
  have h := a_trigamma_gt_one ha
  have hinv : 4 / trigamma a < 4 * a := by
    rw [div_lt_iff₀ hg]
    nlinarith
  rw [cCrit]
  linarith

/-- **`eq:c-range`.**  `3/2 < c(a) < 7/2` for every `a > 0`. -/
theorem cCrit_mem (ha : 0 < a) : cCrit a ∈ Set.Ioo (3 / 2 : ℝ) (7 / 2) :=
  ⟨cCrit_gt ha, cCrit_lt ha⟩

/-! ### `eq:Sm-gamma-ratio`

Legendre duplication at `s = a + m - 1/2` turns the single gamma `Γ(2a+2m-1)`
hiding inside the Pochhammer numerator of `S_m` into `Γ(a+m-1/2)Γ(a+m)`, which is
what separates the `m`-dependence into `4^m/(m!)²` times two gamma ratios of
fixed shift. -/

private theorem alg_Sm (N Dn Gh Ga F S U V : ℝ)
    (hDn : Dn ≠ 0) (hGa : Ga ≠ 0) (hF : F ≠ 0) (hS : S ≠ 0)
    (h : N = Gh * Ga * (U * V) / S) :
    N / Dn / (F * Ga ^ 2) = U / S * (V / F ^ 2) * (Gh / Ga) * (F / Dn) := by
  subst h
  field_simp

/-- **`eq:Sm-gamma-ratio`.**  For `a > 0` and `m ≥ 1`,
`S_m = (2^{2a-2}/√π)(4^m/(m!)²)·Γ(a+m-1/2)/Γ(a+m)·Γ(m+1)/Γ(2a+m-1)`.  An
identity, not an estimate: Mathlib carries Legendre duplication, so this step of
`lem:central-moments` is unconditional. -/
theorem sweight_eq_gamma_ratio (ha : 0 < a) (hm : 1 ≤ m) :
    sweight a m
      = (2 : ℝ) ^ (2 * a - 2) / Real.sqrt π * ((4 : ℝ) ^ m / (Nat.factorial m : ℝ) ^ 2)
        * (Real.Gamma (a + (m : ℝ) - 1 / 2) / Real.Gamma (a + (m : ℝ)))
        * (Real.Gamma ((m : ℝ) + 1) / Real.Gamma (2 * a + (m : ℝ) - 1)) := by
  have hmr : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hxpos : (0 : ℝ) < 2 * a + (m : ℝ) - 1 := by linarith
  have hamp : (0 : ℝ) < a + (m : ℝ) := by linarith
  have hfac : (0 : ℝ) < (Nat.factorial m : ℝ) := by exact_mod_cast Nat.factorial_pos m
  have hpi : (0 : ℝ) < Real.sqrt π := Real.sqrt_pos.2 Real.pi_pos
  -- the Pochhammer numerator as a gamma ratio
  have hpoch : poch (2 * a + (m : ℝ) - 1) m
      = Real.Gamma (2 * a + 2 * (m : ℝ) - 1) / Real.Gamma (2 * a + (m : ℝ) - 1) := by
    have h := Gamma_add_natCast hxpos m
    rw [show 2 * a + (m : ℝ) - 1 + (m : ℝ) = 2 * a + 2 * (m : ℝ) - 1 from by ring] at h
    rw [eq_div_iff (Real.Gamma_pos_of_pos hxpos).ne', h]
    ring
  -- Legendre duplication at `s = a + m - 1/2`
  have hdup : Real.Gamma (a + (m : ℝ) - 1 / 2) * Real.Gamma (a + (m : ℝ))
      = Real.Gamma (2 * a + 2 * (m : ℝ) - 1) * (2 : ℝ) ^ (2 - 2 * a - 2 * (m : ℝ))
        * Real.sqrt π := by
    have h := Real.Gamma_mul_Gamma_add_half (a + (m : ℝ) - 1 / 2)
    rw [show a + (m : ℝ) - 1 / 2 + 1 / 2 = a + (m : ℝ) from by ring,
      show 2 * (a + (m : ℝ) - 1 / 2) = 2 * a + 2 * (m : ℝ) - 1 from by ring,
      show 1 - (2 * a + 2 * (m : ℝ) - 1) = 2 - 2 * a - 2 * (m : ℝ) from by ring] at h
    exact h
  -- the two powers of `2` are reciprocal
  have hpow : (2 : ℝ) ^ (2 - 2 * a - 2 * (m : ℝ))
      * ((2 : ℝ) ^ (2 * a - 2) * (4 : ℝ) ^ m) = 1 := by
    have h4 : (4 : ℝ) ^ m = (2 : ℝ) ^ (2 * (m : ℝ)) := by
      rw [show (2 * (m : ℝ)) = ((2 * m : ℕ) : ℝ) from by push_cast; ring,
        Real.rpow_natCast, pow_mul]
      norm_num
    rw [h4, ← Real.rpow_add (by norm_num : (0:ℝ) < 2),
      ← Real.rpow_add (by norm_num : (0:ℝ) < 2),
      show 2 - 2 * a - 2 * (m : ℝ) + (2 * a - 2 + 2 * (m : ℝ)) = 0 from by ring,
      Real.rpow_zero]
  have hG1 : Real.Gamma (2 * a + 2 * (m : ℝ) - 1)
      = Real.Gamma (a + (m : ℝ) - 1 / 2) * Real.Gamma (a + (m : ℝ))
        * ((2 : ℝ) ^ (2 * a - 2) * (4 : ℝ) ^ m) / Real.sqrt π := by
    rw [eq_div_iff hpi.ne']
    calc Real.Gamma (2 * a + 2 * (m : ℝ) - 1) * Real.sqrt π
        = Real.Gamma (2 * a + 2 * (m : ℝ) - 1)
            * ((2 : ℝ) ^ (2 - 2 * a - 2 * (m : ℝ))
              * ((2 : ℝ) ^ (2 * a - 2) * (4 : ℝ) ^ m)) * Real.sqrt π := by
          rw [hpow]; ring
      _ = Real.Gamma (2 * a + 2 * (m : ℝ) - 1) * (2 : ℝ) ^ (2 - 2 * a - 2 * (m : ℝ))
            * Real.sqrt π * ((2 : ℝ) ^ (2 * a - 2) * (4 : ℝ) ^ m) := by ring
      _ = Real.Gamma (a + (m : ℝ) - 1 / 2) * Real.Gamma (a + (m : ℝ))
            * ((2 : ℝ) ^ (2 * a - 2) * (4 : ℝ) ^ m) := by rw [← hdup]
  have hΓm : Real.Gamma ((m : ℝ) + 1) = (Nat.factorial m : ℝ) := by
    rw [show ((m : ℝ) + 1) = ((m : ℕ) : ℝ) + 1 from rfl, Real.Gamma_nat_eq_factorial]
  rw [sweight, hpoch, hΓm]
  exact alg_Sm _ _ _ _ _ _ _ _ (Real.Gamma_pos_of_pos hxpos).ne'
    (Real.Gamma_pos_of_pos hamp).ne' hfac.ne' hpi.ne' hG1

/-! ### `eq:alpha-asymptotic`, two terms deep

`α_m = ψ₁(a+m)`, and the sharp trigamma bounds already proved sandwich `ψ₁(x)`
between `x⁻¹ + x⁻²/2` and `x⁻¹ + x⁻²/2 + x⁻³/6`.  Re-expanding those two
denominators at `x = a+m` in powers of `m⁻¹` is exact, so the first two terms of
`eq:alpha-asymptotic` come out with a written-down constant.  The paper's third
term needs the next order of the sandwich, which is the same Euler--Maclaurin
step one power further and is not done here. -/

/-- Cross-multiplied comparison of two quotients, with both denominators positive.
Used throughout `sec:scaling` in place of `div_le_div_iff`. -/
theorem alg_div_le {X Y D1 D2 : ℝ} (h1 : 0 < D1) (h2 : 0 < D2)
    (h : X * D2 ≤ Y * D1) : X / D1 ≤ Y / D2 := by
  have n1 : D1 ≠ 0 := h1.ne'
  have n2 : D2 ≠ 0 := h2.ne'
  have hid : Y / D2 - X / D1 = (Y * D1 - X * D2) / (D1 * D2) := by
    field_simp
  have hnn : 0 ≤ Y / D2 - X / D1 := by
    rw [hid]; exact div_nonneg (by linarith) (mul_pos h1 h2).le
  linarith

private theorem alg_inv2 (X : ℝ) (hX : X ≠ 0) :
    1 / X + 1 / (2 * X ^ 2) = X⁻¹ + (1 / 2) * ((X : ℝ) ^ 2)⁻¹ := by
  field_simp

private theorem alg_sixth (X : ℝ) (hX : X ≠ 0) : 1 / (6 * X) = (1 / 6) / X := by
  field_simp

private theorem alg_add_div (X Y D : ℝ) : X / D + Y / D = (X + Y) / D := by
  ring

private theorem pow_le_pow_of_le_nonneg {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (n : ℕ) :
    x ^ n ≤ y ^ n := by
  induction n with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, pow_succ]
      exact mul_le_mul ih hxy hx (pow_nonneg (hx.trans hxy) k)

/-- **`eq:alpha-asymptotic`, truncated after two terms**, with the constant
written out: `|ψ₁(a+m) - m⁻¹ - (1/2-a)m⁻²| ≤ (a(3a+2)/2 + 1/6)m⁻³`. -/
theorem abs_alpha_sub_two_term_le (ha : 0 < a) (hm : 1 ≤ m) :
    |αcoef a m - (1 / (m : ℝ) + (1 / 2 - a) / (m : ℝ) ^ 2)|
      ≤ (a * (3 * a + 2) / 2 + 1 / 6) / (m : ℝ) ^ 3 := by
  have hM : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hM0 : (0 : ℝ) < (m : ℝ) := by linarith
  have hx : (0 : ℝ) < a + (m : ℝ) := by linarith
  have hlow := trigamma_gt_inv_sharp hx
  have hup := trigamma_lt_cubic hx
  -- exact re-expansion of the two leading terms
  have hid : (a + (m : ℝ))⁻¹ + (1 / 2) * ((a + (m : ℝ)) ^ 2)⁻¹
      = 1 / (m : ℝ) + (1 / 2 - a) / (m : ℝ) ^ 2
        + (a ^ 2 / ((m : ℝ) ^ 2 * (a + (m : ℝ)))
            - a * (2 * (m : ℝ) + a) / (2 * (m : ℝ) ^ 2 * (a + (m : ℝ)) ^ 2)) := by
    have n1 : (a + (m : ℝ)) ≠ 0 := hx.ne'
    have n2 : (m : ℝ) ≠ 0 := hM0.ne'
    field
  -- two-sided bounds on the remainder
  have hRup : a ^ 2 / ((m : ℝ) ^ 2 * (a + (m : ℝ)))
        - a * (2 * (m : ℝ) + a) / (2 * (m : ℝ) ^ 2 * (a + (m : ℝ)) ^ 2)
      ≤ a ^ 2 / (m : ℝ) ^ 3 := by
    have hc : a ^ 2 * ((m : ℝ) ^ 2 * (a + (m : ℝ))) - a ^ 2 * (m : ℝ) ^ 3
        = a ^ 3 * (m : ℝ) ^ 2 := by ring
    have hp : (0 : ℝ) ≤ a ^ 3 * (m : ℝ) ^ 2 :=
      mul_nonneg (pow_nonneg ha.le 3) (sq_nonneg _)
    have h1 : a ^ 2 / ((m : ℝ) ^ 2 * (a + (m : ℝ))) ≤ a ^ 2 / (m : ℝ) ^ 3 :=
      alg_div_le (mul_pos (pow_pos hM0 2) hx) (pow_pos hM0 3) (by linarith)
    have h2 : 0 ≤ a * (2 * (m : ℝ) + a) / (2 * (m : ℝ) ^ 2 * (a + (m : ℝ)) ^ 2) := by
      refine div_nonneg (mul_nonneg ha.le (by linarith)) ?_
      have : (0 : ℝ) < 2 * (m : ℝ) ^ 2 := by positivity
      nlinarith [sq_nonneg (a + (m : ℝ)), this]
    linarith
  have hRlow : -(a * (2 + a) / (2 * (m : ℝ) ^ 3))
      ≤ a ^ 2 / ((m : ℝ) ^ 2 * (a + (m : ℝ)))
        - a * (2 * (m : ℝ) + a) / (2 * (m : ℝ) ^ 2 * (a + (m : ℝ)) ^ 2) := by
    have h1 : 0 ≤ a ^ 2 / ((m : ℝ) ^ 2 * (a + (m : ℝ))) :=
      div_nonneg (sq_nonneg a) (mul_pos (pow_pos hM0 2) hx).le
    have hcert : a * (2 + a) * (2 * (m : ℝ) ^ 2 * (a + (m : ℝ)) ^ 2)
          - a * (2 * (m : ℝ) + a) * (2 * (m : ℝ) ^ 3)
        = 2 * a * (m : ℝ) ^ 2
          * (a ^ 3 + 2 * a ^ 2 * (m : ℝ) + 2 * a ^ 2 + a * (m : ℝ) ^ 2 + 3 * a * (m : ℝ)) := by
      ring
    have hf1 : (0 : ℝ) < 2 * a * (m : ℝ) ^ 2 :=
      mul_pos (by linarith) (pow_pos hM0 2)
    have hf2 : (0 : ℝ) < a ^ 3 + 2 * a ^ 2 * (m : ℝ) + 2 * a ^ 2
        + a * (m : ℝ) ^ 2 + 3 * a * (m : ℝ) := by
      have t1 : (0 : ℝ) < a ^ 3 := pow_pos ha 3
      have t2 : (0 : ℝ) ≤ 2 * a ^ 2 * (m : ℝ) := mul_nonneg (by positivity) hM0.le
      have t3 : (0 : ℝ) < 2 * a ^ 2 := by positivity
      have t4 : (0 : ℝ) ≤ a * (m : ℝ) ^ 2 := mul_nonneg ha.le (sq_nonneg _)
      have t5 : (0 : ℝ) ≤ 3 * a * (m : ℝ) := mul_nonneg (by linarith) hM0.le
      linarith
    have h2 : a * (2 * (m : ℝ) + a) / (2 * (m : ℝ) ^ 2 * (a + (m : ℝ)) ^ 2)
        ≤ a * (2 + a) / (2 * (m : ℝ) ^ 3) := by
      refine alg_div_le ?_ (by positivity) ?_
      · have : (0 : ℝ) < (a + (m : ℝ)) ^ 2 := by positivity
        nlinarith [pow_pos hM0 2, this]
      · nlinarith [hcert, mul_pos hf1 hf2]
    linarith
  have hcube : 1 / (6 * (a + (m : ℝ)) ^ 3) ≤ 1 / (6 * (m : ℝ) ^ 3) := by
    have hc : (a + (m : ℝ)) ^ 3 - (m : ℝ) ^ 3
        = a ^ 3 + 3 * a ^ 2 * (m : ℝ) + 3 * a * (m : ℝ) ^ 2 := by ring
    have t1 : (0 : ℝ) ≤ a ^ 3 := pow_nonneg ha.le 3
    have t2 : (0 : ℝ) ≤ 3 * a ^ 2 * (m : ℝ) := mul_nonneg (by positivity) hM0.le
    have t3 : (0 : ℝ) ≤ 3 * a * (m : ℝ) ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
    refine alg_div_le ?_ (by positivity) (by linarith)
    have : (0 : ℝ) < (a + (m : ℝ)) ^ 3 := by positivity
    linarith
  have hupc := alg_inv2 (a + (m : ℝ)) hx.ne'
  have hC1 : a * (2 + a) / (2 * (m : ℝ) ^ 3)
      ≤ (a * (3 * a + 2) / 2 + 1 / 6) / (m : ℝ) ^ 3 := by
    refine alg_div_le (by positivity) (pow_pos hM0 3) ?_
    nlinarith [pow_pos hM0 3, sq_nonneg a]
  have hC2 : a ^ 2 / (m : ℝ) ^ 3 + 1 / (6 * (m : ℝ) ^ 3)
      ≤ (a * (3 * a + 2) / 2 + 1 / 6) / (m : ℝ) ^ 3 := by
    rw [alg_sixth ((m : ℝ) ^ 3) (pow_pos hM0 3).ne', alg_add_div]
    refine alg_div_le (pow_pos hM0 3) (pow_pos hM0 3) ?_
    nlinarith [pow_pos hM0 3, sq_nonneg a]
  rw [αcoef, abs_le]
  rw [hupc, hid] at hup
  rw [hid] at hlow
  constructor
  · linarith [hlow, hRlow, hC1]
  · linarith [hup, hRup, hcube, hC2]

/-! ### The cubic trigamma minorant, and `eq:alpha-asymptotic` in full

`Phase.cubicMaj` bounds `ψ₁` above by `y⁻¹ + y⁻²/2 + y⁻³/6`; the third term of
`eq:alpha-asymptotic` needs a matching bound below.  `cubicMin` subtracts
`y⁻⁴/20`, and that is enough for the same telescoping argument to run in the
other direction: the surplus in the step inequality is
`-(12y³+8y²+2y+3)/(60y⁴(y+1)⁴)`, negative for every `y > 0`. -/

/-- `1/y + 1/(2y²) + 1/(6y³) - 1/(20y⁴)`, the minorant matching `Phase.cubicMaj`. -/
noncomputable def cubicMin (y : ℝ) : ℝ :=
  1 / y + 1 / (2 * y ^ 2) + 1 / (6 * y ^ 3) - 1 / (20 * y ^ 4)

theorem cubicMin_step {y : ℝ} (hy : 0 < y) : cubicMin y - cubicMin (y + 1) ≤ ((y : ℝ)⁻¹) ^ 2 := by
  have hy1 : (0 : ℝ) < y + 1 := by linarith
  have hinv : ((y : ℝ)⁻¹) ^ 2 = 1 / y ^ 2 := by rw [inv_pow, one_div]
  have key : cubicMin y - cubicMin (y + 1) - 1 / y ^ 2
      = -((12 * y ^ 3 + 8 * y ^ 2 + 2 * y + 3) / (60 * y ^ 4 * (y + 1) ^ 4)) := by
    unfold cubicMin; field_simp; ring
  have hpos : (0 : ℝ) < (12 * y ^ 3 + 8 * y ^ 2 + 2 * y + 3) / (60 * y ^ 4 * (y + 1) ^ 4) := by
    positivity
  rw [hinv]; linarith

theorem cubicMin_le_sum {y : ℝ} (hy : 0 < y) (N : ℕ) :
    cubicMin y - cubicMin (y + (N : ℝ)) ≤ ∑ i ∈ Finset.range N, ((y + (i : ℝ))⁻¹) ^ 2 := by
  have hyn : ∀ n : ℕ, (0 : ℝ) < y + (n : ℝ) := by
    intro n; have := Nat.cast_nonneg (α := ℝ) n; linarith
  have htel : ∀ M : ℕ,
      ∑ i ∈ Finset.range M, (cubicMin (y + (i : ℝ)) - cubicMin (y + (i : ℝ) + 1))
        = cubicMin y - cubicMin (y + (M : ℝ)) := by
    intro M
    induction M with
    | zero => simp
    | succ k ih =>
        rw [Finset.sum_range_succ, ih]
        have h : y + ((k : ℝ) + 1) = y + (k : ℝ) + 1 := by ring
        push_cast
        rw [h]
        ring
  have hle : ∑ i ∈ Finset.range N, (cubicMin (y + (i : ℝ)) - cubicMin (y + (i : ℝ) + 1))
      ≤ ∑ i ∈ Finset.range N, ((y + (i : ℝ))⁻¹) ^ 2 :=
    Finset.sum_le_sum (fun i _ => cubicMin_step (hyn i))
  rw [htel N] at hle
  exact hle

/-- `cubicMin y ≤ ψ₁(y)`.  The tail `cubicMin (y+N)` is below `2/(y+N)` once
`y+N ≥ 1`, so the telescoped bound sharpens to the tsum with no summability side
condition beyond nonnegativity of the terms. -/
theorem cubicMin_le_trigamma {y : ℝ} (hy : 0 < y) : cubicMin y ≤ trigamma y := by
  have hsum : Summable (fun n : ℕ => ((y + (n : ℝ))⁻¹) ^ 2) := trigamma_summable hy
  refine le_of_forall_pos_le_add ?_
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt (max (2 / ε) 1)
  have hN1 : (1 : ℝ) < (N : ℝ) := lt_of_le_of_lt (le_max_right _ _) hN
  have hNe : 2 / ε < (N : ℝ) := lt_of_le_of_lt (le_max_left _ _) hN
  have ht : (1 : ℝ) < y + (N : ℝ) := by linarith
  have htail : cubicMin (y + (N : ℝ)) ≤ 2 / (y + (N : ℝ)) := by
    have h1 : (0 : ℝ) < y + (N : ℝ) := by linarith
    have e2 : (1 : ℝ) ≤ (y + (N : ℝ)) ^ 2 := by nlinarith
    have e3 : (1 : ℝ) ≤ (y + (N : ℝ)) ^ 3 := by nlinarith
    have b1 : 1 / (2 * (y + (N : ℝ)) ^ 2) ≤ 1 / (2 * (y + (N : ℝ))) := by
      apply alg_div_le (by positivity) (by positivity)
      nlinarith
    have b2 : 1 / (6 * (y + (N : ℝ)) ^ 3) ≤ 1 / (6 * (y + (N : ℝ))) := by
      apply alg_div_le (by positivity) (by positivity)
      nlinarith
    have b3 : (0 : ℝ) ≤ 1 / (20 * (y + (N : ℝ)) ^ 4) := by positivity
    have hsplit : 1 / (y + (N : ℝ)) + 1 / (2 * (y + (N : ℝ))) + 1 / (6 * (y + (N : ℝ)))
        ≤ 2 / (y + (N : ℝ)) := by
      have hne : (y + (N : ℝ)) ≠ 0 := h1.ne'
      have he : 1 / (y + (N : ℝ)) + 1 / (2 * (y + (N : ℝ))) + 1 / (6 * (y + (N : ℝ)))
          = (5 / 3) / (y + (N : ℝ)) := by field_simp; ring
      rw [he]
      exact alg_div_le h1 h1 (by linarith)
    rw [cubicMin]
    linarith
  have hεN : 2 / (y + (N : ℝ)) < ε := by
    have h1 : (0 : ℝ) < y + (N : ℝ) := by linarith
    rw [div_lt_iff₀ h1]
    have : 2 / ε < y + (N : ℝ) := by linarith
    rw [div_lt_iff₀ hε] at this
    linarith
  have hpart : ∑ i ∈ Finset.range N, ((y + (i : ℝ))⁻¹) ^ 2 ≤ trigamma y := by
    rw [trigamma]
    exact hsum.sum_le_tsum _ (fun i _ => by positivity)
  linarith [cubicMin_le_sum hy N, hpart, htail, hεN]

/-- **The cubic trigamma sandwich.**  `|ψ₁(y) - (y⁻¹ + y⁻²/2 + y⁻³/6)| ≤ y⁻⁴/20`. -/
theorem abs_trigamma_sub_cubic_le {y : ℝ} (hy : 0 < y) :
    |trigamma y - (1 / y + 1 / (2 * y ^ 2) + 1 / (6 * y ^ 3))| ≤ 1 / (20 * y ^ 4) := by
  have hup := trigamma_le_cubicMaj hy
  have hlow := cubicMin_le_trigamma hy
  rw [cubicMaj] at hup
  rw [cubicMin] at hlow
  rw [abs_le]
  exact ⟨by linarith, by linarith⟩

private theorem alg_alpha3 (a M X : ℝ) (hM : M ≠ 0) (hX : X ≠ 0) (hXd : X = a + M) :
    (1 / X + 1 / (2 * X ^ 2) + 1 / (6 * X ^ 3))
        - (1 / M + (1 / 2 - a) / M ^ 2 + (a ^ 2 - a + 1 / 6) / M ^ 3)
      = -(a * (6 * a ^ 4 + 12 * a ^ 3 * M - 6 * a ^ 3 + 6 * a ^ 2 * M ^ 2 - 15 * a ^ 2 * M
              + a ^ 2 - 9 * a * M ^ 2 + 3 * a * M + 3 * M ^ 2)) / (6 * M ^ 3 * X ^ 3) := by
  field_simp
  subst hXd
  ring

/-- The numerator of `alg_alpha3` is below `M²K` with
`K = 6a⁴+18a³+22a²+12a+3`: in the shifted variable `t = M-1 ≥ 0` both
`KM² - Q` and `KM² + Q` have nonnegative coefficients throughout. -/
private theorem alg_Qbound {a t : ℝ} (ha : 0 ≤ a) (ht : 0 ≤ t) :
    |6 * a ^ 4 + 12 * a ^ 3 * (1 + t) - 6 * a ^ 3 + 6 * a ^ 2 * (1 + t) ^ 2
        - 15 * a ^ 2 * (1 + t) + a ^ 2 - 9 * a * (1 + t) ^ 2 + 3 * a * (1 + t)
        + 3 * (1 + t) ^ 2|
      ≤ (1 + t) ^ 2 * (6 * a ^ 4 + 18 * a ^ 3 + 22 * a ^ 2 + 12 * a + 3) := by
  have m1 : (0 : ℝ) ≤ t := ht
  have m2 : (0 : ℝ) ≤ t ^ 2 := by positivity
  have m3 : (0 : ℝ) ≤ a := ha
  have m4 : (0 : ℝ) ≤ a * t := mul_nonneg ha ht
  have m5 : (0 : ℝ) ≤ a * t ^ 2 := mul_nonneg ha m2
  have m6 : (0 : ℝ) ≤ a ^ 2 := by positivity
  have m7 : (0 : ℝ) ≤ a ^ 2 * t := mul_nonneg m6 ht
  have m8 : (0 : ℝ) ≤ a ^ 2 * t ^ 2 := mul_nonneg m6 m2
  have m9 : (0 : ℝ) ≤ a ^ 3 := pow_nonneg ha 3
  have m10 : (0 : ℝ) ≤ a ^ 3 * t := mul_nonneg m9 ht
  have m11 : (0 : ℝ) ≤ a ^ 3 * t ^ 2 := mul_nonneg m9 m2
  have m12 : (0 : ℝ) ≤ a ^ 4 := by positivity
  have m13 : (0 : ℝ) ≤ a ^ 4 * t := mul_nonneg m12 ht
  have m14 : (0 : ℝ) ≤ a ^ 4 * t ^ 2 := mul_nonneg m12 m2
  rw [abs_le]
  constructor <;> nlinarith [m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14]

/-- **`eq:alpha-asymptotic`, all three terms**, with the constant written out:
`|ψ₁(a+m) - m⁻¹ - (1/2-a)m⁻² - (a²-a+1/6)m⁻³| ≤ (1/20 + aK/6)m⁻⁴`, where
`K = 6a⁴+18a³+22a²+12a+3`. -/
theorem abs_alpha_sub_three_term_le (ha : 0 < a) (hm : 1 ≤ m) :
    |αcoef a m - (1 / (m : ℝ) + (1 / 2 - a) / (m : ℝ) ^ 2
        + (a ^ 2 - a + 1 / 6) / (m : ℝ) ^ 3)|
      ≤ (1 / 20 + a * (6 * a ^ 4 + 18 * a ^ 3 + 22 * a ^ 2 + 12 * a + 3) / 6) / (m : ℝ) ^ 4 := by
  have hM : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hM0 : (0 : ℝ) < (m : ℝ) := by linarith
  have hx : (0 : ℝ) < a + (m : ℝ) := by linarith
  set K : ℝ := 6 * a ^ 4 + 18 * a ^ 3 + 22 * a ^ 2 + 12 * a + 3 with hK
  set Q : ℝ := 6 * a ^ 4 + 12 * a ^ 3 * (m : ℝ) - 6 * a ^ 3 + 6 * a ^ 2 * (m : ℝ) ^ 2
      - 15 * a ^ 2 * (m : ℝ) + a ^ 2 - 9 * a * (m : ℝ) ^ 2 + 3 * a * (m : ℝ)
      + 3 * (m : ℝ) ^ 2 with hQ
  -- the exact remainder of the cubic approximation
  have hid : (1 / (a + (m : ℝ)) + 1 / (2 * (a + (m : ℝ)) ^ 2) + 1 / (6 * (a + (m : ℝ)) ^ 3))
        - (1 / (m : ℝ) + (1 / 2 - a) / (m : ℝ) ^ 2 + (a ^ 2 - a + 1 / 6) / (m : ℝ) ^ 3)
      = -(a * Q) / (6 * (m : ℝ) ^ 3 * (a + (m : ℝ)) ^ 3) := by
    rw [hQ]; exact alg_alpha3 a (m : ℝ) (a + (m : ℝ)) hM0.ne' hx.ne' rfl
  -- `|Q| ≤ m²K`
  have hQb : |Q| ≤ (m : ℝ) ^ 2 * K := by
    have h := alg_Qbound (a := a) (t := (m : ℝ) - 1) ha.le (by linarith)
    rw [show (1 : ℝ) + ((m : ℝ) - 1) = (m : ℝ) from by ring] at h
    rw [hQ, hK]
    exact h
  -- the cubic remainder bound
  have hcub : |αcoef a m - (1 / (a + (m : ℝ)) + 1 / (2 * (a + (m : ℝ)) ^ 2)
      + 1 / (6 * (a + (m : ℝ)) ^ 3))| ≤ 1 / (20 * (m : ℝ) ^ 4) := by
    have h := abs_trigamma_sub_cubic_le hx
    have hle : 1 / (20 * (a + (m : ℝ)) ^ 4) ≤ 1 / (20 * (m : ℝ) ^ 4) := by
      apply alg_div_le (by positivity) (by positivity)
      nlinarith [pow_le_pow_of_le_nonneg hM0.le (by linarith : (m : ℝ) ≤ a + (m : ℝ)) 4]
    rw [αcoef]
    linarith [h, hle]
  -- the algebraic remainder bound
  have halg : |(1 / (a + (m : ℝ)) + 1 / (2 * (a + (m : ℝ)) ^ 2) + 1 / (6 * (a + (m : ℝ)) ^ 3))
        - (1 / (m : ℝ) + (1 / 2 - a) / (m : ℝ) ^ 2 + (a ^ 2 - a + 1 / 6) / (m : ℝ) ^ 3)|
      ≤ a * K / (6 * (m : ℝ) ^ 4) := by
    have hden : (0 : ℝ) < 6 * (m : ℝ) ^ 3 * (a + (m : ℝ)) ^ 3 := by positivity
    have hK0 : (0 : ℝ) ≤ K := by rw [hK]; positivity
    rw [hid, abs_div, abs_of_pos hden, abs_neg, abs_mul, abs_of_pos ha]
    refine alg_div_le hden (by positivity) ?_
    have hmul : a * |Q| ≤ a * ((m : ℝ) ^ 2 * K) := mul_le_mul_of_nonneg_left hQb ha.le
    have hpw : (m : ℝ) ^ 3 ≤ (a + (m : ℝ)) ^ 3 :=
      pow_le_pow_of_le_nonneg hM0.le (by linarith) 3
    have h1 : a * |Q| * (6 * (m : ℝ) ^ 4) ≤ a * ((m : ℝ) ^ 2 * K) * (6 * (m : ℝ) ^ 4) :=
      mul_le_mul_of_nonneg_right hmul (by positivity)
    have h2 : a * ((m : ℝ) ^ 2 * K) * (6 * (m : ℝ) ^ 4)
        = a * K * (6 * (m : ℝ) ^ 3 * (m : ℝ) ^ 3) := by ring
    have hc : (0 : ℝ) ≤ a * K * (6 * (m : ℝ) ^ 3) :=
      mul_nonneg (mul_nonneg ha.le hK0) (by positivity)
    have h3 : a * K * (6 * (m : ℝ) ^ 3 * (m : ℝ) ^ 3)
        ≤ a * K * (6 * (m : ℝ) ^ 3 * (a + (m : ℝ)) ^ 3) := by
      have := mul_le_mul_of_nonneg_left hpw hc
      nlinarith [this]
    linarith
  have hfin : (1 : ℝ) / (20 * (m : ℝ) ^ 4) + a * K / (6 * (m : ℝ) ^ 4)
      = (1 / 20 + a * K / 6) / (m : ℝ) ^ 4 := by
    have h4 : ((m : ℝ) ^ 4) ≠ 0 := (pow_pos hM0 4).ne'
    field_simp
  calc |αcoef a m - (1 / (m : ℝ) + (1 / 2 - a) / (m : ℝ) ^ 2
          + (a ^ 2 - a + 1 / 6) / (m : ℝ) ^ 3)|
      ≤ 1 / (20 * (m : ℝ) ^ 4) + a * K / (6 * (m : ℝ) ^ 4) := by
        calc |αcoef a m - (1 / (m : ℝ) + (1 / 2 - a) / (m : ℝ) ^ 2
                + (a ^ 2 - a + 1 / 6) / (m : ℝ) ^ 3)|
            ≤ |αcoef a m - (1 / (a + (m : ℝ)) + 1 / (2 * (a + (m : ℝ)) ^ 2)
                  + 1 / (6 * (a + (m : ℝ)) ^ 3))|
              + |(1 / (a + (m : ℝ)) + 1 / (2 * (a + (m : ℝ)) ^ 2)
                  + 1 / (6 * (a + (m : ℝ)) ^ 3))
                - (1 / (m : ℝ) + (1 / 2 - a) / (m : ℝ) ^ 2
                  + (a ^ 2 - a + 1 / 6) / (m : ℝ) ^ 3)| := abs_sub_le _ _ _
          _ ≤ 1 / (20 * (m : ℝ) ^ 4) + a * K / (6 * (m : ℝ) ^ 4) := by linarith [hcub, halg]
    _ = (1 / 20 + a * K / 6) / (m : ℝ) ^ 4 := hfin

/-! ### `eq:beta-asymptotic` and `eq:c-asymptotic`

`β_m` and `c_m` are rational in `m`, so their expansions are exact algebra: the
remainder is written down rather than estimated, and the bound is a single
denominator comparison. -/

private theorem alg_beta3 (a M X : ℝ) (hM : M ≠ 0) (hX : X ≠ 0) (hXd : X = a + M - 1) :
    (2 * a + M - 2) / (2 * X)
      = 1 / 2 + (a - 1) / (2 * M) - (a - 1) ^ 2 / (2 * M ^ 2)
        + (a - 1) ^ 3 / (2 * M ^ 2 * X) := by
  field_simp
  subst hXd
  ring

/-- **`eq:beta-asymptotic`, exactly.** -/
theorem betacoef_three_term (ha : 0 < a) (hm : 2 ≤ m) :
    βcoef a m = 1 / 2 + (a - 1) / (2 * (m : ℝ)) - (a - 1) ^ 2 / (2 * (m : ℝ) ^ 2)
      + (a - 1) ^ 3 / (2 * (m : ℝ) ^ 2 * (a + (m : ℝ) - 1)) := by
  have hM : (2 : ℝ) ≤ (m : ℝ) := two_le_cast hm
  have hM0 : (0 : ℝ) < (m : ℝ) := by linarith
  have hx : (0 : ℝ) < a + (m : ℝ) - 1 := by linarith
  rw [βcoef_of_one a (by omega)]
  exact alg_beta3 a (m : ℝ) (a + (m : ℝ) - 1) hM0.ne' hx.ne' rfl

theorem abs_betacoef_sub_three_term_le (ha : 0 < a) (hm : 2 ≤ m) :
    |βcoef a m - (1 / 2 + (a - 1) / (2 * (m : ℝ)) - (a - 1) ^ 2 / (2 * (m : ℝ) ^ 2))|
      ≤ |a - 1| ^ 3 / (m : ℝ) ^ 3 := by
  have hM : (2 : ℝ) ≤ (m : ℝ) := two_le_cast hm
  have hM0 : (0 : ℝ) < (m : ℝ) := by linarith
  have hx : (0 : ℝ) < a + (m : ℝ) - 1 := by linarith
  have hhalf : (m : ℝ) / 2 ≤ a + (m : ℝ) - 1 := by linarith
  rw [betacoef_three_term ha hm]
  rw [show 1 / 2 + (a - 1) / (2 * (m : ℝ)) - (a - 1) ^ 2 / (2 * (m : ℝ) ^ 2)
        + (a - 1) ^ 3 / (2 * (m : ℝ) ^ 2 * (a + (m : ℝ) - 1))
        - (1 / 2 + (a - 1) / (2 * (m : ℝ)) - (a - 1) ^ 2 / (2 * (m : ℝ) ^ 2))
      = (a - 1) ^ 3 / (2 * (m : ℝ) ^ 2 * (a + (m : ℝ) - 1)) from by ring]
  rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < 2 * (m : ℝ) ^ 2 * (a + (m : ℝ) - 1))]
  rw [show |(a - 1) ^ 3| = |a - 1| ^ 3 from by rw [abs_pow]]
  refine alg_div_le (by positivity) (pow_pos hM0 3) ?_
  have h1 : (0 : ℝ) ≤ |a - 1| ^ 3 := by positivity
  have hbase : (m : ℝ) ^ 3 ≤ 2 * (m : ℝ) ^ 2 * (a + (m : ℝ) - 1) := by
    nlinarith [pow_pos hM0 2, hhalf]
  exact mul_le_mul_of_nonneg_left hbase h1

private theorem alg_c3 (a M U : ℝ) (hM : M ≠ 0) (hU : U ≠ 0) (hUd : U = 2 * a + 2 * M - 3) :
    M * (M - 1) / (2 * U)
      = M / 4 - (a - 1 / 2) / 4 + (a - 3 / 2) * (a - 1 / 2) / (4 * M)
        + (1 - 2 * a) * (2 * a - 3) ^ 2 / (16 * M * U) := by
  field_simp
  subst hUd
  ring

/-- **`eq:c-asymptotic`, exactly.** -/
theorem ccoef_three_term (ha : 0 < a) (hm : 2 ≤ m) :
    ccoef a m = (m : ℝ) / 4 - (a - 1 / 2) / 4 + (a - 3 / 2) * (a - 1 / 2) / (4 * (m : ℝ))
      + (1 - 2 * a) * (2 * a - 3) ^ 2 / (16 * (m : ℝ) * (2 * a + 2 * (m : ℝ) - 3)) := by
  have hM : (2 : ℝ) ≤ (m : ℝ) := two_le_cast hm
  have hM0 : (0 : ℝ) < (m : ℝ) := by linarith
  have hu : (0 : ℝ) < 2 * a + 2 * (m : ℝ) - 3 := by linarith
  rw [ccoef_of_two a hm]
  exact alg_c3 a (m : ℝ) (2 * a + 2 * (m : ℝ) - 3) hM0.ne' hu.ne' rfl

theorem abs_ccoef_sub_three_term_le (ha : 0 < a) (hm : 2 ≤ m) :
    |ccoef a m - ((m : ℝ) / 4 - (a - 1 / 2) / 4 + (a - 3 / 2) * (a - 1 / 2) / (4 * (m : ℝ)))|
      ≤ |1 - 2 * a| * (2 * a - 3) ^ 2 / (8 * (m : ℝ) ^ 2) := by
  have hM : (2 : ℝ) ≤ (m : ℝ) := two_le_cast hm
  have hM0 : (0 : ℝ) < (m : ℝ) := by linarith
  have hu : (0 : ℝ) < 2 * a + 2 * (m : ℝ) - 3 := by linarith
  have hhalf : (m : ℝ) / 2 ≤ 2 * a + 2 * (m : ℝ) - 3 := by linarith
  rw [ccoef_three_term ha hm]
  rw [show (m : ℝ) / 4 - (a - 1 / 2) / 4 + (a - 3 / 2) * (a - 1 / 2) / (4 * (m : ℝ))
        + (1 - 2 * a) * (2 * a - 3) ^ 2 / (16 * (m : ℝ) * (2 * a + 2 * (m : ℝ) - 3))
        - ((m : ℝ) / 4 - (a - 1 / 2) / 4 + (a - 3 / 2) * (a - 1 / 2) / (4 * (m : ℝ)))
      = (1 - 2 * a) * (2 * a - 3) ^ 2 / (16 * (m : ℝ) * (2 * a + 2 * (m : ℝ) - 3)) from by ring]
  rw [abs_div,
    abs_of_pos (by positivity : (0:ℝ) < 16 * (m : ℝ) * (2 * a + 2 * (m : ℝ) - 3)),
    abs_mul, show |(2 * a - 3) ^ 2| = (2 * a - 3) ^ 2 from abs_of_nonneg (sq_nonneg _)]
  refine alg_div_le (by positivity) (by positivity) ?_
  have h1 : (0 : ℝ) ≤ |1 - 2 * a| * (2 * a - 3) ^ 2 :=
    mul_nonneg (abs_nonneg _) (sq_nonneg _)
  have hbase : 8 * (m : ℝ) ^ 2 ≤ 16 * (m : ℝ) * (2 * a + 2 * (m : ℝ) - 3) := by
    nlinarith [hhalf, hM0]
  exact mul_le_mul_of_nonneg_left hbase h1

end TuranBessel
