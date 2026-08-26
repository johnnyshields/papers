/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Shields.MeasureTheory.Integral.CircleAndreief

/-!
# Modulus bounds for the `k`-fold circle integral

The mixed estimates for `Shields.circleIntegralPow`.  The plain length-times-supremum bound is
`Shields.norm_circleIntegralPow_le`; what this file adds is the **mixed** case: when `\ell` of the
`k` variables are left on a large circle `|t|=R` and the rest sit at radius `s<R`, each variable on
the large circle contributes a factor `(s/R)^{-m}` relative to the small-radius scale, so at a
negative exponent `m` the whole term is `O\bigl((s/R)^{|m|\ell}\bigr)` — geometrically small in
`|m|`, uniformly in which variables were left outside.

## Main results

* `Shields.angleMeasure_univ` — the total mass of the angular measure
* `Shields.norm_circleIntegralPow_le_of_nonneg` — the plain bound with `|ρ|` resolved
* `Shields.norm_prod_zpow_of_mem_polyCircle` — the modulus of a product of integer powers
* `Shields.norm_circleIntegralPow_outer_le`, `Shields.norm_circleIntegralPow_outer_div_le` —
  the mixed bound, absolute and against the small-radius scale
* `Shields.tendsto_circleIntegralPow_outer` — **the mixed term is geometrically small**

## Implementation notes

The exponent is an integer, so that the negative powers a Laurent expansion produces are covered
without a separate statement; that is also why the comparison is stated against the small-radius
scale rather than absolutely, since only the ratio is bounded uniformly.

## Tags

circle integral, ML bound, andreief, geometric decay
-/

open scoped Real
open MeasureTheory Complex Set

namespace Shields

variable {k : ℕ} {ρ : ℝ}

theorem angleMeasure_univ (k : ℕ) :
    angleMeasure k Set.univ = ENNReal.ofReal (2 * π) ^ k := by
  unfold angleMeasure
  rw [show (Set.univ : Set (Fin k → ℝ)) = Set.univ.pi fun _ => (Set.univ : Set ℝ) by simp,
    MeasureTheory.Measure.pi_pi]
  simp [Real.volume_Ioc]

instance instIsFiniteMeasureAngleMeasure (k : ℕ) : IsFiniteMeasure (angleMeasure k) := by
  constructor
  rw [angleMeasure_univ]
  exact ENNReal.pow_lt_top ENNReal.ofReal_lt_top

/-- The length-times-supremum bound with the radius folded into the constant, for `ρ ≥ 0`.  This
is `Shields.norm_circleIntegralPow_le` with `|ρ|` resolved and the powers collected. -/
theorem norm_circleIntegralPow_le_of_nonneg (hρ : 0 ≤ ρ) {F : (Fin k → ℂ) → ℂ} {C : ℝ}
    (hF : ∀ t ∈ polyCircle k ρ, ‖F t‖ ≤ C) :
    ‖circleIntegralPow k ρ F‖ ≤ (2 * π * ρ) ^ k * C := by
  have h := norm_circleIntegralPow_le hF
  rwa [abs_of_nonneg hρ, ← mul_pow] at h

/-- On the polycircle of radius `R` every variable has modulus `R`, so a common
integer power `∏_a t_a^m` has modulus `(R^m)^ℓ`. -/
theorem norm_prod_zpow_of_mem_polyCircle {ℓ : ℕ} {R : ℝ} (hR : 0 < R) (m : ℤ)
    {t : Fin ℓ → ℂ} (ht : t ∈ polyCircle ℓ R) :
    ‖∏ a, t a ^ m‖ = (R ^ m) ^ ℓ := by
  rw [norm_prod]
  have : ∀ a : Fin ℓ, ‖t a ^ m‖ = R ^ m := by
    intro a
    rw [norm_zpow, mem_polyCircle.mp ht a, abs_of_pos hR]
  rw [Finset.prod_congr rfl fun a _ => this a, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]

/-- **The outer contribution against the small-radius scale.**  With `s < R`
the moduli of a selected pole and of the outer contour, a term of
the integral that leaves `ℓ` variables on `|t_a| = R` is bounded by the
residue scale `(s^{-n-k})^ℓ` times `q^{ℓ(n+k)}`, `q = s/R < 1`. -/
theorem norm_circleIntegralPow_outer_le {ℓ : ℕ} {R s M : ℝ} (hs : 0 < s) (hsR : s < R)
    (n k : ℕ) {F : (Fin ℓ → ℂ) → ℂ} (hF : ∀ t ∈ polyCircle ℓ R, ‖F t‖ ≤ M) :
    ‖circleIntegralPow ℓ R (fun t => F t * ∏ a, t a ^ (-(n : ℤ) - (k : ℤ)))‖
      ≤ (2 * π * R) ^ ℓ * M
        * ((s ^ (-(n : ℤ) - (k : ℤ))) ^ ℓ * (s / R) ^ (ℓ * (n + k))) := by
  have hR : 0 < R := hs.trans hsR
  have hMnn : 0 ≤ M := by
    have hmem := circleMap_mem_polyCircle ℓ R (fun _ => 0)
    exact le_trans (norm_nonneg _) (hF _ hmem)
  have hpt : ∀ t ∈ polyCircle ℓ R,
      ‖F t * ∏ a, t a ^ (-(n : ℤ) - (k : ℤ))‖ ≤ M * (R ^ (-(n : ℤ) - (k : ℤ))) ^ ℓ := by
    intro t ht
    rw [norm_mul, norm_prod_zpow_of_mem_polyCircle hR (-(n : ℤ) - (k : ℤ)) ht]
    exact mul_le_mul_of_nonneg_right (hF t ht)
      (pow_nonneg (zpow_nonneg hR.le _) ℓ)
  have hML : ‖circleIntegralPow ℓ R (fun t => F t * ∏ a, t a ^ (-(n : ℤ) - (k : ℤ)))‖
      ≤ (2 * π * R) ^ ℓ * (M * (R ^ (-(n : ℤ) - (k : ℤ))) ^ ℓ) := by
    have h := norm_circleIntegralPow_le hpt
    rwa [abs_of_nonneg hR.le, ← mul_pow] at h
  refine hML.trans_eq ?_
  rw [← mul_assoc]
  refine congrArg (fun x => (2 * π * R) ^ ℓ * M * x) ?_
  -- `s^{-(n+k)} · (s/R)^{n+k} = R^{-(n+k)}`, so the two right-hand sides agree.
  have hscale : (s ^ (-(n : ℤ) - (k : ℤ))) ^ ℓ * (s / R) ^ (ℓ * (n + k))
      = (R ^ (-(n : ℤ) - (k : ℤ))) ^ ℓ := by
    have hzs : s ^ (-(n : ℤ) - (k : ℤ)) = (s ^ (n + k))⁻¹ := by
      rw [show (-(n : ℤ) - (k : ℤ)) = -((n + k : ℕ) : ℤ) by push_cast; ring, zpow_neg,
        zpow_natCast]
    have hzR : R ^ (-(n : ℤ) - (k : ℤ)) = (R ^ (n + k))⁻¹ := by
      rw [show (-(n : ℤ) - (k : ℤ)) = -((n + k : ℕ) : ℤ) by push_cast; ring, zpow_neg,
        zpow_natCast]
    have hbase : s ^ (-(n : ℤ) - (k : ℤ)) * (s / R) ^ (n + k) = R ^ (-(n : ℤ) - (k : ℤ)) := by
      rw [hzs, hzR, div_pow]
      field_simp
    calc (s ^ (-(n : ℤ) - (k : ℤ))) ^ ℓ * (s / R) ^ (ℓ * (n + k))
        = (s ^ (-(n : ℤ) - (k : ℤ))) ^ ℓ * ((s / R) ^ (n + k)) ^ ℓ := by
          rw [mul_comm ℓ (n + k), pow_mul]
      _ = (s ^ (-(n : ℤ) - (k : ℤ)) * (s / R) ^ (n + k)) ^ ℓ := (mul_pow _ _ ℓ).symm
      _ = (R ^ (-(n : ℤ) - (k : ℤ))) ^ ℓ := by rw [hbase]
  exact hscale.symm

/-- **The mixed term is geometrically small.**  As soon as one variable stays on the
outer contour, the outer contribution normalized by the residue scale is
`O(q^n)` with `q = s/R < 1`, uniformly over integrands bounded on the polycircle.
This is where a geometric error term comes
from — a gap between two moduli, with no saddle-point analysis anywhere. -/
theorem norm_circleIntegralPow_outer_div_le {ℓ : ℕ} (hℓ : 0 < ℓ) {R s M : ℝ}
    (hs : 0 < s) (hsR : s < R) (n k : ℕ) {F : (Fin ℓ → ℂ) → ℂ}
    (hF : ∀ t ∈ polyCircle ℓ R, ‖F t‖ ≤ M) :
    ‖circleIntegralPow ℓ R (fun t => F t * ∏ a, t a ^ (-(n : ℤ) - (k : ℤ)))‖
        / (s ^ (-(n : ℤ) - (k : ℤ))) ^ ℓ
      ≤ (2 * π * R) ^ ℓ * M * (s / R) ^ n := by
  have hR : 0 < R := hs.trans hsR
  have hq0 : 0 < s / R := div_pos hs hR
  have hq1 : s / R < 1 := (div_lt_one hR).mpr hsR
  have hMnn : 0 ≤ M := by
    have hmem := circleMap_mem_polyCircle ℓ R (fun _ => 0)
    exact le_trans (norm_nonneg _) (hF _ hmem)
  have hden : (0 : ℝ) < (s ^ (-(n : ℤ) - (k : ℤ))) ^ ℓ :=
    pow_pos (zpow_pos hs _) ℓ
  rw [div_le_iff₀ hden]
  refine (norm_circleIntegralPow_outer_le hs hsR n k hF).trans ?_
  have hexp : n ≤ ℓ * (n + k) :=
    calc n ≤ n + k := Nat.le_add_right _ _
      _ = 1 * (n + k) := (one_mul _).symm
      _ ≤ ℓ * (n + k) := Nat.mul_le_mul hℓ le_rfl
  have hmono : (s / R) ^ (ℓ * (n + k)) ≤ (s / R) ^ n :=
    pow_le_pow_of_le_one hq0.le hq1.le hexp
  have hconst : (0 : ℝ) ≤ (2 * π * R) ^ ℓ * M :=
    mul_nonneg (pow_nonneg (by positivity) ℓ) hMnn
  calc (2 * π * R) ^ ℓ * M * ((s ^ (-(n : ℤ) - (k : ℤ))) ^ ℓ * (s / R) ^ (ℓ * (n + k)))
      = ((2 * π * R) ^ ℓ * M * (s / R) ^ (ℓ * (n + k))) * (s ^ (-(n : ℤ) - (k : ℤ))) ^ ℓ := by
        ring
    _ ≤ ((2 * π * R) ^ ℓ * M * (s / R) ^ n) * (s ^ (-(n : ℤ) - (k : ℤ))) ^ ℓ := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hmono hconst) hden.le

/-- The normalized outer contribution tends to zero as the order grows. -/
theorem tendsto_circleIntegralPow_outer {ℓ : ℕ} (hℓ : 0 < ℓ) {R s M : ℝ}
    (hs : 0 < s) (hsR : s < R) (k : ℕ) {F : ℕ → (Fin ℓ → ℂ) → ℂ}
    (hF : ∀ n, ∀ t ∈ polyCircle ℓ R, ‖F n t‖ ≤ M) :
    Filter.Tendsto
      (fun n : ℕ => ‖circleIntegralPow ℓ R
          (fun t => F n t * ∏ a, t a ^ (-(n : ℤ) - (k : ℤ)))‖
        / (s ^ (-(n : ℤ) - (k : ℤ))) ^ ℓ)
      Filter.atTop (nhds 0) := by
  have hR : 0 < R := hs.trans hsR
  have hq0 : 0 < s / R := div_pos hs hR
  have hq1 : s / R < 1 := (div_lt_one hR).mpr hsR
  have hMnn : 0 ≤ M := by
    have hmem := circleMap_mem_polyCircle ℓ R (fun _ => 0)
    exact le_trans (norm_nonneg _) (hF 0 _ hmem)
  have hmaj : Filter.Tendsto
      (fun n : ℕ => (2 * π * R) ^ ℓ * M * (s / R) ^ n) Filter.atTop (nhds 0) := by
    have := tendsto_pow_atTop_nhds_zero_of_lt_one hq0.le hq1
    simpa using this.const_mul ((2 * π * R) ^ ℓ * M)
  refine squeeze_zero (fun n => ?_) (fun n => ?_) hmaj
  · positivity
  · exact norm_circleIntegralPow_outer_div_le hℓ hs hsR n k (hF n)

end Shields
