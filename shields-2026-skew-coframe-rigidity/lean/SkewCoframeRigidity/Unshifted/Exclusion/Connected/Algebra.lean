/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCoframeRigidity.Unshifted.Exclusion.Ports

/-!
# The child equation of the connected corner

Formalizes `shields-2026-skew-coframe-rigidity.tex`, «Unshifted opposite-end exclusion»
(`ph:unshifted-exclusion`), the connected corner: with `a = -z g / k`, `b = -z c / k` the quadratic
equation is `z²/k²` times `ℰ^L_{g,c} + z^L (g α_c - c α_g)`, and the dependence of that
expression on the top letter `H_L` is the single term `-p(p-1) ϑ^{p-2} H_L z^L 𝒯^L_{g,c}(h)`.
Pure series algebra.  Sorry-free.
-/

namespace SkewCoframeRigidity.Unshifted

open SkewCofactorIndependence SkewCoframeRigidity.Coframe SkewCoframeRigidity Polynomial
open scoped Polynomial Matrix

variable {K : Type*} [Field K]

theorem trunc_X_mul_succ (n : ℕ) (f : PowerSeries K) :
    PowerSeries.trunc (n + 1) (PowerSeries.X * f) = Polynomial.X * PowerSeries.trunc n f := by
  ext i
  rcases i with _ | i
  · simp [PowerSeries.coeff_trunc]
  · simp only [PowerSeries.coeff_trunc, Polynomial.coeff_X_mul, PowerSeries.coeff_succ_X_mul]
    simp [Nat.succ_lt_succ_iff]

/-- Moving the window of the clipped operator by one adds the cap polynomial. -/
theorem clippedOp_succ_window (L : ℕ) (g c : K[X]) (u : PowerSeries K) :
    clippedOp (L + 1) g c u = clippedOp L g c u +
      Polynomial.X ^ L * (g * Polynomial.C (PowerSeries.coeff L (u * (c : PowerSeries K))) -
        c * Polynomial.C (PowerSeries.coeff L (u * (g : PowerSeries K)))) := by
  unfold clippedOp
  rw [PowerSeries.trunc_succ, PowerSeries.trunc_succ, ← Polynomial.C_mul_X_pow_eq_monomial,
    ← Polynomial.C_mul_X_pow_eq_monomial]
  ring

theorem clippedOp_shift (L : ℕ) (s : K) (g c : K[X]) (u : PowerSeries K) :
    clippedOp (L + 2) (Polynomial.C s * Polynomial.X * g) (Polynomial.C s * Polynomial.X * c) u =
      Polynomial.C (s ^ 2) * Polynomial.X ^ 2 * clippedOp (L + 1) g c u := by
  have key : ∀ F : K[X], PowerSeries.trunc (L + 2)
      (u * ((Polynomial.C s * Polynomial.X * F : K[X]) : PowerSeries K)) =
      Polynomial.C s * Polynomial.X * PowerSeries.trunc (L + 1) (u * (F : PowerSeries K)) := by
    intro F
    have : u * ((Polynomial.C s * Polynomial.X * F : K[X]) : PowerSeries K) =
        PowerSeries.C s * (PowerSeries.X * (u * (F : PowerSeries K))) := by
      simp only [Polynomial.coe_mul, Polynomial.coe_C, Polynomial.coe_X]; ring
    rw [this, PowerSeries.trunc_C_mul, trunc_X_mul_succ, mul_assoc]
  unfold clippedOp
  rw [key, key]
  simp only [Polynomial.C_pow]
  ring

/-- The cap coordinate `α_g = [h^p g]_L - p ϑ^{p-1} [h g]_L`. -/
noncomputable def capAlpha (p L : ℕ) (h : ℕ → K) (g : K[X]) : K :=
  PowerSeries.coeff L (seriesOf h ^ p * (g : PowerSeries K)) -
    (p : K) * h 0 ^ (p - 1) * PowerSeries.coeff L (seriesOf h * (g : PowerSeries K))

/-- The child expression `ℰ^L_{g,c} + z^L (g α_c - c α_g)`. -/
noncomputable def childExpr (p L : ℕ) (h : ℕ → K) (g c : K[X]) : PowerSeries K :=
  Eop p L g c (seriesOf h) + PowerSeries.X ^ L * ((g : PowerSeries K) *
    PowerSeries.C (capAlpha p L h c) - (c : PowerSeries K) * PowerSeries.C (capAlpha p L h g))

/-- With `a = -z g / k` and `b = -z c / k` the quadratic coefficient is `z²/k²` times the child
expression. -/
theorem passage (p L : ℕ) (h : ℕ → K) (g c : K[X]) (k s : K) (hs : s * k = -1)
    (hg : PowerSeries.coeff L (seriesOf h * (g : PowerSeries K)) = k)
    (hc : PowerSeries.coeff L (seriesOf h * (c : PowerSeries K)) = k) :
    Eop p (L + 2) (Polynomial.C s * Polynomial.X * g) (Polynomial.C s * Polynomial.X * c)
        (seriesOf h) +
      (PowerSeries.C (p : K) * (PowerSeries.C (h 0) ^ (p - 1) - seriesOf h ^ (p - 1)) *
          PowerSeries.X ^ (L + 1)) *
        ((Polynomial.C s * Polynomial.X * g - Polynomial.C s * Polynomial.X * c : K[X]) :
          PowerSeries K) =
      PowerSeries.C (s ^ 2) * PowerSeries.X ^ 2 * childExpr p L h g c := by
  have hsC : PowerSeries.C s * PowerSeries.C k = -1 := by
    rw [← map_mul, hs, map_neg, map_one]
  have hpC : PowerSeries.C (p : K) = (p : PowerSeries K) := map_natCast _ p
  unfold childExpr capAlpha
  simp only [Eop]
  rw [clippedOp_shift, clippedOp_shift, clippedOp_succ_window, clippedOp_succ_window, hg, hc]
  simp only [Polynomial.coe_add, Polynomial.coe_mul, Polynomial.coe_sub, Polynomial.coe_C,
    Polynomial.coe_pow, Polynomial.coe_X, map_pow, map_mul, map_sub, hpC]
  
  linear_combination ((p : PowerSeries K) * (PowerSeries.C (h 0) ^ (p - 1) -
    seriesOf h ^ (p - 1)) * PowerSeries.X ^ (L + 1) * PowerSeries.X *
      PowerSeries.C s * ((g : PowerSeries K) - (c : PowerSeries K))) * hsC

theorem pow_sub_pow_factor (x y : PowerSeries K) (n : ℕ)
    (hxy : PowerSeries.constantCoeff x = PowerSeries.constantCoeff y) :
    ∃ w : PowerSeries K, x ^ n - y ^ n = (x - y) * w ∧
      PowerSeries.constantCoeff w = n * PowerSeries.constantCoeff y ^ (n - 1) := by
  rcases n with _ | n
  · exact ⟨0, by simp, by simp⟩
  refine ⟨∑ i ∈ Finset.range (n + 1), x ^ i * y ^ (n + 1 - 1 - i), ?_, ?_⟩
  · rw [mul_comm]; exact (geom_sum₂_mul x y (n + 1)).symm
  · simp only [map_sum, map_mul, map_pow, hxy, Finset.sum_const, Finset.card_range]
    rw [Finset.sum_congr rfl (g := fun _ => PowerSeries.constantCoeff y ^ n)]
    · simp
    · intro i hi
      have := Finset.mem_range.1 hi
      rw [← pow_add]; congr 1; omega

theorem clippedOp_X_pow_self_mul (L : ℕ) (g c : K[X]) (w : PowerSeries K) :
    clippedOp L g c (PowerSeries.X ^ L * w) = 0 := by
  unfold clippedOp
  have h : ∀ F : PowerSeries K, PowerSeries.trunc L (PowerSeries.X ^ L * w * F) = 0 := by
    intro F
    rw [mul_assoc, PowerSeries.trunc_X_pow_self_mul]
  simp only [h, mul_zero, sub_zero]

/-- The dependence of the child expression on the top letter `H_L`: it is the single term
`-p (p-1) ϑ^{p-2} H_L z^L 𝒯^L_{g,c}(h)`, read at the coefficient `z^{2L+1}`. -/
theorem childExpr_top_letter (q L : ℕ) (hL : 1 ≤ L) (h₁ : ℕ → K) (u : K) (g c : K[X])
    (hg : g.coeff 0 = 1) (hc : c.coeff 0 = 1)
    (hD : ∀ j ≤ L, PowerSeries.coeff j ((clippedOp L g c (seriesOf h₁) : K[X]) : PowerSeries K) = 0)
    (hz : h₁ L = 0) :
    PowerSeries.coeff (2 * L + 1) (childExpr (q + 2) L (Function.update h₁ L u) g c) =
      PowerSeries.coeff (2 * L + 1) (childExpr (q + 2) L h₁ g c) -
        ((q + 2 : ℕ) : K) * ((q + 1 : ℕ) : K) * h₁ 0 ^ q * u *
          PowerSeries.coeff (L + 1) ((clippedOp L g c (seriesOf h₁) : K[X]) : PowerSeries K) := by
  set h := Function.update h₁ L u with hh
  have h0 : h 0 = h₁ 0 := Function.update_of_ne (by omega) _ _
  have hs : seriesOf h = seriesOf h₁ + PowerSeries.C u * PowerSeries.X ^ L := by
    ext k
    simp only [seriesOf, hh, map_add, PowerSeries.coeff_mk, PowerSeries.coeff_C_mul,
      PowerSeries.coeff_X_pow]
    by_cases hk : k = L
    · subst hk; simp [hz]
    · simp [Function.update_of_ne hk, hk]
  have hsub : seriesOf h - seriesOf h₁ = PowerSeries.C u * PowerSeries.X ^ L := by
    rw [hs]; ring
  have hconst : PowerSeries.constantCoeff (seriesOf h) = PowerSeries.constantCoeff (seriesOf h₁) := by
    rw [hs, map_add, map_mul, map_pow, PowerSeries.constantCoeff_X, zero_pow (by omega)]
    simp
  have hcst : PowerSeries.constantCoeff (seriesOf h₁) = h₁ 0 := rfl
  obtain ⟨w2, hw2, hw2c⟩ := pow_sub_pow_factor (seriesOf h) (seriesOf h₁) (q + 2) hconst
  obtain ⟨w1, hw1, hw1c⟩ := pow_sub_pow_factor (seriesOf h) (seriesOf h₁) (q + 1) hconst
  rw [hsub] at hw2 hw1
  have e1 : clippedOp L g c (seriesOf h ^ (q + 2)) = clippedOp L g c (seriesOf h₁ ^ (q + 2)) := by
    have : seriesOf h ^ (q + 2) = seriesOf h₁ ^ (q + 2) +
        PowerSeries.X ^ L * (PowerSeries.C u * w2) := by
      rw [sub_eq_iff_eq_add] at hw2; rw [hw2]; ring
    rw [this, clippedOp_add_right, clippedOp_X_pow_self_mul, add_zero]
  have e2 : clippedOp L g c (seriesOf h) = clippedOp L g c (seriesOf h₁) := by
    have : seriesOf h = seriesOf h₁ + PowerSeries.X ^ L * PowerSeries.C u := by rw [hs]; ring
    rw [this, clippedOp_add_right, clippedOp_X_pow_self_mul, add_zero]
  have hcap : ∀ f : K[X], f.coeff 0 = 1 →
      capAlpha (q + 2) L h f = capAlpha (q + 2) L h₁ f := by
    intro f hf
    have hf0 : PowerSeries.constantCoeff (f : PowerSeries K) = 1 := by
      rw [Polynomial.constantCoeff_coe]; exact hf
    have a1 : seriesOf h ^ (q + 2) * (f : PowerSeries K) = seriesOf h₁ ^ (q + 2) * (f : PowerSeries K) +
        PowerSeries.X ^ L * (PowerSeries.C u * w2 * (f : PowerSeries K)) := by
      rw [sub_eq_iff_eq_add] at hw2; rw [hw2]; ring
    have a2 : seriesOf h * (f : PowerSeries K) = seriesOf h₁ * (f : PowerSeries K) +
        PowerSeries.X ^ L * (PowerSeries.C u * (f : PowerSeries K)) := by rw [hs]; ring
    unfold capAlpha
    rw [a1, a2, map_add, map_add, PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_X_pow_mul',
      if_pos le_rfl, if_pos le_rfl, Nat.sub_self, h0]
    simp only [PowerSeries.coeff_zero_eq_constantCoeff_apply, map_mul, PowerSeries.constantCoeff_C,
      hw2c, hf0, hcst, Nat.cast_add, Nat.cast_ofNat, mul_one]
    simp only [show q + 2 - 1 = q + 1 from rfl]
    ring
  have key : childExpr (q + 2) L h g c = childExpr (q + 2) L h₁ g c -
      PowerSeries.C ((q + 2 : ℕ) : K) * (PowerSeries.C u * PowerSeries.X ^ L * w1) *
        ((clippedOp L g c (seriesOf h₁) : K[X]) : PowerSeries K) := by
    unfold childExpr
    rw [hcap c hc, hcap g hg]
    simp only [Eop]
    rw [e1, e2, show q + 2 - 1 = q + 1 from rfl]
    have : seriesOf h ^ (q + 1) = seriesOf h₁ ^ (q + 1) +
        PowerSeries.C u * PowerSeries.X ^ L * w1 := by
      rw [sub_eq_iff_eq_add] at hw1; rw [hw1]; ring
    rw [this]
    ring
  have hdvd : PowerSeries.X ^ (L + 1) ∣
      ((clippedOp L g c (seriesOf h₁) : K[X]) : PowerSeries K) := by
    rw [PowerSeries.X_pow_dvd_iff]
    intro j hj
    exact hD j (by omega)
  obtain ⟨D2, hD2⟩ := hdvd
  rw [key, map_sub, hD2]
  have e3 : PowerSeries.C ((q + 2 : ℕ) : K) * (PowerSeries.C u * PowerSeries.X ^ L * w1) *
      (PowerSeries.X ^ (L + 1) * D2) =
      PowerSeries.X ^ (2 * L + 1) * (PowerSeries.C (((q + 2 : ℕ) : K) * u) * w1 * D2) := by
    rw [map_mul, show 2 * L + 1 = L + (L + 1) by omega, pow_add]; ring
  rw [e3, PowerSeries.coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self,
    PowerSeries.coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self]
  simp only [PowerSeries.coeff_zero_eq_constantCoeff_apply, map_mul, PowerSeries.constantCoeff_C,
    hw1c, hcst]
  simp only [Nat.add_sub_cancel]
  ring


end SkewCoframeRigidity.Unshifted
