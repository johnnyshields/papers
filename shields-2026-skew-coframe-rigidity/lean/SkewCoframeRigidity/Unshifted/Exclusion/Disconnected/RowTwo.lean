/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCoframeRigidity.Unshifted.Exclusion.Disconnected.Quadratic

/-!
# The quadratic equation against the two-cell row

Formalizes `shields-2026-skew-coframe-rigidity.tex`, «Unshifted opposite-end exclusion»
(`ph:unshifted-exclusion`, disconnected corner, `A < B`).  For `p = 2` and `b = β z^{M-3}` with
`β h₂ = -1`, the defect expression factors as `b · Br`, where
`Br = R² a + [H² a]_{≥M} - 2 H [H a]_{≥M} + 2 h₂ (ϑ - H) z² b` and `R = H - ϑ - h₁ z`.
-/

namespace SkewCoframeRigidity.Unshifted

open PowerSeries SkewCoframeRigidity SkewCoframeRigidity.Coframe
open Polynomial hiding coeff

variable {K : Type*} [Field K]

/-- The part of a series in degrees at least `N`. -/
noncomputable def tailS (N : ℕ) (v : K⟦X⟧) : K⟦X⟧ := v - ((trunc N v : K[X]) : K⟦X⟧)

theorem coeff_tailS (N n : ℕ) (v : K⟦X⟧) :
    coeff n (tailS N v) = if N ≤ n then coeff n v else 0 := by
  unfold tailS
  rw [map_sub, Polynomial.coeff_coe, coeff_trunc]
  by_cases h : n < N
  · rw [ite_eq_left h, ite_eq_right (by omega)]; simp
  · rw [ite_eq_right h, ite_eq_left (by omega)]; simp

theorem tailS_shift (s : ℕ) (v : K⟦X⟧) (β : K) :
    tailS (s + 3) (PowerSeries.C β * (PowerSeries.X ^ s * v)) =
      PowerSeries.C β * (PowerSeries.X ^ s * tailS 3 v) := by
  ext n
  rw [coeff_tailS, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_C_mul,
    PowerSeries.coeff_X_pow_mul', coeff_tailS]
  by_cases hs : s ≤ n
  · rw [ite_eq_left hs, ite_eq_left hs]
    by_cases h3 : 3 ≤ n - s
    · rw [ite_eq_left h3, ite_eq_left (by omega)]
    · rw [ite_eq_right h3, ite_eq_right (by omega), mul_zero]
  · rw [ite_eq_right hs, ite_eq_right hs, ite_eq_right (by omega)]
    simp

theorem tailS_three (v : K⟦X⟧) :
    tailS 3 v = v - (PowerSeries.C (coeff 0 v) + PowerSeries.C (coeff 1 v) * PowerSeries.X +
      PowerSeries.C (coeff 2 v) * PowerSeries.X ^ 2) := by
  ext n
  rw [coeff_tailS]
  simp only [map_sub, map_add, PowerSeries.coeff_C, PowerSeries.coeff_C_mul_X_pow, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_X, PowerSeries.coeff_X_pow]
  rcases n with _ | _ | _ | n
  · simp
  · simp
  · simp
  · simp

theorem coe_clippedOp_tails (M : ℕ) (a b : K[X]) (u : K⟦X⟧) :
    ((clippedOp M a b u : K[X]) : K⟦X⟧) =
      (b : K⟦X⟧) * tailS M (u * (a : K⟦X⟧)) - (a : K⟦X⟧) * tailS M (u * (b : K⟦X⟧)) := by
  unfold clippedOp tailS
  rw [Polynomial.coe_sub, Polynomial.coe_mul, Polynomial.coe_mul]
  ring

theorem coeff_seriesOf (h : ℕ → K) (n : ℕ) : coeff n (seriesOf h) = h n := by simp [seriesOf]

theorem constantCoeff_seriesOf' (h : ℕ → K) : constantCoeff (seriesOf h) = h 0 := by
  simp [seriesOf]

theorem coeff_sq_seriesOf_zero (h : ℕ → K) : coeff 0 (seriesOf h ^ 2) = h 0 ^ 2 := by
  rw [sq, PowerSeries.coeff_mul]; simp [constantCoeff_seriesOf']; ring

theorem coeff_sq_seriesOf_one (h : ℕ → K) : coeff 1 (seriesOf h ^ 2) = 2 * h 0 * h 1 := by
  rw [sq, coeff_one_mul]; simp [coeff_seriesOf, constantCoeff_seriesOf']; ring

theorem coeff_sq_seriesOf_two (h : ℕ → K) :
    coeff 2 (seriesOf h ^ 2) = 2 * h 0 * h 2 + h 1 ^ 2 := by
  rw [sq, PowerSeries.coeff_mul]
  simp [Finset.Nat.antidiagonal_succ, coeff_seriesOf]; ring

/-- The factorization of the defect expression against `b = β z^{M-3}`. -/
theorem defectExpr_two_row (s : ℕ) (h : ℕ → K) (a : K[X]) (β : K) (hβ : β * h 2 = -1) :
    defectExpr (s + 3) 2 h a (Polynomial.C β * Polynomial.X ^ s) =
      ((Polynomial.C β * Polynomial.X ^ s : K[X]) : K⟦X⟧) *
        ((seriesOf h - PowerSeries.C (h 0) - PowerSeries.C (h 1) * PowerSeries.X) ^ 2 * (a : K⟦X⟧) +
          tailS (s + 3) (seriesOf h ^ 2 * (a : K⟦X⟧)) -
          2 * seriesOf h * tailS (s + 3) (seriesOf h * (a : K⟦X⟧)) +
          PowerSeries.C (2 * h 2) * (PowerSeries.C (h 0) - seriesOf h) * PowerSeries.X ^ 2 *
            ((Polynomial.C β * Polynomial.X ^ s : K[X]) : K⟦X⟧)) := by
  have hb : ∀ u : K⟦X⟧, u * ((Polynomial.C β * Polynomial.X ^ s : K[X]) : K⟦X⟧) =
      PowerSeries.C β * (PowerSeries.X ^ s * u) := by
    intro u
    rw [Polynomial.coe_mul, Polynomial.coe_C, Polynomial.coe_pow, Polynomial.coe_X]; ring
  have hβ' : PowerSeries.C β * PowerSeries.C (h 2) = -1 := by
    rw [← map_mul, hβ]; simp
  unfold defectExpr
  rw [coe_clippedOp_tails, coe_clippedOp_tails, hb, hb, tailS_shift, tailS_shift,
    tailS_three (seriesOf h), tailS_three (seriesOf h ^ 2)]
  have hc0 : coeff 0 (seriesOf h) = h 0 := coeff_seriesOf h 0
  have hc1 : coeff 1 (seriesOf h) = h 1 := coeff_seriesOf h 1
  have hc2 : coeff 2 (seriesOf h) = h 2 := coeff_seriesOf h 2
  rw [hc0, hc1, hc2, coeff_sq_seriesOf_zero, coeff_sq_seriesOf_one, coeff_sq_seriesOf_two]
  simp only [Nat.cast_ofNat, show 2 - 1 = 1 from rfl, pow_one, map_mul, map_add, map_pow,
    map_ofNat, Polynomial.coe_mul, Polynomial.coe_C, Polynomial.coe_pow, Polynomial.coe_X]
  have e : (PowerSeries.X : K⟦X⟧) ^ (s + 3 - 1) = PowerSeries.X ^ s * PowerSeries.X ^ 2 := by
    rw [← pow_add]; rfl
  rw [e]
  linear_combination (2 * (PowerSeries.C (h 0) - seriesOf h) * PowerSeries.X ^ s *
    PowerSeries.X ^ 2 * ((a : K⟦X⟧) - PowerSeries.C β * PowerSeries.X ^ s)) * hβ'

theorem coeff_sq_seriesOf_three (h : ℕ → K) :
    coeff 3 (seriesOf h ^ 2) = 2 * h 0 * h 3 + 2 * h 1 * h 2 := by
  rw [sq, PowerSeries.coeff_mul]
  simp [Finset.Nat.antidiagonal_succ, coeff_seriesOf]; ring

theorem coeff_sq_seriesOf_four (h : ℕ → K) :
    coeff 4 (seriesOf h ^ 2) = 2 * h 0 * h 4 + 2 * h 1 * h 3 + h 2 ^ 2 := by
  rw [sq, PowerSeries.coeff_mul]
  simp [Finset.Nat.antidiagonal_succ, coeff_seriesOf]; ring

/-- A polynomial supported on three consecutive degrees. -/
theorem poly_three_terms (A : ℕ) (a : K[X]) (ha : ∀ i < A, a.coeff i = 0)
    (hd : ∀ j, A + 3 ≤ j → a.coeff j = 0) :
    a = Polynomial.C (a.coeff A) * Polynomial.X ^ A +
      Polynomial.C (a.coeff (A + 1)) * Polynomial.X ^ (A + 1) +
      Polynomial.C (a.coeff (A + 2)) * Polynomial.X ^ (A + 2) := by
  ext i
  simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
  by_cases h1 : i < A
  · rw [ha i h1]; simp [show i ≠ A by omega, show i ≠ A + 1 by omega, show i ≠ A + 2 by omega]
  · by_cases h2 : i = A
    · subst h2; simp
    · by_cases h3 : i = A + 1
      · subst h3; simp
      · by_cases h4 : i = A + 2
        · subst h4; simp
        · rw [hd i (by omega)]; simp [h2, h3, h4]

/-- The coefficient at `A + n` of a product with such a polynomial. -/
theorem coeff_mul_three_terms (A : ℕ) (a : K[X]) (ha : ∀ i < A, a.coeff i = 0)
    (hd : ∀ j, A + 3 ≤ j → a.coeff j = 0) (F : K⟦X⟧) (n : ℕ) (hn : 2 ≤ n) :
    coeff (A + n) (F * (a : K⟦X⟧)) = a.coeff A * coeff n F + a.coeff (A + 1) * coeff (n - 1) F +
      a.coeff (A + 2) * coeff (n - 2) F := by
  conv_lhs => rw [poly_three_terms A a ha hd]
  simp only [Polynomial.coe_add, Polynomial.coe_mul, Polynomial.coe_C, Polynomial.coe_pow,
    Polynomial.coe_X, mul_add, map_add]
  have e : ∀ (c : K) (k : ℕ), k ≤ A + n → F * (PowerSeries.C c * PowerSeries.X ^ k) =
      PowerSeries.C c * (PowerSeries.X ^ k * F) := fun c k _ => by ring
  rw [e _ _ (by omega), e _ _ (by omega), e _ _ (by omega)]
  simp only [PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul']
  rw [ite_eq_left (by omega), ite_eq_left (by omega), ite_eq_left (by omega)]
  rw [show A + n - A = n by omega, show A + n - (A + 1) = n - 1 by omega,
    show A + n - (A + 2) = n - 2 by omega]

theorem coeff_C_X_pow_mul_mul (β : K) (s n : ℕ) (F : K⟦X⟧) :
    coeff (s + n) (((Polynomial.C β * Polynomial.X ^ s : K[X]) : K⟦X⟧) * F) = β * coeff n F := by
  have : ((Polynomial.C β * Polynomial.X ^ s : K[X]) : K⟦X⟧) * F =
      PowerSeries.C β * (PowerSeries.X ^ s * F) := by
    rw [Polynomial.coe_mul, Polynomial.coe_C, Polynomial.coe_pow, Polynomial.coe_X]; ring
  rw [this, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul', ite_eq_left (by omega),
    show s + n - s = n by omega]

theorem sub_sub_eq_X_sq_mul (h : ℕ → K) :
    seriesOf h - PowerSeries.C (h 0) - PowerSeries.C (h 1) * PowerSeries.X =
      PowerSeries.X ^ 2 * mk (fun i => h (i + 2)) := by
  ext n
  simp only [map_sub, PowerSeries.coeff_X_pow_mul', coeff_seriesOf, PowerSeries.coeff_C,
    PowerSeries.coeff_C_mul, PowerSeries.coeff_X]
  rcases n with _ | _ | n
  · simp
  · simp
  · simp [coeff_mk]

/-- Against the two-cell row, the lowest coefficients of the quadratic equation force the
component carrying `a` to start four below the top and give one relation among its first
three coefficients. -/
theorem rowTwo_branch (s A : ℕ) (hAs : A + 1 ≤ s) (h : ℕ → K) (a : K[X]) (β : K)
    (hβ : β * h 2 = -1) (ha : ∀ i < A, a.coeff i = 0) (haA : a.coeff A ≠ 0)
    (hdeg : ∀ j, s + 2 ≤ j → a.coeff j = 0)
    (heq : ∀ n < 2 * (s + 3),
      coeff n (defectExpr (s + 3) 2 h a (Polynomial.C β * Polynomial.X ^ s)) = 0) :
    A + 1 = s ∧
      h 2 ^ 2 * a.coeff A +
        ((2 * h 0 * h 4 + 2 * h 1 * h 3 + h 2 ^ 2) * a.coeff A +
          (2 * h 0 * h 3 + 2 * h 1 * h 2) * a.coeff (A + 1) +
          (2 * h 0 * h 2 + h 1 ^ 2) * a.coeff (A + 2)) -
        2 * h 0 * (h 4 * a.coeff A + h 3 * a.coeff (A + 1) + h 2 * a.coeff (A + 2)) + 2 * h 1 = 0 := by
  have hh2 : h 2 ≠ 0 := fun e => by rw [e, mul_zero] at hβ; exact absurd hβ (by norm_num)
  have hβ0 : β ≠ 0 := fun e => by rw [e, zero_mul] at hβ; exact absurd hβ (by norm_num)
  set Br : K⟦X⟧ := (seriesOf h - PowerSeries.C (h 0) - PowerSeries.C (h 1) * PowerSeries.X) ^ 2 *
          (a : K⟦X⟧) +
          tailS (s + 3) (seriesOf h ^ 2 * (a : K⟦X⟧)) -
          2 * seriesOf h * tailS (s + 3) (seriesOf h * (a : K⟦X⟧)) +
          PowerSeries.C (2 * h 2) * (PowerSeries.C (h 0) - seriesOf h) * PowerSeries.X ^ 2 *
            ((Polynomial.C β * Polynomial.X ^ s : K[X]) : K⟦X⟧) with hBr
  have hBr0 : ∀ n < s + 6, coeff n Br = 0 := by
    intro n hn
    have := heq (s + n) (by omega)
    rw [defectExpr_two_row s h a β hβ, coeff_C_X_pow_mul_mul] at this
    exact (mul_eq_zero.mp this).resolve_left hβ0
  set R' : K⟦X⟧ := mk (fun i => h (i + 2)) with hR'
  have hR2 : (seriesOf h - PowerSeries.C (h 0) - PowerSeries.C (h 1) * PowerSeries.X) ^ 2 *
      (a : K⟦X⟧) = PowerSeries.X ^ 4 * (R' ^ 2 * (a : K⟦X⟧)) := by
    rw [sub_sub_eq_X_sq_mul]; ring
  have hRa : ∀ n, coeff n ((seriesOf h - PowerSeries.C (h 0) - PowerSeries.C (h 1) *
      PowerSeries.X) ^ 2 * (a : K⟦X⟧)) = if 4 ≤ n then coeff (n - 4) (R' ^ 2 * (a : K⟦X⟧)) else 0 := by
    intro n; rw [hR2, PowerSeries.coeff_X_pow_mul']
  have hR'a := coeff_mul_low (f := R' ^ 2) (g := (a : K⟦X⟧)) (N := A)
    (fun k hk => by rw [Polynomial.coeff_coe]; exact ha k hk)
  have hR'c : PowerSeries.constantCoeff (R' ^ 2) = h 2 ^ 2 := by simp [hR']
  have hlow : ∀ n < s + 3, coeff n Br = if 4 ≤ n then coeff (n - 4) (R' ^ 2 * (a : K⟦X⟧)) else 0 := by
    intro n hn
    have t1 : coeff n (tailS (s + 3) (seriesOf h ^ 2 * (a : K⟦X⟧))) = 0 := by
      rw [coeff_tailS, ite_eq_right (by omega)]
    have t2 : coeff n (2 * seriesOf h * tailS (s + 3) (seriesOf h * (a : K⟦X⟧))) = 0 := by
      have := (coeff_mul_low (f := 2 * seriesOf h) (g := tailS (s + 3) (seriesOf h * (a : K⟦X⟧)))
        (N := s + 3) (fun k hk => by rw [coeff_tailS, ite_eq_right (by omega)])).1 n hn
      exact this
    have t3 : coeff n (PowerSeries.C (2 * h 2) * (PowerSeries.C (h 0) - seriesOf h) *
        PowerSeries.X ^ 2 * ((Polynomial.C β * Polynomial.X ^ s : K[X]) : K⟦X⟧)) = 0 := by
      have e : PowerSeries.C (2 * h 2) * (PowerSeries.C (h 0) - seriesOf h) * PowerSeries.X ^ 2 *
          ((Polynomial.C β * Polynomial.X ^ s : K[X]) : K⟦X⟧) =
          PowerSeries.C (2 * h 2 * β) * (PowerSeries.X ^ (s + 2) *
            (PowerSeries.C (h 0) - seriesOf h)) := by
        rw [Polynomial.coe_mul, Polynomial.coe_C, Polynomial.coe_pow, Polynomial.coe_X, map_mul,
          pow_add]
        simp only [map_mul, map_ofNat]; ring
      rw [e, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul']
      by_cases hn2 : s + 2 ≤ n
      · rw [ite_eq_left hn2, show n - (s + 2) = 0 by omega]
        simp [coeff_seriesOf, constantCoeff_seriesOf']
      · rw [ite_eq_right hn2, mul_zero]
    rw [hBr, map_add, map_sub, map_add, hRa, t1, t2, t3]; ring
  have hge : s + 3 ≤ A + 4 := by
    by_contra hcon
    have h1 := hBr0 (A + 4) (by omega)
    rw [hlow (A + 4) (by omega), ite_eq_left (by omega), show A + 4 - 4 = A by omega,
      hR'a.2, hR'c, Polynomial.coeff_coe] at h1
    exact mul_ne_zero (pow_ne_zero 2 hh2) haA h1
  have hAeq : A + 1 = s := by omega
  refine ⟨hAeq, ?_⟩
  have hM := hBr0 (s + 3) (by omega)
  have hd3 : ∀ j, A + 3 ≤ j → a.coeff j = 0 := fun j hj => hdeg j (by omega)
  have tt1 : coeff (s + 3) (tailS (s + 3) (seriesOf h ^ 2 * (a : K⟦X⟧))) =
      a.coeff A * (2 * h 0 * h 4 + 2 * h 1 * h 3 + h 2 ^ 2) +
        a.coeff (A + 1) * (2 * h 0 * h 3 + 2 * h 1 * h 2) +
        a.coeff (A + 2) * (2 * h 0 * h 2 + h 1 ^ 2) := by
    rw [coeff_tailS, ite_eq_left le_rfl, show s + 3 = A + 4 by omega,
      coeff_mul_three_terms A a ha hd3 _ 4 (by omega), coeff_sq_seriesOf_four,
      show (4 - 1 : ℕ) = 3 from rfl, show (4 - 2 : ℕ) = 2 from rfl, coeff_sq_seriesOf_three,
      coeff_sq_seriesOf_two]
  have tt2 : coeff (s + 3) (2 * seriesOf h * tailS (s + 3) (seriesOf h * (a : K⟦X⟧))) =
      2 * h 0 * (a.coeff A * h 4 + a.coeff (A + 1) * h 3 + a.coeff (A + 2) * h 2) := by
    rw [(coeff_mul_low (f := 2 * seriesOf h) (g := tailS (s + 3) (seriesOf h * (a : K⟦X⟧)))
      (N := s + 3) (fun k hk => by rw [coeff_tailS, ite_eq_right (by omega)])).2,
      coeff_tailS, ite_eq_left le_rfl, show s + 3 = A + 4 by omega,
      coeff_mul_three_terms A a ha hd3 _ 4 (by omega)]
    simp only [coeff_seriesOf, show (4 - 1 : ℕ) = 3 from rfl, show (4 - 2 : ℕ) = 2 from rfl,
      map_mul, map_ofNat, constantCoeff_seriesOf']
  have tt3 : coeff (s + 3) (PowerSeries.C (2 * h 2) * (PowerSeries.C (h 0) - seriesOf h) *
      PowerSeries.X ^ 2 * ((Polynomial.C β * Polynomial.X ^ s : K[X]) : K⟦X⟧)) = 2 * h 1 := by
    have e : PowerSeries.C (2 * h 2) * (PowerSeries.C (h 0) - seriesOf h) * PowerSeries.X ^ 2 *
        ((Polynomial.C β * Polynomial.X ^ s : K[X]) : K⟦X⟧) =
        PowerSeries.C (2 * h 2 * β) * (PowerSeries.X ^ (s + 2) *
          (PowerSeries.C (h 0) - seriesOf h)) := by
      rw [Polynomial.coe_mul, Polynomial.coe_C, Polynomial.coe_pow, Polynomial.coe_X, map_mul,
        pow_add]
      simp only [map_mul, map_ofNat]; ring
    rw [e, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul', ite_eq_left (by omega),
      show s + 3 - (s + 2) = 1 by omega]
    simp [coeff_seriesOf]
    linear_combination (-2 * h 1) * hβ
  rw [hBr, map_add, map_sub, map_add, hRa, ite_eq_left (by omega),
    show s + 3 - 4 = A by omega, hR'a.2, hR'c, Polynomial.coeff_coe, tt1, tt2, tt3] at hM
  linear_combination hM

theorem coeff_shift_poly (α : K) (A : ℕ) (g : K[X]) (j : ℕ) :
    (Polynomial.C α * (Polynomial.X ^ A * g)).coeff (A + j) = α * g.coeff j := by
  rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow_mul', ite_eq_left (by omega),
    Nat.add_sub_cancel_left]

/-- The `A < B` branch against the two-cell row: with `a = α₀ z^A g`, `α₀ [H g]_L = -1` and
`g` of degree below `L = M - 1 - A`, the equation forces `L = 3` and
`h₁² g₂ = 2 h₂²`. -/
theorem rowTwo_exclusion (s A : ℕ) (hAs : A + 1 ≤ s) (h : ℕ → K) (g : K[X]) (α₀ β : K)
    (hg0 : g.coeff 0 = 1) (hgdeg : ∀ j, s + 2 ≤ A + j → g.coeff j = 0)
    (hβ : β * h 2 = -1) (hk : α₀ * coeff (s + 2 - A) (seriesOf h * (g : K⟦X⟧)) = -1)
    (heq : ∀ n < 2 * (s + 3), coeff n (defectExpr (s + 3) 2 h
      (Polynomial.C α₀ * (Polynomial.X ^ A * g)) (Polynomial.C β * Polynomial.X ^ s)) = 0) :
    A + 1 = s ∧ h 1 ^ 2 * g.coeff 2 = 2 * h 2 ^ 2 := by
  have hα : α₀ ≠ 0 := fun e => by rw [e, zero_mul] at hk; exact absurd hk (by norm_num)
  have hlow : ∀ i < A, (Polynomial.C α₀ * (Polynomial.X ^ A * g)).coeff i = 0 := by
    intro i hi
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow_mul', ite_eq_right (by omega), mul_zero]
  have hAa : (Polynomial.C α₀ * (Polynomial.X ^ A * g)).coeff A ≠ 0 := by
    have := coeff_shift_poly α₀ A g 0
    rw [add_zero, hg0, mul_one] at this
    rw [this]; exact hα
  have hdega : ∀ j, s + 2 ≤ j → (Polynomial.C α₀ * (Polynomial.X ^ A * g)).coeff j = 0 := by
    intro j hj
    obtain ⟨i, rfl⟩ : ∃ i, j = A + i := ⟨j - A, by omega⟩
    rw [coeff_shift_poly, hgdeg i hj, mul_zero]
  obtain ⟨hA, hrel⟩ := rowTwo_branch s A hAs h _ β hβ hlow hAa hdega heq
  refine ⟨hA, ?_⟩
  have c1 := coeff_shift_poly α₀ A g 1
  have c2 := coeff_shift_poly α₀ A g 2
  have c0 := coeff_shift_poly α₀ A g 0
  rw [add_zero] at c0
  rw [c0, c1, c2, hg0] at hrel
  have e3 : s + 2 - A = 3 := by omega
  rw [e3, PowerSeries.coeff_mul] at hk
  have hg3 : g.coeff 3 = 0 := hgdeg 3 (by omega)
  have hg4 : ∀ j, 3 ≤ j → g.coeff j = 0 := fun j hj => hgdeg j (by omega)
  simp [Finset.Nat.antidiagonal_succ, coeff_seriesOf, hg3, hg0] at hk
  have : α₀ * (h 1 ^ 2 * g.coeff 2 - 2 * h 2 ^ 2) = 0 := by
    linear_combination (-1 : K) * hrel + (2 * h 1) * hk
  have := (mul_eq_zero.mp this).resolve_left hα
  linear_combination this

end SkewCoframeRigidity.Unshifted
