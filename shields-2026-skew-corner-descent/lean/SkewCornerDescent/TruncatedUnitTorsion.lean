/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.Order
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic

/-!
# Torsion-free normalized units in finite coefficient windows

Supports `shields-2026-skew-corner-descent.tex` (`prop:closure-pin`). A power
congruent to one modulo a fixed power of the variable forces its constant-one
base congruent to one. This is a finite-window statement, not exact power-series
torsion. Sorry-free.
-/

namespace SkewCornerDescent

open scoped BigOperators

/-- **Differs from the paper's route.** The geometric sum multiplying `Z - 1`
has nonzero constant coefficient and hence is a unit. Canceling that unit gives
the finite formal-logarithm conclusion without constructing logarithms. -/
theorem normalized_unit_power_dvd {F : Type*} [Field F] [CharZero F]
    (Z : PowerSeries F) (b N : ℕ) (hb : 0 < b)
    (hZ : PowerSeries.constantCoeff Z = 1)
    (hpow : PowerSeries.X ^ N ∣ Z ^ b - 1) :
    PowerSeries.X ^ N ∣ Z - 1 := by
  let G := ∑ i ∈ Finset.range b, Z ^ i
  have hG : PowerSeries.constantCoeff G = (b : F) := by
    simp [G, map_sum, map_pow, hZ]
  have hG0 : PowerSeries.constantCoeff G ≠ 0 := by
    rw [hG]
    exact Nat.cast_ne_zero.mpr (Nat.ne_of_gt hb)
  have hfactor : G * (Z - 1) = Z ^ b - 1 := geom_sum_mul Z b
  have hrecover : Z - 1 = G⁻¹ * (Z ^ b - 1) := by
    rw [← hfactor, ← mul_assoc, PowerSeries.inv_mul_cancel G hG0, one_mul]
  rw [hrecover]
  obtain ⟨q, hq⟩ := hpow
  refine ⟨G⁻¹ * q, ?_⟩
  rw [hq]
  ring

/-- Constant-one units have no nontrivial finite-order jet in characteristic
zero. Only the supplied finite coefficient window is concluded. -/
theorem normalized_unit_power_coeff {F : Type*} [Field F] [CharZero F]
    (Z : PowerSeries F) (b N : ℕ) (hb : 0 < b)
    (hZ : PowerSeries.constantCoeff Z = 1)
    (hpow : ∀ k < N, PowerSeries.coeff k (Z ^ b) = PowerSeries.coeff k 1) :
    ∀ k < N, PowerSeries.coeff k Z = PowerSeries.coeff k 1 := by
  have hd : PowerSeries.X ^ N ∣ Z ^ b - 1 := by
    rw [PowerSeries.X_pow_dvd_iff]
    intro k hk
    rw [map_sub, hpow k hk, sub_self]
  have h := normalized_unit_power_dvd Z b N hb hZ hd
  rw [PowerSeries.X_pow_dvd_iff] at h
  intro k hk
  exact sub_eq_zero.mp (by simpa only [map_sub] using h k hk)

/-- A constant-unit factor can be canceled in any finite coefficient window. -/
theorem unit_jet_cancel_left {F : Type*} [Field F]
    (A B C : PowerSeries F) (N : ℕ) (hA : PowerSeries.constantCoeff A ≠ 0)
    (hprod : PowerSeries.X ^ N ∣ A * B - A * C) :
    PowerSeries.X ^ N ∣ B - C := by
  have he : B - C = A⁻¹ * (A * B - A * C) := by
    rw [← mul_sub, ← mul_assoc, PowerSeries.inv_mul_cancel A hA, one_mul]
  rw [he]
  obtain ⟨q, hq⟩ := hprod
  refine ⟨A⁻¹ * q, ?_⟩
  rw [hq]
  ring

/-- Equal left jets and equal product jets determine equal right jets, retaining
the original finite precision rather than asserting equality of entire series. -/
theorem unit_jet_product_right {F : Type*} [Field F]
    (A B C D : PowerSeries F) (N : ℕ) (hA : PowerSeries.constantCoeff A ≠ 0)
    (hleft : ∀ k < N, PowerSeries.coeff k A = PowerSeries.coeff k C)
    (hprod : ∀ k < N, PowerSeries.coeff k (A * B) = PowerSeries.coeff k (C * D)) :
    ∀ k < N, PowerSeries.coeff k B = PowerSeries.coeff k D := by
  have hl : PowerSeries.X ^ N ∣ A - C := by
    rw [PowerSeries.X_pow_dvd_iff]
    intro k hk
    rw [map_sub, hleft k hk, sub_self]
  have hp : PowerSeries.X ^ N ∣ A * B - C * D := by
    rw [PowerSeries.X_pow_dvd_iff]
    intro k hk
    rw [map_sub, hprod k hk, sub_self]
  have hd : PowerSeries.X ^ N ∣ (A - C) * D := by
    obtain ⟨q, hq⟩ := hl
    exact ⟨q * D, by rw [hq, mul_assoc]⟩
  have he : A * B - A * D = (A * B - C * D) - (A - C) * D := by ring
  have h := unit_jet_cancel_left A B D N hA (he ▸ dvd_sub hp hd)
  rw [PowerSeries.X_pow_dvd_iff] at h
  intro k hk
  exact sub_eq_zero.mp (by simpa only [map_sub] using h k hk)

end SkewCornerDescent
