/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCoframeRigidity.Unshifted.Exclusion.Disconnected.Scale
import SkewCoframeRigidity.Unshifted.Exclusion.Shift

/-!
# The shift of the letter `H_L` in the equation of two components

Formalizes `shields-2026-skew-coframe-rigidity.tex`, «Unshifted opposite-end exclusion»
(`ph:unshifted-exclusion`, disconnected corner, `A = B`).  Replacing `H` by `H + s z^L` and the
two top quotients by `k + s` changes `eqL` by exactly `s` times
`p (p - 1) z^{2L} H^{p-2} (k_F g - k_E c - z S)` modulo `z^{2L+2}`, where `z^{L+1} S = 𝒯(H)`;
there is no term of order `s²`.  Consequently, if `eqL` vanishes at precision `2L + 2` at both
`s = 0` and `s = 1`, the two top quotients agree and the first two coefficients of `S` are
those of the cap difference.
-/

namespace SkewCoframeRigidity.Unshifted

open PowerSeries SkewCoframeRigidity SkewCoframeRigidity.Coframe
open Polynomial hiding coeff

variable {K : Type*} [Field K]

theorem pow_add_expand_succ (H t : K⟦X⟧) (r : ℕ) :
    ∃ w : K⟦X⟧, (H + t) ^ (r + 1) = H ^ (r + 1) + ((r + 1 : ℕ) : K⟦X⟧) * t * H ^ r + t ^ 2 * w := by
  rcases r with _ | r
  · exact ⟨0, by simp⟩
  · obtain ⟨w, hw⟩ := pow_add_expand H t r
    exact ⟨w, by rw [hw]; push_cast; ring⟩

/-- The series `S` with `z^{L+1} S = 𝒯^{L+1}_{g,c}(H)`. -/
noncomputable def topTail (L : ℕ) (g c : K[X]) (H : K⟦X⟧) : K⟦X⟧ :=
  (c : K⟦X⟧) * mk (fun i => coeff (i + (L + 1)) (H * (g : K⟦X⟧))) -
    (g : K⟦X⟧) * mk (fun i => coeff (i + (L + 1)) (H * (c : K⟦X⟧)))

/-- The slope of the shift. -/
noncomputable def shiftSlope (L q : ℕ) (g c : K[X]) (kE kF : K) (H : K⟦X⟧) : K⟦X⟧ :=
  PowerSeries.C (((q + 2 : ℕ) : K) * ((q + 1 : ℕ) : K)) * PowerSeries.X ^ (2 * L) * H ^ q *
    (PowerSeries.C kF * (g : K⟦X⟧) - PowerSeries.C kE * (c : K⟦X⟧) -
      PowerSeries.X * topTail L g c H)

theorem eqL_shift (L q : ℕ) (hL : 2 ≤ L) (g c : K[X]) (hg0 : g.coeff 0 = 1) (hc0 : c.coeff 0 = 1)
    (kE kF s : K) (h : ℕ → K) :
    ∃ W : K⟦X⟧, eqL L (q + 2) g c (kE + s) (kF + s)
        (seriesOf h + PowerSeries.C s * PowerSeries.X ^ L) =
      eqL L (q + 2) g c kE kF (seriesOf h) +
        PowerSeries.C s * shiftSlope L q g c kE kF (seriesOf h) + PowerSeries.X ^ (2 * L + 2) * W := by
  obtain ⟨L', rfl⟩ : ∃ L', L = L' + 2 := ⟨L - 2, by omega⟩
  set H := seriesOf h with hH
  set t : K⟦X⟧ := PowerSeries.C s * PowerSeries.X ^ (L' + 2) with ht
  have hc1 : constantCoeff (H + t) = constantCoeff H := by
    simp [ht]
  obtain ⟨w, hw⟩ := pow_add_expand_succ H t q
  obtain ⟨Dg', hDg⟩ : (PowerSeries.X : K⟦X⟧) ∣ (g : K⟦X⟧) - (c : K⟦X⟧) :=
    PowerSeries.X_dvd_iff.mpr (by
      rw [map_sub, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
        ← PowerSeries.coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe,
        Polynomial.coeff_coe, hg0, hc0, sub_self])
  have hT1 : ((clippedOp (L' + 2 + 1) g c (H + t) : K[X]) : K⟦X⟧) =
      ((clippedOp (L' + 2 + 1) g c H : K[X]) : K⟦X⟧) +
        PowerSeries.C s * PowerSeries.X ^ (L' + 2) * ((g : K⟦X⟧) - (c : K⟦X⟧)) := by
    have := clippedOp_X_pow_mul_of_const_one (L' + 2) g c hg0 hc0 (PowerSeries.C s)
    rw [ht, clippedOp_add_right, Polynomial.coe_add, this]
    simp only [Polynomial.coe_mul, Polynomial.coe_C, Polynomial.coe_pow, Polynomial.coe_X,
      Polynomial.coe_sub, PowerSeries.constantCoeff_C]
  have hTp : ((clippedOp (L' + 2 + 1) g c ((H + t) ^ (q + 2)) : K[X]) : K⟦X⟧) =
      ((clippedOp (L' + 2 + 1) g c (H ^ (q + 2)) : K[X]) : K⟦X⟧) +
        PowerSeries.C (s * ((q + 2 : ℕ) : K) * constantCoeff H ^ (q + 1)) * PowerSeries.X ^ (L' + 2) *
          ((g : K⟦X⟧) - (c : K⟦X⟧)) := by
    have := clippedOp_power_expand (L' + 2) q (by omega) g c H s
    rw [ht, this]
    simp only [Polynomial.coe_add, Polynomial.coe_mul, Polynomial.coe_C, Polynomial.coe_pow,
      Polynomial.coe_X, Polynomial.coe_sub, hg0, hc0, map_one, one_mul]
    simp only [Nat.cast_add, Nat.cast_ofNat]
  have hS : ((clippedOp (L' + 2 + 1) g c H : K[X]) : K⟦X⟧) =
      PowerSeries.X ^ (L' + 2 + 1) * topTail (L' + 2) g c H := by
    rw [clippedOp_eq_tails]; unfold topTail; ring
  refine ⟨PowerSeries.C (((q + 2 : ℕ) : K)) * PowerSeries.C s ^ 2 * w * PowerSeries.X ^ L' *
    (PowerSeries.C kF * (g : K⟦X⟧) - PowerSeries.C kE * (c : K⟦X⟧) -
      PowerSeries.X * topTail (L' + 2) g c H), ?_⟩
  unfold eqL shiftSlope
  simp only [show q + 2 - 1 = q + 1 from rfl]
  rw [hT1, hTp, hw, hc1, hS]
  have hq1 : ∀ n : ℕ, PowerSeries.C ((n : ℕ) : K) = ((n : ℕ) : K⟦X⟧) := fun n => map_natCast _ n
  simp only [map_mul, map_add, map_sub, show q + 2 - 1 = q + 1 from rfl, hq1, Nat.cast_add,
    Nat.cast_one, Nat.cast_ofNat, map_pow, map_natCast, ht] at *
  simp only [map_ofNat, map_one]
  ring

/-- If `eqL` vanishes at precision `2L + 2` both at `H` and at `H + z^L` with the top quotients
shifted by one, the top quotients agree and the first coefficients of the cap difference match. -/
theorem eqL_consequence [CharZero K] (L q : ℕ) (hL : 2 ≤ L) (g c : K[X]) (hg0 : g.coeff 0 = 1)
    (hc0 : c.coeff 0 = 1) (kE kF : K) (h : ℕ → K) (hϑ : h 0 ≠ 0)
    (e0 : ∀ m < 2 * L + 2, coeff m (eqL L (q + 2) g c kE kF (seriesOf h)) = 0)
    (e1 : ∀ m < 2 * L + 2, coeff m (eqL L (q + 2) g c (kE + 1) (kF + 1)
      (seriesOf h + PowerSeries.C 1 * PowerSeries.X ^ L)) = 0) :
    kE = kF ∧ coeff (L + 1) (seriesOf h * (g : K⟦X⟧)) - coeff (L + 1) (seriesOf h * (c : K⟦X⟧)) =
      kE * (g.coeff 1 - c.coeff 1) := by
  obtain ⟨W, hW⟩ := eqL_shift L q hL g c hg0 hc0 kE kF 1 h
  have hsl : ∀ m < 2 * L + 2, coeff m (shiftSlope L q g c kE kF (seriesOf h)) = 0 := by
    intro m hm
    have a := e1 m hm
    rw [hW, map_add, map_add, e0 m hm, PowerSeries.coeff_X_pow_mul', ite_eq_right (by omega),
      map_one, one_mul, zero_add, add_zero] at a
    exact a
  set Z : K⟦X⟧ := PowerSeries.C kF * (g : K⟦X⟧) - PowerSeries.C kE * (c : K⟦X⟧) -
    PowerSeries.X * topTail L g c (seriesOf h) with hZ
  set κ : K := ((q + 2 : ℕ) : K) * ((q + 1 : ℕ) : K) with hκ
  have hκ0 : κ ≠ 0 := by
    rw [hκ]
    exact mul_ne_zero (by exact_mod_cast (by omega : q + 2 ≠ 0))
      (by exact_mod_cast (by omega : q + 1 ≠ 0))
  have hform : ∀ i, coeff (2 * L + i) (shiftSlope L q g c kE kF (seriesOf h)) =
      κ * coeff i (seriesOf h ^ q * Z) := by
    intro i
    have : shiftSlope L q g c kE kF (seriesOf h) =
        PowerSeries.C κ * (PowerSeries.X ^ (2 * L) * (seriesOf h ^ q * Z)) := by
      unfold shiftSlope; rw [hκ, hZ]; ring
    rw [this, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul', ite_eq_left (by omega),
      Nat.add_sub_cancel_left]
  have hZ0 : constantCoeff Z = kF - kE := by
    rw [hZ]
    simp only [map_sub, map_mul, PowerSeries.constantCoeff_C, PowerSeries.constantCoeff_X,
      zero_mul, sub_zero]
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
      Polynomial.coeff_coe, Polynomial.coeff_coe, hg0, hc0]
    ring
  have hc0H : constantCoeff (seriesOf h ^ q) = h 0 ^ q := by
    rw [map_pow, constantCoeff_seriesOf']
  have a0 := hsl (2 * L + 0) (by omega)
  rw [hform, show (0 : ℕ) = 0 from rfl] at a0
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, map_mul, hc0H, hZ0] at a0
  have hkk : kE = kF := by
    have := (mul_eq_zero.mp a0).resolve_left hκ0
    have := (mul_eq_zero.mp this).resolve_left (pow_ne_zero _ hϑ)
    linear_combination -this
  refine ⟨hkk, ?_⟩
  have a1 := hsl (2 * L + 1) (by omega)
  rw [hform, coeff_one_mul, hc0H, hZ0, hkk, sub_self, mul_zero, add_zero] at a1
  have hZ1 : coeff 1 Z = kF * g.coeff 1 - kE * c.coeff 1 -
      coeff 0 (topTail L g c (seriesOf h)) := by
    rw [hZ]
    simp only [map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_succ_X_mul]
    rw [Polynomial.coeff_coe, Polynomial.coeff_coe]
  have hT0 : coeff 0 (topTail L g c (seriesOf h)) =
      coeff (L + 1) (seriesOf h * (g : K⟦X⟧)) - coeff (L + 1) (seriesOf h * (c : K⟦X⟧)) := by
    unfold topTail
    rw [map_sub, PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_zero_eq_constantCoeff_apply]
    simp only [map_mul, PowerSeries.constantCoeff_mk]
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
      Polynomial.coeff_coe, Polynomial.coeff_coe, hg0, hc0]
    simp
  rw [hZ1, hT0] at a1
  have := (mul_eq_zero.mp a1).resolve_left hκ0
  have := (mul_eq_zero.mp this).resolve_left (pow_ne_zero _ hϑ)
  rw [hkk] at *
  linear_combination -this

theorem clippedOp_X_pow_mul_eq_zero (L N : ℕ) (hN : L + 1 ≤ N) (g c : K[X]) (u : K⟦X⟧) :
    clippedOp (L + 1) g c (PowerSeries.X ^ N * u) = 0 := by
  have h : ∀ F : K⟦X⟧, trunc (L + 1) (PowerSeries.X ^ N * u * F) = 0 := by
    intro F
    have : PowerSeries.X ^ N * u * F =
        PowerSeries.X ^ (L + 1) * (PowerSeries.X ^ (N - (L + 1)) * (u * F)) := by
      rw [show N = (L + 1) + (N - (L + 1)) by omega, pow_add]
      simp only [Nat.add_sub_cancel_left]; ring
    rw [this, trunc_X_pow_self_mul]
  unfold clippedOp
  rw [h, h]; simp

/-- `eqL` modulo `z^N` depends only on `H` modulo `z^N`, for `N ≥ L + 1`. -/
theorem eqL_congr (L p : ℕ) (g c : K[X]) (kE kF : K) (H H' R : K⟦X⟧) (N : ℕ) (hN : L + 1 ≤ N)
    (hH : H' = H + PowerSeries.X ^ N * R) :
    ∃ R' : K⟦X⟧, eqL L p g c kE kF H' = eqL L p g c kE kF H + PowerSeries.X ^ N * R' := by
  obtain ⟨P1, hP1⟩ : (H' - H) ∣ H' ^ p - H ^ p := sub_dvd_pow_sub_pow _ _ _
  obtain ⟨P2, hP2⟩ : (H' - H) ∣ H' ^ (p - 1) - H ^ (p - 1) := sub_dvd_pow_sub_pow _ _ _
  have hsub : H' - H = PowerSeries.X ^ N * R := by rw [hH]; ring
  rw [hsub] at hP1 hP2
  have e1 : H' ^ p = H ^ p + PowerSeries.X ^ N * (R * P1) := by
    linear_combination hP1
  have e2 : H' ^ (p - 1) = H ^ (p - 1) + PowerSeries.X ^ N * (R * P2) := by
    linear_combination hP2
  have hT1 : clippedOp (L + 1) g c (H' ^ p) = clippedOp (L + 1) g c (H ^ p) := by
    rw [e1, clippedOp_add_right, clippedOp_X_pow_mul_eq_zero L N hN, add_zero]
  have hT2 : clippedOp (L + 1) g c H' = clippedOp (L + 1) g c H := by
    rw [hH, clippedOp_add_right, clippedOp_X_pow_mul_eq_zero L N hN, add_zero]
  have hc : constantCoeff H' = constantCoeff H := by
    rw [hH]
    have : 1 ≤ N := by omega
    obtain ⟨N', rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by omega⟩
    simp [pow_succ]
  refine ⟨PowerSeries.C (p : K) * (R * P2) * (PowerSeries.X ^ L *
    (PowerSeries.C kF * (g : K⟦X⟧) - PowerSeries.C kE * (c : K⟦X⟧)) -
    ((clippedOp (L + 1) g c H : K[X]) : K⟦X⟧)), ?_⟩
  unfold eqL
  rw [hT1, hT2, hc, e2]
  ring

theorem eqL_map {K' : Type*} [Field K'] (f : K →+* K') (L p : ℕ) (g c : K[X]) (kE kF : K)
    (H : K⟦X⟧) :
    PowerSeries.map f (eqL L p g c kE kF H) =
      eqL L p (g.map f) (c.map f) (f kE) (f kF) (PowerSeries.map f H) := by
  unfold eqL
  have hcl : ∀ u : K⟦X⟧, PowerSeries.map f ((clippedOp (L + 1) g c u : K[X]) : K⟦X⟧) =
      ((clippedOp (L + 1) (g.map f) (c.map f) (PowerSeries.map f u) : K'[X]) : K'⟦X⟧) := by
    intro u
    rw [← clippedOp_map, Polynomial.polynomial_map_coe]
  have hcc : constantCoeff (PowerSeries.map f H) = f (constantCoeff H) := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simp only [map_sub, map_mul, map_pow, PowerSeries.map_C, map_natCast, hcc, PowerSeries.map_X]
  rw [hcl (H ^ p), hcl H]
  simp only [map_pow, Polynomial.polynomial_map_coe]

end SkewCoframeRigidity.Unshifted
