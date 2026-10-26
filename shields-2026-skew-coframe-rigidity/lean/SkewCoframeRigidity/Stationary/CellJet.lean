/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCoframeRigidity.Stationary.CellPowers

/-!
# The second pole jet of the cell case

Formalizes `sc:cell-second-jet` in `shields-2026-skew-coframe-rigidity.tex`.  For a cell
(`g = 1`, `k = H_1`, `L = 1`) and the potential `r(H) = -p H^{p-1}`, the coefficient of degree
`M + d + 1` of the derivative of the one-power equation is `C(p,2) ϑ^{p-2} H_1 Δ_d`.
-/

namespace SkewCoframeRigidity.Coframe

open SkewCofactorIndependence Polynomial
open scoped Polynomial

theorem trunc_one_coe {F : Type*} [CommRing F] (f : PowerSeries F) :
    (PowerSeries.trunc 1 f : PowerSeries F) = PowerSeries.C (PowerSeries.coeff 0 f) := by
  ext i
  rw [Polynomial.coeff_coe, PowerSeries.coeff_trunc, PowerSeries.coeff_C]
  by_cases h : i = 0
  · subst h; simp
  · simp [h]

theorem coeff_mul_congr_low {F : Type*} [CommRing F] (n : ℕ) (r f f' : PowerSeries F)
    (h : ∀ i ≤ n, PowerSeries.coeff i f = PowerSeries.coeff i f') :
    PowerSeries.coeff n (r * f) = PowerSeries.coeff n (r * f') := by
  rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
  rw [h x.2 (by omega)]

theorem cell_second_jet (M a d q : ℕ) (hMa : a + 2 = M) (hd : d + 2 ≤ a)
    (G C : CohField[X]) (k : CohField) (hk : k ≠ 0) (hG0 : G.coeff 0 = 1) (hC0 : C.coeff 0 = 1)
    (hG : dS (M - 1) (G : PowerSeries CohField) =
      ((-(Polynomial.C k⁻¹ * Polynomial.X ^ a * 1) : CohField[X]) : PowerSeries CohField))
    (hC : dS (M - 1) (C : PowerSeries CohField) =
      ((-(Polynomial.C k⁻¹ * Polynomial.X ^ a * 1) : CohField[X]) : PowerSeries CohField))
    (hΔ : ∀ i < d, (C - G).coeff i = 0)
    (hkdef : PowerSeries.coeff 1 (letterSeries * ((1 : CohField[X]) : PowerSeries CohField)) = k)
    (hdef : ∀ j ≤ M, (clippedOp M G C letterSeries).coeff j = 0)
    (r ψ : PowerSeries CohField) (hψ : dS (M - 1) r = PowerSeries.X ^ (M - 1) * ψ)
    (hr : r = -(PowerSeries.C ((q + 2 : ℕ) : CohField) * letterSeries ^ (q + 1))) :
    PowerSeries.coeff (M + d + 1) (dS (M - 1)
      (((clippedOp M G C (PowerSeries.X * letterSeries ^ (q + 2)) : CohField[X]) :
          PowerSeries CohField) +
        PowerSeries.X * ((clippedOp M G C letterSeries : CohField[X]) : PowerSeries CohField) * r))
      = ((q + 2).choose 2 : CohField) * cohLetters 0 ^ q * k * (C - G).coeff d := by
  have hMm : M - 1 + 1 = M := by omega
  rw [jet_identity M a 1 (q + 2) (by omega) G C 1 k hk hG0 hC0 hG hC hkdef r ψ hψ,
    map_add, show M + d + 1 = (a + 1) + (d + 2) by omega, PowerSeries.coeff_X_pow_mul',
    if_pos (by omega), Nat.add_sub_cancel_left]
  have hcoe1 : ((1 : CohField[X]) : PowerSeries CohField) = 1 := Polynomial.coe_one
  set ΔS : PowerSeries CohField := ((C - G : CohField[X]) : PowerSeries CohField) with hΔS
  have hΔ' : ∀ i < d, PowerSeries.coeff i ΔS = 0 := fun i hi => by
    rw [hΔS, Polynomial.coeff_coe]; exact hΔ i hi
  set K := letterSeries with hK
  have hD0 : PowerSeries.coeff (a + 1 + (d + 2)) (PowerSeries.X *
      ((clippedOp M G C letterSeries : CohField[X]) : PowerSeries CohField) *
        (PowerSeries.X ^ (M - 1) * ψ)) = 0 := by
    have : PowerSeries.X * ((clippedOp M G C letterSeries : CohField[X]) : PowerSeries CohField) *
        (PowerSeries.X ^ (M - 1) * ψ) = PowerSeries.X ^ M *
        (((clippedOp M G C letterSeries : CohField[X]) : PowerSeries CohField) * ψ) := by
      have hX : (PowerSeries.X : PowerSeries CohField) ^ M = PowerSeries.X * PowerSeries.X ^ (M - 1) := by
        rw [← pow_succ', hMm]
      rw [hX]
      ring
    rw [this, PowerSeries.coeff_X_pow_mul', if_pos (by omega),
      show a + 1 + (d + 2) - M = d + 1 by omega]
    exact coeff_defect_mul_eq_zero _ _ M (d + 1) hdef (by omega)
  have hKc : PowerSeries.coeff 1 K = k := by rw [← hkdef, hcoe1, mul_one]
  have hKc1 : PowerSeries.coeff 1 K = cohLetters 1 := by simp [hK, letterSeries, seriesOf]
  have hK0 : PowerSeries.coeff 0 K = cohLetters 0 := by simp [hK, letterSeries, seriesOf]
  rw [hD0, add_zero]
  have hlt1 : ∀ i ≤ d + 2, i < M - 1 := fun i hi => by omega
  have hlt2 : ∀ i ≤ d + 2, i < M := fun i hi => by omega
  have hT1 : ∀ i ≤ d + 2, PowerSeries.coeff i
      (PowerSeries.C (-k⁻¹) * ((1 : PowerSeries CohField) *
          ((PowerSeries.trunc (M - 1) (K ^ (q + 2) * ΔS) : CohField[X]) : PowerSeries CohField)) +
        PowerSeries.C k⁻¹ * (ΔS * ((PowerSeries.trunc 1 (K ^ (q + 2) * 1) : CohField[X]) :
          PowerSeries CohField))) =
      PowerSeries.coeff i (PowerSeries.C (-k⁻¹) * (K ^ (q + 2) * ΔS) +
        PowerSeries.C k⁻¹ * (ΔS * PowerSeries.C (cohLetters 0 ^ (q + 2)))) := by
    intro i hi
    rw [map_add, map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul,
      PowerSeries.coeff_C_mul, one_mul, mul_one, trunc_one_coe, ← hK0, ← coeff_zero_pow']
    congr 2
    · rw [Polynomial.coeff_coe, PowerSeries.coeff_trunc, if_pos (hlt1 i hi)]
  have hT2 : ∀ i ≤ d + 2, PowerSeries.coeff i
      (PowerSeries.C (-k⁻¹) * ((1 : PowerSeries CohField) *
          ((PowerSeries.trunc M (K * ΔS) : CohField[X]) : PowerSeries CohField)) +
        PowerSeries.C k⁻¹ * (ΔS * ((PowerSeries.trunc 1 (K * 1) : CohField[X]) :
          PowerSeries CohField))) =
      PowerSeries.coeff i (PowerSeries.C (-k⁻¹) * (K * ΔS) +
        PowerSeries.C k⁻¹ * (ΔS * PowerSeries.C (cohLetters 0))) := by
    intro i hi
    rw [map_add, map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul,
      PowerSeries.coeff_C_mul, one_mul, mul_one, trunc_one_coe, ← hK0]
    congr 2
    · rw [Polynomial.coeff_coe, PowerSeries.coeff_trunc, if_pos (hlt2 i hi)]
  rw [hcoe1] at *
  rw [map_add, coeff_mul_congr_low _ _ _ _ hT2]
  rw [hr, hT1 (d + 2) le_rfl, ← map_add]
  have hid : PowerSeries.C (-k⁻¹) * (K ^ (q + 2) * ΔS) +
        PowerSeries.C k⁻¹ * (ΔS * PowerSeries.C (cohLetters 0 ^ (q + 2))) +
      -(PowerSeries.C ((q + 2 : ℕ) : CohField) * K ^ (q + 1)) *
        (PowerSeries.C (-k⁻¹) * (K * ΔS) + PowerSeries.C k⁻¹ * (ΔS * PowerSeries.C (cohLetters 0)))
      = PowerSeries.C k⁻¹ * (ΔS * cellF K (q + 2)) := by
    unfold cellF
    have e1 : q + 2 - 1 = q + 1 := rfl
    rw [e1, hK0]
    simp only [map_mul, map_sub, map_add, map_neg, map_pow, map_natCast, map_one]
    push_cast
    ring_nf
  rw [hid, PowerSeries.coeff_C_mul]
  have hlow : ∀ j, j < 2 → PowerSeries.coeff j (cellF K (q + 2)) = 0 := by
    intro j hj
    obtain ⟨h0, h1, -⟩ := cellF_coeff K q
    interval_cases j <;> assumption
  rw [PowerSeries.coeff_mul, Finset.sum_eq_single (d, 2)]
  · obtain ⟨-, -, h2⟩ := cellF_coeff K q
    have hk1 : cohLetters 1 = k := hKc1.symm.trans hKc
    rw [h2, hKc, hK0]
    have hd' : PowerSeries.coeff (d, 2).1 ΔS = (C - G).coeff d := by
      rw [hΔS, Polynomial.coeff_coe]
    rw [hd']
    field_simp
  · rintro ⟨i, j⟩ hij hne
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hij
    by_cases hi : i < d
    · rw [hΔ' i hi, zero_mul]
    · have hj : j < 2 := by
        by_contra hj; apply hne; simp only [Prod.mk.injEq]; omega
      rw [hlow j hj, mul_zero]
  · intro h; exact absurd (by simp) h

end SkewCoframeRigidity.Coframe
