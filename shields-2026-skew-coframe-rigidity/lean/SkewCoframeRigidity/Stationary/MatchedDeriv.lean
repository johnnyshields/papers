/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCoframeRigidity.Stationary.NeitherCase

/-!
# The derivative of the clipped operator for matched coframes

When `∂G = ∂C = v`, the derivative of `𝒯_{G,C}(u)` is
`v [u (C - G)]_{<M} - (C - G) [u v]_{<M} + 𝒯_{G,C}(∂u)`.
This is the computation behind `sc:complete-pole-bracket` in
`shields-2026-skew-coframe-rigidity.tex`.
-/

namespace SkewCoframeRigidity.Coframe

open SkewCofactorIndependence Polynomial
open scoped Polynomial

theorem dS_clippedOp_matched (m M : ℕ) (G C : CohField[X]) (u v : PowerSeries CohField)
    (hG : dS m (G : PowerSeries CohField) = v) (hC : dS m (C : PowerSeries CohField) = v) :
    dS m ((clippedOp M G C u : CohField[X]) : PowerSeries CohField) =
      v * (PowerSeries.trunc M (u * ((C - G : CohField[X]) : PowerSeries CohField)) :
        PowerSeries CohField) -
      ((C - G : CohField[X]) : PowerSeries CohField) *
        (PowerSeries.trunc M (u * v) : PowerSeries CohField) +
      ((clippedOp M G C (dS m u) : CohField[X]) : PowerSeries CohField) := by
  unfold clippedOp
  simp only [Polynomial.coe_sub, Polynomial.coe_mul]
  rw [dS_sub, dS_mul, dS_mul, dS_trunc, dS_trunc, dS_mul, dS_mul, hG, hC]
  simp only [mul_sub, sub_mul, map_sub, map_add, Polynomial.coe_add, Polynomial.coe_sub,
    add_mul, mul_add]
  ring

theorem coeff_mul_trunc_of_lt {F : Type*} [CommRing F] (K n : ℕ) (hn : n < K)
    (f h : PowerSeries F) :
    PowerSeries.coeff n (f * (PowerSeries.trunc K h : PowerSeries F)) =
      PowerSeries.coeff n (f * h) := by
  rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
  rw [Polynomial.coeff_coe, PowerSeries.coeff_trunc, if_pos (by omega)]

theorem trunc_X_pow_mul_shift {F : Type*} [CommRing F] (M j : ℕ) (hj : j ≤ M)
    (f : PowerSeries F) :
    (PowerSeries.trunc M (PowerSeries.X ^ j * f) : PowerSeries F) =
      PowerSeries.X ^ j * (PowerSeries.trunc (M - j) f : PowerSeries F) := by
  ext i
  rw [Polynomial.coeff_coe, PowerSeries.coeff_trunc, PowerSeries.coeff_X_pow_mul',
    PowerSeries.coeff_X_pow_mul', Polynomial.coeff_coe, PowerSeries.coeff_trunc]
  by_cases h1 : j ≤ i
  · by_cases h2 : i < M
    · rw [if_pos h2, if_pos h1, if_pos h1, if_pos (by omega)]
    · rw [if_neg h2, if_pos h1, if_neg (by omega)]
  · rw [if_neg h1, if_neg h1]
    by_cases h2 : i < M <;> simp [h2]

theorem coeff_mul_tail {F : Type*} [CommRing F] (L d : ℕ) (Δ : PowerSeries F)
    (hΔ : ∀ i < d, PowerSeries.coeff i Δ = 0) (h : PowerSeries F) :
    PowerSeries.coeff (L + d) (Δ * (h - (PowerSeries.trunc L h : PowerSeries F))) =
      PowerSeries.coeff d Δ * PowerSeries.coeff L h := by
  rw [PowerSeries.coeff_mul, Finset.sum_eq_single (d, L)]
  · simp [PowerSeries.coeff_trunc]
  · rintro ⟨i, j⟩ hij hne
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hij
    by_cases hi : i < d
    · rw [hΔ i hi, zero_mul]
    · have hj : j < L := by
        by_contra hj
        apply hne
        simp only [Prod.mk.injEq]; omega
      rw [map_sub, Polynomial.coeff_coe, PowerSeries.coeff_trunc, if_pos hj, sub_self, mul_zero]
  · intro h'; exact absurd (by simp [add_comm]) h'

theorem coeff_mul_tail_lt {F : Type*} [CommRing F] (L d n : ℕ) (hn : n < L + d)
    (Δ : PowerSeries F) (hΔ : ∀ i < d, PowerSeries.coeff i Δ = 0) (h : PowerSeries F) :
    PowerSeries.coeff n (Δ * (h - (PowerSeries.trunc L h : PowerSeries F))) = 0 := by
  rw [PowerSeries.coeff_mul]
  refine Finset.sum_eq_zero fun x hx => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
  by_cases hi : x.1 < d
  · rw [hΔ _ hi, zero_mul]
  · rw [map_sub, Polynomial.coeff_coe, PowerSeries.coeff_trunc, if_pos (by omega), sub_self,
      mul_zero]

theorem jetA {F : Type*} [Field F] (K L d : ℕ) (hK : L + d < K) (k : F) (gS ΔS Hp : PowerSeries F)
    (hΔ : ∀ i < d, PowerSeries.coeff i ΔS = 0) :
    PowerSeries.coeff (L + d)
      (PowerSeries.C (-k⁻¹) * (gS * (PowerSeries.trunc K (Hp * ΔS) : PowerSeries F)) +
        PowerSeries.C k⁻¹ * (ΔS * (PowerSeries.trunc L (Hp * gS) : PowerSeries F))) =
      -k⁻¹ * (PowerSeries.coeff d ΔS * PowerSeries.coeff L (Hp * gS)) := by
  rw [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul,
    coeff_mul_trunc_of_lt K _ hK]
  have h1 := coeff_mul_tail L d ΔS hΔ (Hp * gS)
  rw [mul_sub, map_sub] at h1
  have h2 : PowerSeries.coeff (L + d) (gS * (Hp * ΔS)) =
      PowerSeries.coeff (L + d) (ΔS * (Hp * gS)) := by ring_nf
  rw [h2]
  have h3 : PowerSeries.coeff (L + d) (ΔS * (PowerSeries.trunc L (Hp * gS) : PowerSeries F)) =
      PowerSeries.coeff (L + d) (ΔS * (Hp * gS)) -
        PowerSeries.coeff d ΔS * PowerSeries.coeff L (Hp * gS) := by
    rw [← h1]; ring
  rw [h3]; ring

theorem jetB {F : Type*} [Field F] (M L d : ℕ) (hK : L + d < M) (k : F) (gS ΔS Hs r : PowerSeries F)
    (hΔ : ∀ i < d, PowerSeries.coeff i ΔS = 0) :
    PowerSeries.coeff (L + d) (r *
      (PowerSeries.C (-k⁻¹) * (gS * (PowerSeries.trunc M (Hs * ΔS) : PowerSeries F)) +
        PowerSeries.C k⁻¹ * (ΔS * (PowerSeries.trunc L (Hs * gS) : PowerSeries F)))) =
      -k⁻¹ * (PowerSeries.constantCoeff r *
        (PowerSeries.coeff d ΔS * PowerSeries.coeff L (Hs * gS))) := by
  set Y := PowerSeries.C (-k⁻¹) * (gS * (PowerSeries.trunc M (Hs * ΔS) : PowerSeries F)) +
        PowerSeries.C k⁻¹ * (ΔS * (PowerSeries.trunc L (Hs * gS) : PowerSeries F)) with hY
  have hYi : ∀ i, i ≤ L + d → PowerSeries.coeff i Y =
      -k⁻¹ * PowerSeries.coeff i (ΔS * (Hs * gS - (PowerSeries.trunc L (Hs * gS) :
        PowerSeries F))) := by
    intro i hi
    rw [hY, map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul,
      coeff_mul_trunc_of_lt M _ (by omega), mul_sub, map_sub]
    have h2 : PowerSeries.coeff i (gS * (Hs * ΔS)) = PowerSeries.coeff i (ΔS * (Hs * gS)) := by
      ring_nf
    rw [h2]; ring
  have hlow : ∀ i < L + d, PowerSeries.coeff i Y = 0 := by
    intro i hi
    rw [hYi i hi.le, coeff_mul_tail_lt L d i hi ΔS hΔ, mul_zero]
  rw [PowerSeries.coeff_mul, Finset.sum_eq_single (0, L + d)]
  · rw [hYi _ le_rfl, coeff_mul_tail L d ΔS hΔ, PowerSeries.coeff_zero_eq_constantCoeff_apply]
    ring
  · rintro ⟨i, j⟩ hij hne
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hij
    have : j < L + d := by
      by_contra hj
      apply hne
      simp only [Prod.mk.injEq]; omega
    rw [hlow j this, mul_zero]
  · intro h'; exact absurd (by simp) h'

theorem trunc_C_mul {F : Type*} [CommRing F] (M : ℕ) (c : F) (f : PowerSeries F) :
    (PowerSeries.trunc M (PowerSeries.C c * f) : PowerSeries F) =
      PowerSeries.C c * (PowerSeries.trunc M f : PowerSeries F) := by
  ext i
  rw [Polynomial.coeff_coe, PowerSeries.coeff_trunc, PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul,
    Polynomial.coeff_coe, PowerSeries.coeff_trunc]
  split_ifs <;> simp

theorem trunc_succ_eq {F : Type*} [CommRing F] (L : ℕ) (f : PowerSeries F) :
    (PowerSeries.trunc (L + 1) f : PowerSeries F) =
      (PowerSeries.trunc L f : PowerSeries F) + PowerSeries.C (PowerSeries.coeff L f) *
        PowerSeries.X ^ L := by
  rw [PowerSeries.trunc_succ]
  push_cast
  rw [PowerSeries.monomial_eq_mk]
  congr 1
  ext i
  simp [PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow, PowerSeries.coeff_monomial, eq_comm]

theorem jet_identity (M a L p : ℕ) (hMaL : a + L + 1 = M)
    (G C g : CohField[X]) (k : CohField) (hk : k ≠ 0) (hG0 : G.coeff 0 = 1) (hC0 : C.coeff 0 = 1)
    (hG : dS (M - 1) (G : PowerSeries CohField) =
      ((-(Polynomial.C k⁻¹ * Polynomial.X ^ a * g) : CohField[X]) : PowerSeries CohField))
    (hC : dS (M - 1) (C : PowerSeries CohField) =
      ((-(Polynomial.C k⁻¹ * Polynomial.X ^ a * g) : CohField[X]) : PowerSeries CohField))
    (hkdef : PowerSeries.coeff L (letterSeries * (g : PowerSeries CohField)) = k)
    (r ψ : PowerSeries CohField) (hψ : dS (M - 1) r = PowerSeries.X ^ (M - 1) * ψ) :
    dS (M - 1)
      (((clippedOp M G C (PowerSeries.X * letterSeries ^ p) : CohField[X]) :
          PowerSeries CohField) +
        PowerSeries.X * ((clippedOp M G C letterSeries : CohField[X]) : PowerSeries CohField) * r)
      = PowerSeries.X ^ (a + 1) *
        ((PowerSeries.C (-k⁻¹) * ((g : PowerSeries CohField) *
            ((PowerSeries.trunc (M - 1) (letterSeries ^ p *
              ((C - G : CohField[X]) : PowerSeries CohField)) : CohField[X]) :
              PowerSeries CohField)) +
          PowerSeries.C k⁻¹ * (((C - G : CohField[X]) : PowerSeries CohField) *
            ((PowerSeries.trunc L (letterSeries ^ p * (g : PowerSeries CohField)) :
              CohField[X]) : PowerSeries CohField))) +
        r * (PowerSeries.C (-k⁻¹) * ((g : PowerSeries CohField) *
            ((PowerSeries.trunc M (letterSeries * ((C - G : CohField[X]) : PowerSeries CohField)) :
              CohField[X]) : PowerSeries CohField)) +
          PowerSeries.C k⁻¹ * (((C - G : CohField[X]) : PowerSeries CohField) *
            ((PowerSeries.trunc L (letterSeries * (g : PowerSeries CohField)) :
              CohField[X]) : PowerSeries CohField)))) +
      PowerSeries.X * ((clippedOp M G C letterSeries : CohField[X]) : PowerSeries CohField) *
        (PowerSeries.X ^ (M - 1) * ψ) := by
  have hMm : M - 1 + 1 = M := by omega
  have hv : (((-(Polynomial.C k⁻¹ * Polynomial.X ^ a * g) : CohField[X])) :
      PowerSeries CohField) = -(PowerSeries.C k⁻¹ * PowerSeries.X ^ a * (g : PowerSeries CohField)) := by
    simp [Polynomial.coe_mul, Polynomial.coe_C, Polynomial.coe_pow, Polynomial.coe_X]
  rw [hv] at hG hC
  have hT1 : clippedOp M G C (dS (M - 1) (PowerSeries.X * letterSeries ^ p)) = 0 := by
    rw [dS_xhp, hMm]
    unfold clippedOp
    have e1 : ∀ (X' : PowerSeries CohField), PowerSeries.X ^ M * (PowerSeries.C (p : CohField) *
        letterSeries ^ (p - 1)) * X' = PowerSeries.X ^ M * (PowerSeries.C (p : CohField) *
        letterSeries ^ (p - 1) * X') := fun X' => by ring
    rw [e1, e1, trunc_X_pow_mul_self, trunc_X_pow_mul_self]; simp
  rw [dS_add, dS_clippedOp_matched _ _ _ _ _ _ hG hC, hT1, dS_mul, dS_mul, dS_X, zero_mul, zero_add,
    dS_clippedOp_matched _ _ _ _ _ _ hG hC, hψ,
    show dS (M - 1) letterSeries = _ from dS_mk_letters _,
    clippedOp_X_pow_pred M (by omega) G C hC0 hG0]
  set gS : PowerSeries CohField := (g : PowerSeries CohField) with hgS
  set ΔS : PowerSeries CohField := ((C - G : CohField[X]) : PowerSeries CohField) with hΔS
  have hLa : M - (a + 1) = L := by omega
  have hMa : M - a = L + 1 := by omega
  have t1 : (PowerSeries.trunc M (PowerSeries.X * letterSeries ^ p * ΔS) : PowerSeries CohField) =
      PowerSeries.X * (PowerSeries.trunc (M - 1) (letterSeries ^ p * ΔS) : PowerSeries CohField) := by
    have : PowerSeries.X * letterSeries ^ p * ΔS = PowerSeries.X ^ 1 * (letterSeries ^ p * ΔS) := by
      ring
    rw [this, trunc_X_pow_mul_shift M 1 (by omega)]; simp
  have t2 : (PowerSeries.trunc M (PowerSeries.X * letterSeries ^ p *
      -(PowerSeries.C k⁻¹ * PowerSeries.X ^ a * gS)) : PowerSeries CohField) =
      PowerSeries.X ^ (a + 1) * (PowerSeries.C (-k⁻¹) *
        (PowerSeries.trunc L (letterSeries ^ p * gS) : PowerSeries CohField)) := by
    have : PowerSeries.X * letterSeries ^ p * -(PowerSeries.C k⁻¹ * PowerSeries.X ^ a * gS) =
        PowerSeries.X ^ (a + 1) * (PowerSeries.C (-k⁻¹) * (letterSeries ^ p * gS)) := by
      rw [map_neg]; ring
    rw [this, trunc_X_pow_mul_shift M (a + 1) (by omega), hLa, trunc_C_mul]
  have t3 : (PowerSeries.trunc M (letterSeries * -(PowerSeries.C k⁻¹ * PowerSeries.X ^ a * gS)) :
      PowerSeries CohField) = PowerSeries.X ^ a * (PowerSeries.C (-k⁻¹) *
        ((PowerSeries.trunc L (letterSeries * gS) : PowerSeries CohField) +
          PowerSeries.C k * PowerSeries.X ^ L)) := by
    have : letterSeries * -(PowerSeries.C k⁻¹ * PowerSeries.X ^ a * gS) =
        PowerSeries.X ^ a * (PowerSeries.C (-k⁻¹) * (letterSeries * gS)) := by
      rw [map_neg]; ring
    rw [this, trunc_X_pow_mul_shift M a (by omega), hMa, trunc_C_mul, trunc_succ_eq, hkdef]
  rw [t1, t2, t3]
  have hGC : (((G - C) * Polynomial.X ^ (M - 1) : CohField[X]) : PowerSeries CohField) =
      -(ΔS * PowerSeries.X ^ (M - 1)) := by
    rw [hΔS]
    simp only [Polynomial.coe_mul, Polynomial.coe_sub, Polynomial.coe_pow, Polynomial.coe_X]
    ring
  have hcc : PowerSeries.C k⁻¹ * PowerSeries.C k = (1 : PowerSeries CohField) := by
    rw [← map_mul, inv_mul_cancel₀ hk, map_one]
  have hX : (PowerSeries.X : PowerSeries CohField) ^ (M - 1) =
      PowerSeries.X ^ a * PowerSeries.X ^ L := by rw [← pow_add]; congr 1; omega
  have hX2 : (PowerSeries.X : PowerSeries CohField) ^ (a + 1) * PowerSeries.X ^ L =
      PowerSeries.X ^ (M - 1) * PowerSeries.X := by rw [hX]; ring
  set Dfct : PowerSeries CohField := ((clippedOp M G C letterSeries : CohField[X]) :
    PowerSeries CohField) with hDfct
  have key : (-(PowerSeries.C k⁻¹ * PowerSeries.X ^ a * gS) *
        (PowerSeries.X * ((PowerSeries.trunc (M - 1)) (letterSeries ^ p * ΔS) : PowerSeries CohField)) -
      ΔS * (PowerSeries.X ^ (a + 1) * (PowerSeries.C (-k⁻¹) *
        ((PowerSeries.trunc L) (letterSeries ^ p * gS) : PowerSeries CohField))) +
      ((0 : CohField[X]) : PowerSeries CohField) +
      (PowerSeries.X * (-(PowerSeries.C k⁻¹ * PowerSeries.X ^ a * gS) *
          ((PowerSeries.trunc M) (letterSeries * ΔS) : PowerSeries CohField) -
        ΔS * (PowerSeries.X ^ a * (PowerSeries.C (-k⁻¹) *
          (((PowerSeries.trunc L) (letterSeries * gS) : PowerSeries CohField) +
            PowerSeries.C k * PowerSeries.X ^ L))) +
        (((G - C) * Polynomial.X ^ (M - 1) : CohField[X]) : PowerSeries CohField)) * r +
      PowerSeries.X * Dfct * (PowerSeries.X ^ (M - 1) * ψ))) =
      PowerSeries.X ^ (a + 1) *
        ((PowerSeries.C (-k⁻¹) * (gS * ((PowerSeries.trunc (M - 1) (letterSeries ^ p * ΔS) :
            CohField[X]) : PowerSeries CohField)) +
          PowerSeries.C k⁻¹ * (ΔS * ((PowerSeries.trunc L (letterSeries ^ p * gS) :
            CohField[X]) : PowerSeries CohField))) +
        r * (PowerSeries.C (-k⁻¹) * (gS * ((PowerSeries.trunc M (letterSeries * ΔS) :
            CohField[X]) : PowerSeries CohField)) +
          PowerSeries.C k⁻¹ * (ΔS * ((PowerSeries.trunc L (letterSeries * gS) :
            CohField[X]) : PowerSeries CohField)))) +
      PowerSeries.X * Dfct * (PowerSeries.X ^ (M - 1) * ψ) := by
    rw [hGC, map_neg]
    simp only [Polynomial.coe_zero]
    linear_combination (PowerSeries.X ^ (a + 1 + L) * r * ΔS) * hcc +
      (-(PowerSeries.X * r * ΔS)) * hX
  exact key

theorem first_jet (M a L d p : ℕ) (hMaL : a + L + 1 = M) (hd : d + 2 ≤ a)
    (G C g : CohField[X]) (k : CohField) (hk : k ≠ 0) (hG0 : G.coeff 0 = 1) (hC0 : C.coeff 0 = 1)
    (hG : dS (M - 1) (G : PowerSeries CohField) =
      ((-(Polynomial.C k⁻¹ * Polynomial.X ^ a * g) : CohField[X]) : PowerSeries CohField))
    (hC : dS (M - 1) (C : PowerSeries CohField) =
      ((-(Polynomial.C k⁻¹ * Polynomial.X ^ a * g) : CohField[X]) : PowerSeries CohField))
    (hΔ : ∀ i < d, (C - G).coeff i = 0)
    (hkdef : PowerSeries.coeff L (letterSeries * (g : PowerSeries CohField)) = k)
    (hdef : ∀ k ≤ M, (clippedOp M G C letterSeries).coeff k = 0)
    (r ψ : PowerSeries CohField) (hψ : dS (M - 1) r = PowerSeries.X ^ (M - 1) * ψ) :
    PowerSeries.coeff (M + d) (dS (M - 1)
      (((clippedOp M G C (PowerSeries.X * letterSeries ^ p) : CohField[X]) :
          PowerSeries CohField) +
        PowerSeries.X * ((clippedOp M G C letterSeries : CohField[X]) : PowerSeries CohField) * r))
      = -((C - G).coeff d * (PowerSeries.coeff L (letterSeries ^ p * (g : PowerSeries CohField)) / k
          + PowerSeries.constantCoeff r)) := by
  have hMm : M - 1 + 1 = M := by omega
  have hv : (((-(Polynomial.C k⁻¹ * Polynomial.X ^ a * g) : CohField[X])) :
      PowerSeries CohField) = -(PowerSeries.C k⁻¹ * PowerSeries.X ^ a * (g : PowerSeries CohField)) := by
    simp [Polynomial.coe_mul, Polynomial.coe_C, Polynomial.coe_pow, Polynomial.coe_X]
  rw [hv] at hG hC
  have hT1 : clippedOp M G C (dS (M - 1) (PowerSeries.X * letterSeries ^ p)) = 0 := by
    rw [dS_xhp, hMm]
    unfold clippedOp
    have e1 : ∀ (X' : PowerSeries CohField), PowerSeries.X ^ M * (PowerSeries.C (p : CohField) *
        letterSeries ^ (p - 1)) * X' = PowerSeries.X ^ M * (PowerSeries.C (p : CohField) *
        letterSeries ^ (p - 1) * X') := fun X' => by ring
    rw [e1, e1, trunc_X_pow_mul_self, trunc_X_pow_mul_self]; simp
  rw [dS_add, dS_clippedOp_matched _ _ _ _ _ _ hG hC, hT1, dS_mul, dS_mul, dS_X, zero_mul, zero_add,
    dS_clippedOp_matched _ _ _ _ _ _ hG hC, hψ,
    show dS (M - 1) letterSeries = _ from dS_mk_letters _,
    clippedOp_X_pow_pred M (by omega) G C hC0 hG0]
  set gS : PowerSeries CohField := (g : PowerSeries CohField) with hgS
  set ΔS : PowerSeries CohField := ((C - G : CohField[X]) : PowerSeries CohField) with hΔS
  have hΔ' : ∀ i < d, PowerSeries.coeff i ΔS = 0 := fun i hi => by
    rw [hΔS, Polynomial.coeff_coe]; exact hΔ i hi
  have hLa : M - (a + 1) = L := by omega
  have hMa : M - a = L + 1 := by omega
  have t1 : (PowerSeries.trunc M (PowerSeries.X * letterSeries ^ p * ΔS) : PowerSeries CohField) =
      PowerSeries.X * (PowerSeries.trunc (M - 1) (letterSeries ^ p * ΔS) : PowerSeries CohField) := by
    have : PowerSeries.X * letterSeries ^ p * ΔS = PowerSeries.X ^ 1 * (letterSeries ^ p * ΔS) := by
      ring
    rw [this, trunc_X_pow_mul_shift M 1 (by omega)]; simp
  have t2 : (PowerSeries.trunc M (PowerSeries.X * letterSeries ^ p *
      -(PowerSeries.C k⁻¹ * PowerSeries.X ^ a * gS)) : PowerSeries CohField) =
      PowerSeries.X ^ (a + 1) * (PowerSeries.C (-k⁻¹) *
        (PowerSeries.trunc L (letterSeries ^ p * gS) : PowerSeries CohField)) := by
    have : PowerSeries.X * letterSeries ^ p * -(PowerSeries.C k⁻¹ * PowerSeries.X ^ a * gS) =
        PowerSeries.X ^ (a + 1) * (PowerSeries.C (-k⁻¹) * (letterSeries ^ p * gS)) := by
      rw [map_neg]; ring
    rw [this, trunc_X_pow_mul_shift M (a + 1) (by omega), hLa, trunc_C_mul]
  have t3 : (PowerSeries.trunc M (letterSeries * -(PowerSeries.C k⁻¹ * PowerSeries.X ^ a * gS)) :
      PowerSeries CohField) = PowerSeries.X ^ a * (PowerSeries.C (-k⁻¹) *
        ((PowerSeries.trunc L (letterSeries * gS) : PowerSeries CohField) +
          PowerSeries.C k * PowerSeries.X ^ L)) := by
    have : letterSeries * -(PowerSeries.C k⁻¹ * PowerSeries.X ^ a * gS) =
        PowerSeries.X ^ a * (PowerSeries.C (-k⁻¹) * (letterSeries * gS)) := by
      rw [map_neg]; ring
    rw [this, trunc_X_pow_mul_shift M a (by omega), hMa, trunc_C_mul, trunc_succ_eq, hkdef]
  rw [t1, t2, t3]
  have hGC : (((G - C) * Polynomial.X ^ (M - 1) : CohField[X]) : PowerSeries CohField) =
      -(ΔS * PowerSeries.X ^ (M - 1)) := by
    rw [hΔS]
    simp only [Polynomial.coe_mul, Polynomial.coe_sub, Polynomial.coe_pow, Polynomial.coe_X]
    ring
  have hcc : PowerSeries.C k⁻¹ * PowerSeries.C k = (1 : PowerSeries CohField) := by
    rw [← map_mul, inv_mul_cancel₀ hk, map_one]
  have hX : (PowerSeries.X : PowerSeries CohField) ^ (M - 1) =
      PowerSeries.X ^ a * PowerSeries.X ^ L := by rw [← pow_add]; congr 1; omega
  have hX2 : (PowerSeries.X : PowerSeries CohField) ^ (a + 1) * PowerSeries.X ^ L =
      PowerSeries.X ^ (M - 1) * PowerSeries.X := by rw [hX]; ring
  set Dfct : PowerSeries CohField := ((clippedOp M G C letterSeries : CohField[X]) :
    PowerSeries CohField) with hDfct
  have key : (-(PowerSeries.C k⁻¹ * PowerSeries.X ^ a * gS) *
        (PowerSeries.X * ((PowerSeries.trunc (M - 1)) (letterSeries ^ p * ΔS) : PowerSeries CohField)) -
      ΔS * (PowerSeries.X ^ (a + 1) * (PowerSeries.C (-k⁻¹) *
        ((PowerSeries.trunc L) (letterSeries ^ p * gS) : PowerSeries CohField))) +
      ((0 : CohField[X]) : PowerSeries CohField) +
      (PowerSeries.X * (-(PowerSeries.C k⁻¹ * PowerSeries.X ^ a * gS) *
          ((PowerSeries.trunc M) (letterSeries * ΔS) : PowerSeries CohField) -
        ΔS * (PowerSeries.X ^ a * (PowerSeries.C (-k⁻¹) *
          (((PowerSeries.trunc L) (letterSeries * gS) : PowerSeries CohField) +
            PowerSeries.C k * PowerSeries.X ^ L))) +
        (((G - C) * Polynomial.X ^ (M - 1) : CohField[X]) : PowerSeries CohField)) * r +
      PowerSeries.X * Dfct * (PowerSeries.X ^ (M - 1) * ψ))) =
      PowerSeries.X ^ (a + 1) *
        ((PowerSeries.C (-k⁻¹) * (gS * ((PowerSeries.trunc (M - 1) (letterSeries ^ p * ΔS) :
            CohField[X]) : PowerSeries CohField)) +
          PowerSeries.C k⁻¹ * (ΔS * ((PowerSeries.trunc L (letterSeries ^ p * gS) :
            CohField[X]) : PowerSeries CohField))) +
        r * (PowerSeries.C (-k⁻¹) * (gS * ((PowerSeries.trunc M (letterSeries * ΔS) :
            CohField[X]) : PowerSeries CohField)) +
          PowerSeries.C k⁻¹ * (ΔS * ((PowerSeries.trunc L (letterSeries * gS) :
            CohField[X]) : PowerSeries CohField)))) +
      PowerSeries.X * Dfct * (PowerSeries.X ^ (M - 1) * ψ) := by
    rw [hGC, map_neg]
    simp only [Polynomial.coe_zero]
    linear_combination (PowerSeries.X ^ (a + 1 + L) * r * ΔS) * hcc +
      (-(PowerSeries.X * r * ΔS)) * hX
  rw [key, map_add, PowerSeries.coeff_X_pow_mul', if_pos (by omega),
    show M + d - (a + 1) = L + d by omega]
  have hD0 : PowerSeries.coeff (M + d) (PowerSeries.X * Dfct * (PowerSeries.X ^ (M - 1) * ψ)) = 0 := by
    have : PowerSeries.X * Dfct * (PowerSeries.X ^ (M - 1) * ψ) =
        PowerSeries.X ^ M * (Dfct * ψ) := by
      conv_rhs => rw [← hMm, pow_succ]
      ring
    rw [this, PowerSeries.coeff_X_pow_mul', if_pos (by omega), Nat.add_sub_cancel_left]
    exact coeff_defect_mul_eq_zero _ _ M d hdef (by omega)
  have hH : PowerSeries.coeff L (letterSeries * gS) = k := hkdef
  rw [hD0, add_zero, map_add, jetA (M - 1) L d (by omega) k gS ΔS (letterSeries ^ p) hΔ',
    jetB M L d (by omega) k gS ΔS letterSeries r hΔ', hH]
  have hΔd : PowerSeries.coeff d ΔS = (C - G).coeff d := by rw [hΔS, Polynomial.coeff_coe]
  rw [hΔd]
  field_simp
  ring

end SkewCoframeRigidity.Coframe
