/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCoframeRigidity.Stationary.UnitCase.Embed
import SkewCoframeRigidity.Stationary.UnitCase.HatCoframe
import SkewCoframeRigidity.Stationary.UnitCase.Master
import SkewCoframeRigidity.Stationary.PowerEquation

/-!
# The coframes of a coequal pair over `CohField[ε]`

Formalizes the setting of the unit case of `sc:positive-power` in
`shields-2026-skew-coframe-rigidity.tex`: the coframes of two connected diagrams with presented
zero-free cores, multiplied by a common denominator regular at `ε = 0`, are polynomials over
`CohField[ε]` that agree with constant polynomials (a nonzero multiple of the core coframes) at
`ε = 0` to first order, satisfy the row equations and the support constraints, and satisfy the
one-power equation.
-/

namespace SkewCoframeRigidity.UnitCase

open SkewCofactorIndependence SkewCoframeRigidity SkewCoframeRigidity.Coframe
  SkewCoframeRigidity.UnitRestoration Polynomial

/-- A polynomial over `A = CohField[ε]` all of whose coefficients vanish at `ε = 0` is divisible by
`ε` coefficientwise. -/
theorem exists_eq_C_X_mul (R : Polynomial CohField[X]) (h : ∀ s, (R.coeff s).coeff 0 = 0) :
    ∃ a : Polynomial CohField[X], R = Polynomial.C Polynomial.X * a := by
  refine ⟨∑ s ∈ Finset.range (R.natDegree + 1),
    Polynomial.monomial s (Polynomial.divX (R.coeff s)), ?_⟩
  refine Polynomial.ext fun s => ?_
  have key := Polynomial.divX_mul_X_add (R.coeff s)
  rw [h s, map_zero, add_zero] at key
  rw [Polynomial.coeff_C_mul, Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_monomial]
  rw [Finset.sum_ite_eq']
  by_cases hs : s ∈ Finset.range (R.natDegree + 1)
  · rw [if_pos hs, mul_comm]
    exact key.symm
  · rw [if_neg hs, mul_zero]
    rw [Finset.mem_range, not_lt] at hs
    exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)

/-- The clipped operator commutes with ring homomorphisms. -/
theorem clippedOp_map_eq {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (M : ℕ)
    (G C : R[X]) (u : PowerSeries R) :
    (clippedOp M G C u).map f =
      clippedOp M (G.map f) (C.map f) (PowerSeries.map f u) := by
  have hc : ∀ H : R[X],
      PowerSeries.map f (H : PowerSeries R) = ((H.map f : S[X]) : PowerSeries S) :=
    fun H => Polynomial.polynomial_map_coe.symm
  unfold clippedOp
  simp only [Polynomial.map_sub, Polynomial.map_mul, ← PowerSeries.trunc_map, map_mul, hc]

/-- The clipped operator is quadratic in a common scalar factor of its two polynomials. -/
theorem clippedOp_C_mul_sq {R : Type*} [CommRing R] (M : ℕ) (c : R) (G C : R[X])
    (u : PowerSeries R) :
    clippedOp M (Polynomial.C c * G) (Polynomial.C c * C) u =
      Polynomial.C c ^ 2 * clippedOp M G C u := by
  unfold clippedOp
  have h1 : ∀ H : R[X], u * ((Polynomial.C c * H : R[X]) : PowerSeries R) =
      PowerSeries.C c * (u * (H : PowerSeries R)) := by
    intro H
    rw [Polynomial.coe_mul, Polynomial.coe_C]
    ring
  rw [h1, h1, PowerSeries.trunc_C_mul, PowerSeries.trunc_C_mul]
  ring

theorem pair_package {n m : ℕ} {D E : BetaDiagram (n + 1)} {CD CE : BetaDiagram (m + 1)}
    (PD : CoreData D CD) (PE : CoreData E CE) (hD : D.Connected) (hE : E.Connected)
    (hCD : CD.Connected) (hCE : CE.Connected) (hs : span D = span E)
    (hq : topQuotient D = topQuotient E) {p : ℕ} (hp : 1 ≤ p)
    (h : ∀ k < 2 * span D, PowerSeries.coeff k
      (((clippedOp (span D) (coframe D) (coframe E) (PowerSeries.X * letterSeries ^ p) :
          CohField[X]) : PowerSeries CohField) -
        PowerSeries.X * ((defect D E : CohField[X]) : PowerSeries CohField) *
          letterSeries ^ (p - 1)) = 0) :
    ∃ (β : CohField) (Gt Ct a b : Polynomial CohField[X]), β ≠ 0 ∧
      Gt = liftK (Polynomial.C β * coframe CD) + Polynomial.C Polynomial.X * a ∧
      Ct = liftK (Polynomial.C β * coframe CE) + Polynomial.C Polynomial.X * b ∧
      Gt.natDegree < span D ∧ Ct.natDegree < span D ∧
      (∀ i ∈ rowSet D, PowerSeries.coeff i (AH * (Gt : PowerSeries CohField[X])) = 0) ∧
      (∀ i ∈ rowSet E, PowerSeries.coeff i (AH * (Ct : PowerSeries CohField[X])) = 0) ∧
      (∀ s, s ≠ 0 → s ∉ colSet D → Gt.coeff s = 0) ∧
      (∀ s, s ≠ 0 → s ∉ colSet E → Ct.coeff s = 0) ∧
      PowerSeries.coeff (span D - 1) (AH ^ p * ((Ct - Gt : Polynomial CohField[X]) :
        PowerSeries CohField[X])) = 0 ∧
      (∀ k < 2 * span D, PowerSeries.coeff k
        (((clippedOp (span D) Gt Ct (PowerSeries.X * AH ^ p) : Polynomial CohField[X]) :
            PowerSeries CohField[X]) -
          PowerSeries.X * ((clippedOp (span D) Gt Ct AH : Polynomial CohField[X]) :
            PowerSeries CohField[X]) * AH ^ (p - 1)) = 0) ∧
      Gt.coeff 0 = Ct.coeff 0 := by
  obtain ⟨BD, ND, hBD, hND, hND0⟩ := hat_regular PD hCD
  obtain ⟨BE, NE, hBE, hNE, hNE0⟩ := hat_regular PE hCE
  set φ : CohField[X] →+* Eps := algebraMap CohField[X] Eps with hφdef
  have hφ : Function.Injective φ := IsFractionRing.injective CohField[X] Eps
  set c : Eps := φ BD * φ BE with hc
  set Gt : Polynomial CohField[X] := Polynomial.C BE * ND with hGt
  set Ct : Polynomial CohField[X] := Polynomial.C BD * NE with hCt
  have hGm : Gt.map φ = Polynomial.C c * hatCoframe D := by
    ext s
    rw [Polynomial.coeff_map, hGt, Polynomial.coeff_C_mul, map_mul, hND s,
      Polynomial.coeff_C_mul, hc]
    ring
  have hCm : Ct.map φ = Polynomial.C c * hatCoframe E := by
    ext s
    rw [Polynomial.coeff_map, hCt, Polynomial.coeff_C_mul, map_mul, hNE s,
      Polynomial.coeff_C_mul, hc]
    ring
  have hMpos : 0 < span D := span_pos D
  -- coefficients of the cores
  have hGc : ∀ s, (Gt.coeff s).coeff 0 =
      (BD.coeff 0 * BE.coeff 0) * (coframe CD).coeff s := by
    intro s
    rw [hGt, Polynomial.coeff_C_mul, Polynomial.mul_coeff_zero, hND0 s]
    ring
  have hCc : ∀ s, (Ct.coeff s).coeff 0 =
      (BD.coeff 0 * BE.coeff 0) * (coframe CE).coeff s := by
    intro s
    rw [hCt, Polynomial.coeff_C_mul, Polynomial.mul_coeff_zero, hNE0 s]
    ring
  have hβ : BD.coeff 0 * BE.coeff 0 ≠ 0 := mul_ne_zero hBD hBE
  have hdiv : ∀ (P : Polynomial CohField[X]) (g : CohField[X]),
      (∀ s, (P.coeff s).coeff 0 = (BD.coeff 0 * BE.coeff 0) * g.coeff s) →
      ∃ a : Polynomial CohField[X],
        P = liftK (Polynomial.C (BD.coeff 0 * BE.coeff 0) * g) +
          Polynomial.C Polynomial.X * a := by
    intro P g hP
    obtain ⟨a, ha⟩ := exists_eq_C_X_mul (P - liftK (Polynomial.C (BD.coeff 0 * BE.coeff 0) * g))
      (by
        intro s
        rw [Polynomial.coeff_sub, liftK, Polynomial.coeff_map, Polynomial.coeff_C_mul,
          Polynomial.coeff_sub, hP s, Polynomial.coeff_C_zero]
        simp)
    exact ⟨a, by rw [← ha]; ring⟩
  obtain ⟨a, ha⟩ := hdiv Gt (coframe CD) hGc
  obtain ⟨b, hb⟩ := hdiv Ct (coframe CE) hCc
  -- degree and support
  have hdeg : ∀ (P : Polynomial CohField[X]) (F : Eps[X]), P.map φ = Polynomial.C c * F →
      (∀ s, span D ≤ s → F.coeff s = 0) → P.natDegree < span D := by
    intro P F hP hF
    have : P.natDegree ≤ span D - 1 := by
      rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
      intro N hN
      apply hφ
      rw [← Polynomial.coeff_map, hP, Polynomial.coeff_C_mul, hF N (by omega), mul_zero,
        map_zero]
    omega
  have hsupp : ∀ (P : Polynomial CohField[X]) (F : Eps[X]), P.map φ = Polynomial.C c * F →
      ∀ s, F.coeff s = 0 → P.coeff s = 0 := by
    intro P F hP s hF
    apply hφ
    rw [← Polynomial.coeff_map, hP, Polynomial.coeff_C_mul, hF, mul_zero, map_zero]
  have hrow : ∀ (P : Polynomial CohField[X]) (F : Eps[X]), P.map φ = Polynomial.C c * F →
      ∀ i, PowerSeries.coeff i (epsH * (F : PowerSeries Eps)) = 0 →
        PowerSeries.coeff i (AH * (P : PowerSeries CohField[X])) = 0 := by
    intro P F hP i hF
    apply hφ
    rw [← PowerSeries.coeff_map, map_mul, ← Polynomial.polynomial_map_coe, hP, ← epsH_eq,
      Polynomial.coe_mul, Polynomial.coe_C, mul_left_comm, PowerSeries.coeff_C_mul, hF,
      mul_zero, map_zero]
  -- the power equation
  have hpow := hat_power hD hE hs hp h
  have hPE : ∀ k < 2 * span D, PowerSeries.coeff k
      (((clippedOp (span D) Gt Ct (PowerSeries.X * AH ^ p) : Polynomial CohField[X]) :
          PowerSeries CohField[X]) -
        PowerSeries.X * ((clippedOp (span D) Gt Ct AH : Polynomial CohField[X]) :
          PowerSeries CohField[X]) * AH ^ (p - 1)) = 0 := by
    intro k hk
    have hX : PowerSeries.map φ (PowerSeries.X * AH ^ p) = PowerSeries.X * epsH ^ p := by
      rw [map_mul, map_pow, PowerSeries.map_X, ← epsH_eq]
    have hY : PowerSeries.map φ (AH ^ (p - 1)) = epsH ^ (p - 1) := by
      rw [map_pow, ← epsH_eq]
    apply hφ
    rw [← PowerSeries.coeff_map, map_sub, map_mul, map_mul, ← Polynomial.polynomial_map_coe,
      ← Polynomial.polynomial_map_coe, clippedOp_map_eq, clippedOp_map_eq, hGm, hCm,
      clippedOp_C_mul_sq, clippedOp_C_mul_sq, hX, hY, PowerSeries.map_X, ← epsH_eq]
    have e : (((Polynomial.C c ^ 2 * clippedOp (span D) (hatCoframe D) (hatCoframe E)
        (PowerSeries.X * epsH ^ p) : Eps[X]) : PowerSeries Eps) -
        PowerSeries.X * ((Polynomial.C c ^ 2 * clippedOp (span D) (hatCoframe D) (hatCoframe E)
          epsH : Eps[X]) : PowerSeries Eps) * epsH ^ (p - 1)) =
        PowerSeries.C c ^ 2 * (((clippedOp (span D) (hatCoframe D) (hatCoframe E)
          (PowerSeries.X * epsH ^ p) : Eps[X]) : PowerSeries Eps) -
        PowerSeries.X * ((clippedOp (span D) (hatCoframe D) (hatCoframe E) epsH : Eps[X]) :
          PowerSeries Eps) * epsH ^ (p - 1)) := by
      rw [Polynomial.coe_mul, Polynomial.coe_mul, Polynomial.coe_pow, Polynomial.coe_C]
      ring
    rw [e, ← map_pow, PowerSeries.coeff_C_mul, hpow k hk, mul_zero, map_zero]
  have h00 : Gt.coeff 0 = Ct.coeff 0 := by
    apply hφ
    rw [← Polynomial.coeff_map, ← Polynomial.coeff_map, hGm, hCm, Polynomial.coeff_C_mul,
      Polynomial.coeff_C_mul, hat_coeff_zero, hat_coeff_zero]
  refine ⟨BD.coeff 0 * BE.coeff 0, Gt, Ct, a, b, hβ, ha, hb,
    hdeg Gt _ hGm fun s hs' => hat_degree D hs',
    hdeg Ct _ hCm fun s hs' => hat_degree E (hs ▸ hs'),
    fun i hi => hrow Gt _ hGm i (hat_rows PD hCD hi),
    fun i hi => hrow Ct _ hCm i (hat_rows PE hCE hi),
    fun s hs0 hc => hsupp Gt _ hGm s (hat_support D hs0 hc),
    fun s hs0 hc => hsupp Ct _ hCm s (hat_support E hs0 hc), ?_, hPE, h00⟩
  by_cases hM1 : span D = 1
  · have hEq : hatCoframe E = hatCoframe D := by
      refine Polynomial.ext fun s => ?_
      rcases Nat.eq_zero_or_pos s with rfl | hs0
      · rw [hat_coeff_zero, hat_coeff_zero]
      · rw [hat_degree D (by omega), hat_degree E (by omega)]
    have hCG : Ct = Gt :=
      Polynomial.map_injective φ hφ (by rw [hCm, hGm, hEq])
    simp [hCG]
  · have hM2 : 2 ≤ span D := by omega
    have hd := clippedOp_coeff_eq_zero (span D) (hatCoframe D) (hatCoframe E) epsH
      (hat_coeff_zero D) (hat_coeff_zero E) (hat_top hD hE hs hq)
    have hpow := hat_power hD hE hs hp h
    have e : ∀ A B r : PowerSeries Eps,
        A + PowerSeries.X * B * (-r) = A - PowerSeries.X * B * r := fun _ _ _ => by ring
    have hend := endpoints_of_powerEquation (span D) p hM2 (hatCoframe D) (hatCoframe E) epsH
      (hat_coeff_zero D) (hat_coeff_zero E) (-(epsH ^ (p - 1))) hd
      (by rw [e]; exact hpow _ (by omega)) (by rw [e]; exact hpow _ (by omega))
    have h0 := hend.1
    unfold endpointZero at h0
    apply hφ
    rw [← PowerSeries.coeff_map, map_mul, map_pow, ← Polynomial.polynomial_map_coe,
      Polynomial.map_sub, hGm, hCm, ← epsH_eq, ← mul_sub, Polynomial.coe_mul, Polynomial.coe_C,
      mul_left_comm, PowerSeries.coeff_C_mul, h0, mul_zero, map_zero]

end SkewCoframeRigidity.UnitCase
