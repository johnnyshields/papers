/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCoframeRigidity.Stationary.TopMatching

/-!
# Maximal-row incidence

Formalizes the first step of the proof of `shields-2026-skew-coframe-rigidity.tex`,
`sc:positive-power` («we first earn the maximal-row incidence»): when no proper row sits at
`M - 1` the complete coframe does not involve the letter `H_{M-1}`, and the first endpoint
equation differentiates to a nonzero ratio when exactly one diagram has such a row.
-/

namespace SkewCoframeRigidity.Coframe

open SkewCofactorIndependence Polynomial
open scoped Polynomial Matrix

variable {n : ℕ}

theorem rowPos_ne_top_of_not {D : BetaDiagram (n + 1)} (hn : 0 < n) (ht : ¬ TopRow D hn)
    (i : Fin n) : rowPos D i ≠ span D - 1 := by
  intro h
  apply ht
  have h0 : rowPos D ⟨0, hn⟩ < span D := rowPos_lt_span D _
  have h1 : rowPos D i ≤ rowPos D ⟨0, hn⟩ :=
    (rowPos_strictAnti D).antitone (Fin.le_iff_val_le_val.2 (Nat.zero_le _))
  unfold TopRow; omega

/-- With no row at `M - 1` the coframe does not involve `H_{M-1}`. -/
theorem dS_coframe_eq_zero {D : BetaDiagram (n + 1)} (hD : D.Connected) (hn : 0 < n)
    (ht : ¬ TopRow D hn) : dS (span D - 1) (coframe D : PowerSeries CohField) = 0 := by
  have hinv : IsUnit (properMatrixOf cohLetters D).det :=
    (properDet_cohLetters_ne_zero hD).isUnit
  have h1 := properMatrix_mulVec_dvec hD
  have h2 : (fun j => dRaw (span D - 1) (coframeVecOf cohLetters D j)) = 0 := by
    have : (fun i : Fin n => -(if rowPos D i = span D - 1 then (1 : CohField) else 0)) = 0 := by
      ext i; simp [rowPos_ne_top_of_not hn ht i]
    rw [this] at h1
    have h3 := congrArg ((properMatrixOf cohLetters D)⁻¹ *ᵥ ·) h1
    simpa only [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hinv, Matrix.one_mulVec,
      Matrix.mulVec_zero] using h3
  have h2' : ∀ j, dRaw (span D - 1) (coframeVecOf cohLetters D j) = 0 := fun j => congrFun h2 j
  rw [dS_coframe]
  simp [h2']

theorem natCast_ne_zero_field (p : ℕ) (hp : 1 ≤ p) : (p : CohField) ≠ 0 := by
  exact_mod_cast (by omega : p ≠ 0)

theorem ratio_ne_zero {p : ℕ} (c : CompData p) (hp : 2 ≤ p) : c.ratio ≠ 0 := by
  have hθ : cohLetters 0 ≠ 0 := cohLetters_zero_ne_zero
  have hpn := natCast_ne_zero_field p (by omega)
  rcases Nat.lt_or_ge c.L 2 with hl | hl
  · have : c.L = 0 ∨ c.L = 1 := by omega
    rcases this with h | h
    · rw [ratio_unit c h (by omega)]; exact pow_ne_zero _ hθ
    · rw [ratio_cell c h (by omega)]; exact mul_ne_zero hpn (pow_ne_zero _ hθ)
  · obtain ⟨k₀, α, hk₀, hα, hα0, hk, hr⟩ := ratio_big c hl hp
    intro h0
    rw [hr] at h0
    have hkne := c.hk
    have e : (p * cohLetters 0 ^ (p - 1)) * cohLetters c.L +
        (p * cohLetters 0 ^ (p - 1) * k₀ + α) = 0 := by
      have : p * cohLetters 0 ^ (p - 1) * c.k + α = 0 := by
        field_simp at h0; linear_combination h0
      rw [hk] at this; linear_combination this
    have hθF : cohLetters 0 ∈ lowerField c.L := letter_mem_lowerField (by omega)
    have hu : (p : CohField) * cohLetters 0 ^ (p - 1) ∈ lowerField c.L :=
      (lowerField _).mul_mem ((lowerField _).natCast_mem p) (pow_mem hθF _)
    obtain ⟨h1, -⟩ := eq_zero_of_mul_add_eq_zero (F := (lowerField c.L).toSubfield)
      (letter_notMem_lowerField c.L) hu
      ((lowerField _).add_mem ((lowerField _).mul_mem hu hk₀) hα) e
    exact mul_ne_zero hpn (pow_ne_zero _ hθ) h1

/-- The derivative of the first endpoint expression, for any two coframes. -/
theorem dRaw_endpoint_zero (D E : BetaDiagram (n + 1)) (p : ℕ) :
    dRaw (span D - 1) (PowerSeries.coeff (span D - 1)
        (letterSeries ^ p * ((coframe E - coframe D : CohField[X]) : PowerSeries CohField))) =
      PowerSeries.coeff (span D - 1) (letterSeries ^ p *
        dS (span D - 1) (coframe E : PowerSeries CohField)) -
      PowerSeries.coeff (span D - 1) (letterSeries ^ p *
        dS (span D - 1) (coframe D : PowerSeries CohField)) := by
  have hLs : dS (span D - 1) letterSeries = PowerSeries.X ^ (span D - 1) := dS_mk_letters _
  rw [← coeff_dS, dS_mul, dS_pow', hLs, map_add]
  have e1 : PowerSeries.coeff (span D - 1) (PowerSeries.C (p : CohField) *
      (letterSeries ^ (p - 1) * PowerSeries.X ^ (span D - 1)) *
      ((coframe E - coframe D : CohField[X]) : PowerSeries CohField)) = 0 := by
    have : PowerSeries.C (p : CohField) *
        (letterSeries ^ (p - 1) * PowerSeries.X ^ (span D - 1)) *
        ((coframe E - coframe D : CohField[X]) : PowerSeries CohField) =
        PowerSeries.C (p : CohField) * (PowerSeries.X ^ (span D - 1) * (letterSeries ^ (p - 1) *
          ((coframe E - coframe D : CohField[X]) : PowerSeries CohField))) := by ring
    rw [this, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, map_mul, delta_zero E D, mul_zero, mul_zero]
  rw [e1, zero_add, Polynomial.coe_sub, dS_sub, mul_sub, map_sub]

theorem mixed_absurd {D E : BetaDiagram (n + 1)} (hE : E.Connected) (hn : 0 < n)
    (hD' : dS (span D - 1) (coframe D : PowerSeries CohField) = 0)
    (hs : span D = span E) (htE : TopRow E hn) {p : ℕ} (hp : 2 ≤ p)
    (h0 : PowerSeries.coeff (span D - 1)
      (letterSeries ^ p * ((coframe E - coframe D : CohField[X]) : PowerSeries CohField)) = 0) :
    False := by
  obtain ⟨sE⟩ := topSide_exists hE hn htE p
  have h := congrArg (dRaw (span D - 1)) h0
  rw [dRaw_zero, dRaw_endpoint_zero, hD', mul_zero, map_zero, sub_zero, hs] at h
  rw [coeff_pow_mul_dS sE] at h
  exact ratio_ne_zero sE.c hp (neg_eq_zero.1 h)

theorem mixed_absurd' {D E : BetaDiagram (n + 1)} (hD : D.Connected) (hn : 0 < n)
    (hE' : dS (span E - 1) (coframe E : PowerSeries CohField) = 0)
    (hs : span D = span E) (htD : TopRow D hn) {p : ℕ} (hp : 2 ≤ p)
    (h0 : PowerSeries.coeff (span D - 1)
      (letterSeries ^ p * ((coframe E - coframe D : CohField[X]) : PowerSeries CohField)) = 0) :
    False := by
  obtain ⟨sD⟩ := topSide_exists hD hn htD p
  have h := congrArg (dRaw (span D - 1)) h0
  rw [dRaw_zero, dRaw_endpoint_zero] at h
  rw [← hs] at hE'
  rw [hE', mul_zero, map_zero, zero_sub, coeff_pow_mul_dS sD] at h
  exact ratio_ne_zero sD.c hp (by linear_combination h)

end SkewCoframeRigidity.Coframe
