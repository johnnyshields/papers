/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCoframeRigidity.Stationary.IncidenceBoth
import SkewCoframeRigidity.Stationary.TopMatchingThm
import SkewCoframeRigidity.Stationary.MatchedDeriv
import SkewCoframeRigidity.Stationary.CellJet

/-!
# One-power stationary separation

Formalizes the pole calculation in `shields-2026-skew-coframe-rigidity.tex`,
`sc:positive-power`.
-/

namespace SkewCoframeRigidity.Coframe

open SkewCofactorIndependence Polynomial
open scoped Polynomial Matrix

variable {n : ℕ}

theorem aeval_theta_mem (L : ℕ) (hL : 1 ≤ L) (P : ℚ[X]) :
    Polynomial.aeval (cohLetters 0) P ∈ lowerField L := by
  have hx : cohLetters 0 ∈ lowerField L := letter_mem_lowerField (by omega)
  have h1 := Polynomial.aeval_mem_adjoin_singleton ℚ (cohLetters 0) (p := P)
  exact (Algebra.adjoin_le (S := (lowerField L).toSubalgebra)
    (by simpa using hx)) h1

theorem potential_const_mem (L : ℕ) (hL : 1 ≤ L) (P Q : ℚ[X]) :
    PowerSeries.constantCoeff (potential P Q) ∈ lowerField L := by
  unfold potential
  rw [map_mul, PowerSeries.constantCoeff_inv, constantCoeff_aeval_letterSeries,
    constantCoeff_aeval_letterSeries]
  exact (lowerField L).mul_mem (aeval_theta_mem L hL P)
    ((lowerField L).inv_mem (aeval_theta_mem L hL Q))

theorem ratio_not_mem {p : ℕ} (c : CompData p) (hp : 2 ≤ p) (hL : 2 ≤ c.L) :
    c.ratio ∉ lowerField c.L := by
  intro hmem
  obtain ⟨k₀, α, hk₀, hα, hα0, hk, hr⟩ := ratio_big c hL hp
  have hθ : cohLetters 0 ∈ lowerField c.L := letter_mem_lowerField (by omega)
  have hnat : ((p : ℕ) : CohField) ∈ lowerField c.L := (lowerField c.L).natCast_mem p
  have hr' : α / c.k ∈ lowerField c.L := by
    have : α / c.k = c.ratio - p * cohLetters 0 ^ (p - 1) := by rw [hr]; ring
    rw [this]
    exact (lowerField _).sub_mem hmem ((lowerField _).mul_mem hnat (pow_mem hθ _))
  have hkne := c.hk
  have h2 : (α / c.k) * cohLetters c.L + (α / c.k * k₀ - α) = 0 := by
    have e : α = α / c.k * c.k := by field_simp
    linear_combination (-1 : CohField) * e + (-(α / c.k)) * hk
  obtain ⟨h3, -⟩ := eq_zero_of_mul_add_eq_zero (F := (lowerField c.L).toSubfield)
    (letter_notMem_lowerField c.L) hr'
    ((lowerField _).sub_mem ((lowerField _).mul_mem hr' hk₀) hα) h2
  have : α = 0 := by
    have e : α = α / c.k * c.k := by field_simp
    rw [e, h3, zero_mul]
  exact hα0 this

theorem flags_agree {D E : BetaDiagram (n + 1)} {p : ℕ} {sD : TopSide D p} {sE : TopSide E p}
    (hm : Matched sD sE) (hg : sD.c.g = sE.c.g) :
    (∀ i, sD.a ≤ i → (i ∈ rowSet D ↔ i ∈ rowSet E)) ∧
      (∀ s, sD.a ≤ s → (s ∈ colSet D ↔ s ∈ colSet E)) := by
  obtain ⟨hc1, hr1⟩ := sD.hflags
  obtain ⟨hc2, hr2⟩ := sE.hflags
  refine ⟨fun i hi => ?_, fun s hs => ?_⟩
  · rw [hr1 i hi, hr2 i (hm.ha ▸ hi), hm.ha, hm.hL, hg]
  · rw [hc1 s hs, hc2 s (hm.ha ▸ hs), hm.ha, hg]

/-- The pole relation: the first pole jet of the derivative of the one-power equation. -/
theorem pole_relation {D E : BetaDiagram (n + 1)} (hD : D.Connected) (hE : E.Connected)
    (hn : 0 < n) (hs : span D = span E) (hM : 3 ≤ span D)
    (hcf : coframe D ≠ coframe E) (hDdeg : 0 < (coframe D).natDegree)
    (hcop : IsCoprime (coframe D) (coframe E)) (hq : topQuotient D = topQuotient E)
    (hd : ∀ k ≤ span D, (defect D E).coeff k = 0) {p : ℕ} (hp : 2 ≤ p) (P Q : ℚ[X])
    (hQ : Q ≠ 0)
    (heq : ∀ k < 2 * span D, PowerSeries.coeff k
      (((clippedOp (span D) (coframe D) (coframe E) (PowerSeries.X * letterSeries ^ p) :
          CohField[X]) : PowerSeries CohField) +
        PowerSeries.X * ((defect D E : CohField[X]) : PowerSeries CohField) * potential P Q) = 0) :
    ∃ (sD : TopSide D p) (sE : TopSide E p), Matched sD sE ∧ sD.c.g = sE.c.g ∧
      sD.c.ratio + PowerSeries.constantCoeff (potential P Q) = 0 := by
  obtain ⟨htD, htE⟩ := incidence_both hD hE hn hs hM hcf hDdeg hcop hd hp P Q hQ heq
  obtain ⟨h0, h1⟩ := endpoints_diagrams hs hM hd P Q heq
  obtain ⟨sD, sE, hm, hg, -, -⟩ := top_matching hD hE hn hs htD htE hp hq h0
    (by rw [h1, dRaw_zero])
  refine ⟨sD, sE, hm, hg, ?_⟩
  obtain ⟨hrow, hcol⟩ := flags_agree hm hg
  obtain ⟨hd1, hd2⟩ := top_support hD hE hs sD.a hrow hcol hcf
  set d := (coframe E - coframe D).natTrailingDegree with hdd
  have hdne : coframe E - coframe D ≠ 0 := sub_ne_zero.2 hcf.symm
  have hlead : (coframe E - coframe D).coeff d ≠ 0 := mt Polynomial.trailingCoeff_eq_zero.1 hdne
  obtain ⟨ψ, hψ⟩ := potential_divDeriv (span D - 1) P Q hQ
  have hMaL : sD.a + sD.c.L + 1 = span D := by have := sD.hsum; have := span_pos D; omega
  have hG := sD.hd
  have hC := sE.hd
  rw [← hs, ← hm.hk, ← hm.ha, ← hg] at hC
  have hjet := first_jet (span D) sD.a sD.c.L d p hMaL (by omega) (coframe D) (coframe E)
    sD.c.g sD.c.k sD.c.hk (coframe_coeff_zero D) (coframe_coeff_zero E) hG hC
    (fun i hi => Polynomial.coeff_eq_zero_of_lt_natTrailingDegree hi) sD.c.hkdef hd
    (potential P Q) ψ hψ
  have hz : PowerSeries.coeff (span D + d) (dS (span D - 1)
      (((clippedOp (span D) (coframe D) (coframe E) (PowerSeries.X * letterSeries ^ p) :
          CohField[X]) : PowerSeries CohField) +
        PowerSeries.X * ((defect D E : CohField[X]) : PowerSeries CohField) *
          potential P Q)) = 0 := by
    rw [coeff_dS, heq _ (by omega), dRaw_zero]
  have hdefE : defect D E = clippedOp (span D) (coframe D) (coframe E) letterSeries := rfl
  rw [hdefE, hjet] at hz
  have : (coframe E - coframe D).coeff d * (sD.c.ratio + PowerSeries.constantCoeff (potential P Q))
      = 0 := by
    have := neg_eq_zero.1 hz
    unfold CompData.ratio
    exact this
  rcases mul_eq_zero.1 this with h | h
  · exact absurd h hlead
  · exact h

/-- The cell case `L = 1` of the pole calculation: the second pole jet. -/
theorem cell_case {D E : BetaDiagram (n + 1)} (hD : D.Connected) (hE : E.Connected)
    (hn : 0 < n) (hs : span D = span E) (hM : 3 ≤ span D)
    (hcf : coframe D ≠ coframe E) (hDdeg : 0 < (coframe D).natDegree)
    (hcop : IsCoprime (coframe D) (coframe E)) (hq : topQuotient D = topQuotient E)
    (hd : ∀ k ≤ span D, (defect D E).coeff k = 0) {p : ℕ} (hp : 2 ≤ p) (P Q : ℚ[X])
    (hQ : Q ≠ 0)
    (heq : ∀ k < 2 * span D, PowerSeries.coeff k
      (((clippedOp (span D) (coframe D) (coframe E) (PowerSeries.X * letterSeries ^ p) :
          CohField[X]) : PowerSeries CohField) +
        PowerSeries.X * ((defect D E : CohField[X]) : PowerSeries CohField) * potential P Q) = 0)
    (sD : TopSide D p) (sE : TopSide E p) (hm : Matched sD sE) (hg : sD.c.g = sE.c.g)
    (hrel : sD.c.ratio + PowerSeries.constantCoeff (potential P Q) = 0)
    (hL : sD.c.L = 1) : False := by
  obtain ⟨hg1, hk1⟩ := cell_gk sD.c hL
  have hθ : cohLetters 0 ≠ 0 := cohLetters_zero_ne_zero
  have hpn := natCast_ne_zero_field p (by omega)
  -- the potential is `-p H^{p-1}`
  have hratio := ratio_cell sD.c hL (by omega)
  have hPQ : P = -(Polynomial.C (p : ℚ) * Polynomial.X ^ (p - 1)) * Q := by
    have h0 : Polynomial.aeval (cohLetters 0) (P + Polynomial.C (p : ℚ) *
        Polynomial.X ^ (p - 1) * Q) = 0 := by
      have hc := constantCoeff_aeval_letterSeries Q
      have hQ0 := aeval_theta_ne_zero hQ
      have e : PowerSeries.constantCoeff (potential P Q) =
          Polynomial.aeval (cohLetters 0) P * (Polynomial.aeval (cohLetters 0) Q)⁻¹ := by
        unfold potential
        rw [map_mul, PowerSeries.constantCoeff_inv, constantCoeff_aeval_letterSeries,
          constantCoeff_aeval_letterSeries]
      rw [e, hratio] at hrel
      simp only [map_add, map_mul, map_pow, Polynomial.aeval_C, Polynomial.aeval_X, map_natCast]
      field_simp at hrel
      linear_combination hrel
    have := aeval_theta_eq_zero h0
    linear_combination this
  have hr : potential P Q = -(PowerSeries.C (p : CohField) * letterSeries ^ (p - 1)) := by
    unfold potential
    rw [hPQ]
    have hQ0 : PowerSeries.constantCoeff (Polynomial.aeval letterSeries Q) ≠ 0 :=
      potential_const_ne Q hQ
    have hi := PowerSeries.mul_inv_cancel _ hQ0
    simp only [map_mul, map_neg, map_pow, map_natCast, Polynomial.aeval_C, Polynomial.aeval_X]
    have hC : PowerSeries.C (p : CohField) = (p : PowerSeries CohField) := map_natCast _ _
    linear_combination (-((p : PowerSeries CohField) * letterSeries ^ (p - 1))) * hi
  obtain ⟨htD, htE⟩ := incidence_both hD hE hn hs hM hcf hDdeg hcop hd hp P Q hQ heq
  obtain ⟨hrow, hcol⟩ := flags_agree hm hg
  obtain ⟨hd1, hd2⟩ := top_support hD hE hs sD.a hrow hcol hcf
  set d := (coframe E - coframe D).natTrailingDegree with hdd
  have hdne : coframe E - coframe D ≠ 0 := sub_ne_zero.2 hcf.symm
  have hlead : (coframe E - coframe D).coeff d ≠ 0 := mt Polynomial.trailingCoeff_eq_zero.1 hdne
  obtain ⟨ψ, hψ⟩ := potential_divDeriv (span D - 1) P Q hQ
  have hsum := sD.hsum
  have hMpos := span_pos D
  have hG := sD.hd
  have hC := sE.hd
  rw [← hs, ← hm.hk, ← hm.ha, ← hg] at hC
  rw [hg1] at hG hC
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 2 := ⟨p - 2, by omega⟩
  have hjet := cell_second_jet (span D) sD.a d q (by omega) (by omega) (coframe D) (coframe E)
    sD.c.k sD.c.hk (coframe_coeff_zero D) (coframe_coeff_zero E) hG hC
    (fun i hi => Polynomial.coeff_eq_zero_of_lt_natTrailingDegree hi)
    (by have := sD.c.hkdef; rw [hL, hg1] at this; exact this) hd
    (potential P Q) ψ hψ (by rw [hr]; push_cast; simp)
  have hz : PowerSeries.coeff (span D + d + 1) (dS (span D - 1)
      (((clippedOp (span D) (coframe D) (coframe E) (PowerSeries.X * letterSeries ^ (q + 2)) :
          CohField[X]) : PowerSeries CohField) +
        PowerSeries.X * ((defect D E : CohField[X]) : PowerSeries CohField) *
          potential P Q)) = 0 := by
    rw [coeff_dS, heq _ (by omega), dRaw_zero]
  have hdefE : defect D E = clippedOp (span D) (coframe D) (coframe E) letterSeries := rfl
  rw [hdefE, hjet] at hz
  have hch : (((q + 2).choose 2 : ℕ) : CohField) ≠ 0 := by
    have : 0 < (q + 2).choose 2 := Nat.choose_pos (by omega)
    exact_mod_cast this.ne'
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero hch (pow_ne_zero _ hθ)) sD.c.hk) hlead hz

end SkewCoframeRigidity.Coframe
