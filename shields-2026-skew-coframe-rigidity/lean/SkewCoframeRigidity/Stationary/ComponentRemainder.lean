/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCoframeRigidity.Coframe.Atlas
import SkewCoframeRigidity.Coframe.Algebra
import SkewCoframeRigidity.Stationary.SeriesPower
import SkewCoframeRigidity.Stationary.LowerField

/-!
# The component remainder

Formalizes `shields-2026-skew-coframe-rigidity.tex`, `sc:component-remainder`.  For the
coframe `g` of a connected diagram of span `L`, `P = [Hg]_{<L}` and any integer `p ≥ 1`,
\[
  [H^p g]_L = p ϑ^{p-1} [Hg]_L + \alpha, \qquad \alpha = [P^p g^{1-p}]_L,
\]
where `α` involves only the letters of index below `L`.  This module proves the identity and
the independence of `α` from the top letter; the nonvanishing of `α` is in
`Stationary.ComponentNonzero`.
-/

namespace SkewCoframeRigidity.Coframe

open SkewCofactorIndependence Polynomial
open scoped Polynomial Matrix

variable {n : ℕ}

theorem coeff_zero_coframe (D : BetaDiagram (n + 1)) : (coframe D).coeff 0 = 1 := by
  unfold coframe coframeOf
  rw [Polynomial.coeff_add, Polynomial.coeff_one_zero, Polynomial.finsetSum_coeff]
  have : ∀ j ∈ Finset.univ, (C (coframeVecOf cohLetters D j) * X ^ colPos D j).coeff 0 = 0 := by
    intro j _
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg (colPos_pos D j).ne, mul_zero]
  rw [Finset.sum_eq_zero this, add_zero]

/-- A series is its truncation plus `z^L` times its tail. -/
theorem eq_trunc_add_X_pow_mul {F : Type*} [CommRing F] (L : ℕ) (W : PowerSeries F) :
    W = (PowerSeries.trunc L W : PowerSeries F) +
      PowerSeries.X ^ L * PowerSeries.mk (fun i => PowerSeries.coeff (L + i) W) := by
  ext m
  rw [map_add, Polynomial.coeff_coe, PowerSeries.coeff_trunc, PowerSeries.coeff_X_pow_mul']
  by_cases h : m < L
  · simp [h, not_le.mpr h]
  · simp only [h, if_false, zero_add, PowerSeries.coeff_mk, if_true, not_lt.mp h]
    rw [show L + (m - L) = m by omega]

/-- The identity `[H^p g]_L = p ϑ^{p-1} [Hg]_L + α`. -/
theorem coeff_pow_letterSeries_mul_coframe (D : BetaDiagram (n + 1)) (p : ℕ) (hp : 1 ≤ p) :
    PowerSeries.coeff (span D) (letterSeries ^ p * (coframe D : PowerSeries CohField)) =
      PowerSeries.coeff (span D)
          ((numerator D : PowerSeries CohField) ^ p *
            ((coframe D : PowerSeries CohField)⁻¹) ^ (p - 1)) +
        p * cohLetters 0 ^ (p - 1) * topQuotient D := by
  set g : PowerSeries CohField := (coframe D : PowerSeries CohField) with hg
  have hg0 : PowerSeries.constantCoeff g = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, hg, Polynomial.coeff_coe,
      coeff_zero_coframe]
  have hginv : g * g⁻¹ = 1 := PowerSeries.mul_inv_cancel _ (by rw [hg0]; exact one_ne_zero)
  have hL := span_pos D
  set W : PowerSeries CohField := letterSeries * g with hW
  have hWe := eq_trunc_add_X_pow_mul (span D) W
  have hnum : (numerator D : PowerSeries CohField) =
      (PowerSeries.trunc (span D) W : PowerSeries CohField) := rfl
  have hpow : letterSeries ^ p * g = W ^ p * (g⁻¹) ^ (p - 1) := by
    obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
    simp only [Nat.add_sub_cancel, hW]
    calc letterSeries ^ (q + 1) * g
        = letterSeries ^ (q + 1) * g * (g * g⁻¹) ^ q := by rw [hginv, one_pow, mul_one]
      _ = _ := by ring
  rw [hpow]
  have := coeff_add_X_pow_mul_pow (span D) hL
    (PowerSeries.trunc (span D) W : PowerSeries CohField)
    (PowerSeries.mk fun i => PowerSeries.coeff (span D + i) W) ((g⁻¹) ^ (p - 1)) p
  rw [← hWe, ← hnum] at this
  rw [this]
  congr 1
  have h0 : PowerSeries.constantCoeff (numerator D : PowerSeries CohField) = cohLetters 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe]
    simp only [numerator, numeratorOf, PowerSeries.coeff_trunc, if_pos hL,
      PowerSeries.coeff_zero_eq_constantCoeff, map_mul]
    rw [show PowerSeries.constantCoeff (coframeOf cohLetters D : PowerSeries CohField) = 1 from hg0,
      mul_one]
    simp [letterSeries, seriesOf, cohLetters]
  have hq : PowerSeries.constantCoeff ((g⁻¹) ^ (p - 1)) = 1 := by
    rw [map_pow, PowerSeries.constantCoeff_inv, hg0]; simp
  rw [h0, hq]
  simp only [topQuotient, topQuotientOf, hW, hg, seriesOf, letterSeries]
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_mk, add_zero, mul_one]
  rfl

section Independence

variable (F : IntermediateField ℚ CohField)

/-- Power series over the raw field with all coefficients in `F`. -/
noncomputable def seriesOverRange : Subring (PowerSeries CohField) :=
  (PowerSeries.map (algebraMap F CohField)).range

theorem mem_seriesOverRange_iff {φ : PowerSeries CohField} :
    φ ∈ seriesOverRange F ↔ ∀ m, PowerSeries.coeff m φ ∈ F := by
  constructor
  · rintro ⟨ψ, rfl⟩ m
    rw [PowerSeries.coeff_map]
    exact (PowerSeries.coeff m ψ).2
  · intro h
    refine ⟨PowerSeries.mk fun m => ⟨PowerSeries.coeff m φ, h m⟩, ?_⟩
    ext m
    simp [PowerSeries.coeff_map]

theorem inv_mem_seriesOverRange {φ : PowerSeries CohField} (h : φ ∈ seriesOverRange F)
    (h0 : PowerSeries.constantCoeff φ = 1) : φ⁻¹ ∈ seriesOverRange F := by
  obtain ⟨ψ, rfl⟩ := h
  have hψ : PowerSeries.constantCoeff ψ ≠ 0 := by
    intro h'
    have : PowerSeries.constantCoeff (PowerSeries.map (algebraMap F CohField) ψ) = 0 := by
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
        PowerSeries.coeff_zero_eq_constantCoeff_apply, h', map_zero]
    rw [h0] at this; exact one_ne_zero this
  have e : (PowerSeries.map (algebraMap F CohField) ψ)⁻¹ =
      PowerSeries.map (algebraMap F CohField) ψ⁻¹ := by
    have h1 := PowerSeries.mul_inv_cancel ψ hψ
    have h2 := PowerSeries.mul_inv_cancel (PowerSeries.map (algebraMap F CohField) ψ)
      (by rw [h0]; exact one_ne_zero)
    calc (PowerSeries.map (algebraMap F CohField) ψ)⁻¹
        = (PowerSeries.map (algebraMap F CohField) ψ)⁻¹ *
            (PowerSeries.map (algebraMap F CohField) (ψ * ψ⁻¹)) := by rw [h1, map_one, mul_one]
      _ = _ := by
        rw [map_mul, ← mul_assoc, mul_comm _ (PowerSeries.map _ ψ), h2, one_mul]
  rw [e]
  exact ⟨_, rfl⟩

theorem coframe_series_mem (D : BetaDiagram (n + 1)) (hF : ∀ k < span D, cohLetters k ∈ F) :
    (coframe D : PowerSeries CohField) ∈ seriesOverRange F := by
  rw [mem_seriesOverRange_iff]
  intro m
  rw [Polynomial.coeff_coe]
  exact coframe_coeff_mem D F hF m

theorem numerator_series_mem (D : BetaDiagram (n + 1)) (hF : ∀ k < span D, cohLetters k ∈ F) :
    (numerator D : PowerSeries CohField) ∈ seriesOverRange F := by
  rw [mem_seriesOverRange_iff]
  intro m
  rw [Polynomial.coeff_coe]
  exact numerator_coeff_mem D F hF m

/-- The remainder `α = [P^p g^{1-p}]_L` involves only the letters of lower index. -/
theorem remainder_mem (D : BetaDiagram (n + 1)) (p : ℕ) :
    PowerSeries.coeff (span D)
        ((numerator D : PowerSeries CohField) ^ p *
          ((coframe D : PowerSeries CohField)⁻¹) ^ (p - 1)) ∈ lowerField (span D) := by
  have hF : ∀ k < span D, cohLetters k ∈ lowerField (span D) := fun k hk => letter_mem_lowerField hk
  have hg0 : PowerSeries.constantCoeff (coframe D : PowerSeries CohField) = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe,
      coeff_zero_coframe]
  have := (seriesOverRange (lowerField (span D))).mul_mem
    ((seriesOverRange (lowerField (span D))).pow_mem (numerator_series_mem _ D hF) p)
    ((seriesOverRange (lowerField (span D))).pow_mem
      (inv_mem_seriesOverRange _ (coframe_series_mem _ D hF) hg0) (p - 1))
  exact (mem_seriesOverRange_iff _).1 this _

/-- The top quotient is the top letter plus a lower part. -/
theorem topQuotient_sub_mem (D : BetaDiagram (n + 1)) :
    topQuotient D - cohLetters (span D) ∈ lowerField (span D) := by
  have hF : ∀ k < span D, cohLetters k ∈ lowerField (span D) := fun k hk => letter_mem_lowerField hk
  unfold topQuotient topQuotientOf
  show PowerSeries.coeff (span D) (PowerSeries.mk cohLetters *
      (uniPoly (coframeVecOf cohLetters D) (colPos D) : PowerSeries CohField)) -
      cohLetters (span D) ∈ _
  rw [coeff_series_mul_uniPoly, add_sub_cancel_left]
  refine (lowerField (span D)).sum_mem fun j _ => (lowerField (span D)).mul_mem
    (coframeVec_mem D _ hF j) ?_
  have := colPos_pos D j
  exact letterOf_mem D _ hF (by omega)

end Independence

end SkewCoframeRigidity.Coframe
