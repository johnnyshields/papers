/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCoframeRigidity.Stationary.UnitCase.Scale

/-!
# The complete coframe for the scaled letters

Formalizes the regularity statements of `sc:unit-expansion` in
`shields-2026-skew-coframe-rigidity.tex` for the scaled normalized letters `epsSeq`: the coframe of
a connected diagram with units is regular at `ε = 0` with leading term the coframe of its zero-free
core, it has constant term one and support on the column positions, and it satisfies the proper
row equations.
-/

namespace SkewCoframeRigidity.UnitCase

open SkewCofactorIndependence SkewCoframeRigidity SkewCoframeRigidity.Coframe
  SkewCoframeRigidity.UnitRestoration Polynomial

theorem hat_coeff_zero {n : ℕ} (D : BetaDiagram (n + 1)) : (hatCoframe D).coeff 0 = 1 := by
  unfold hatCoframe
  rw [coframeOf_eq_uniPoly]
  exact uniPoly_coeff_zero_of_pos _ _ (colPos_pos D)

theorem hat_support {n : ℕ} (D : BetaDiagram (n + 1)) {s : ℕ} (hs : s ≠ 0) (hc : s ∉ colSet D) :
    (hatCoframe D).coeff s = 0 := by
  unfold hatCoframe
  rw [coframeOf_eq_uniPoly]
  refine uniPoly_coeff_of_ne _ _ s (Nat.pos_of_ne_zero hs) fun j hj => hc ?_
  exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, hj⟩

theorem hat_degree {n : ℕ} (D : BetaDiagram (n + 1)) {s : ℕ} (hs : span D ≤ s) :
    (hatCoframe D).coeff s = 0 := by
  unfold hatCoframe
  have h0 : s ≠ 0 := by have := span_pos D; omega
  rw [coframeOf_eq_uniPoly, uniPoly_coeff, ite_eq_right_iff.mpr (fun h => absurd h h0), zero_add]
  refine Finset.sum_eq_zero fun j _ => ?_
  have := colPos_lt_span D j
  exact ite_eq_right_iff.mpr (fun h => by omega)

/-- The proper matrix of the normalized letters of a presented core is invertible. -/
theorem properDet_normLetters_ne_zero {m : ℕ} {C : BetaDiagram (m + 1)} (hC : C.Connected) :
    (properMatrixOf normLetters C).det ≠ 0 := by
  have : normLetters = fun k => (cohLetters 0)⁻¹ * cohLetters k := funext normLetters_eq
  rw [this, properMatrixOf_scale, Matrix.det_smul]
  exact mul_ne_zero (pow_ne_zero _ (inv_ne_zero cohLetters_zero_ne_zero))
    (properDet_cohLetters_ne_zero hC)

/-- The proper matrix of the scaled letters is invertible. -/
theorem hat_properDet_ne_zero {n m : ℕ} {D : BetaDiagram (n + 1)} {C : BetaDiagram (m + 1)}
    (P : CoreData D C) (hC : C.Connected) : (properMatrixOf epsSeq D).det ≠ 0 := by
  classical
  have hdet := tZero_det_ne_zero P normLetters (properDet_normLetters_ne_zero hC)
  set φ := algebraMap CohField[X] Eps with hφ
  have hinj : Function.Injective φ := IsFractionRing.injective CohField[X] Eps
  have hB : denomPoly D normLetters ≠ 0 := by
    intro h0
    have := coeff_zero_denomPoly D normLetters
    rw [h0, Polynomial.coeff_zero] at this
    exact hdet this.symm
  have hφB : φ (denomPoly D normLetters) ≠ 0 := (map_ne_zero_iff φ hinj).mpr hB
  have hdetmap : ((tTilde D normLetters).map φ).det = φ (denomPoly D normLetters) := by
    unfold denomPoly
    rw [RingHom.map_det]
    rfl
  unfold epsSeq
  rw [properMatrix_scaledSeq, Matrix.det_mul, Matrix.det_diagonal, hdetmap]
  refine mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun i _ => ?_) hφB
  exact (map_ne_zero_iff φ hinj).mpr (rowScale_ne_zero D i)

/-- The proper row equations. -/
theorem hat_rows {n m : ℕ} {D : BetaDiagram (n + 1)} {C : BetaDiagram (m + 1)}
    (P : CoreData D C) (hC : C.Connected) {i : ℕ} (hi : i ∈ rowSet D) :
    PowerSeries.coeff i (epsH * (hatCoframe D : PowerSeries Eps)) = 0 := by
  obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hi
  exact coeff_rowPos_eq_zero epsSeq D (coframeVecOf epsSeq D)
    (properMatrix_mulVec_coframeVecOf epsSeq D (hat_properDet_ne_zero P hC)) j

/-- Regularity at `ε = 0`: a common denominator `B` with `B(0) ≠ 0` and numerators `N` over
`CohField[ε]`, with leading term the coframe of the zero-free core. -/
theorem hat_regular {n m : ℕ} {D : BetaDiagram (n + 1)} {C : BetaDiagram (m + 1)}
    (P : CoreData D C) (hC : C.Connected) :
    ∃ (B : CohField[X]) (N : Polynomial CohField[X]), B.coeff 0 ≠ 0 ∧
      (∀ s, algebraMap CohField[X] Eps (N.coeff s) =
        algebraMap CohField[X] Eps B * (hatCoframe D).coeff s) ∧
      ∀ s, (N.coeff s).coeff 0 = B.coeff 0 * (coframe C).coeff s := by
  classical
  obtain ⟨B, N, hB, hN⟩ := coframe_regular_at_zero P normLetters (properDet_normLetters_ne_zero hC)
  have hinj : Function.Injective (algebraMap CohField[X] Eps) :=
    IsFractionRing.injective CohField[X] Eps
  have hzero : ∀ s, span D ≤ s → N s = 0 := by
    intro s hs
    apply hinj
    rw [← (hN s).1, map_zero]
    have : (coframeOf (scaledSeq normLetters) D).coeff s = 0 := hat_degree D hs
    rw [this, zero_mul]
  have hco : ∀ s, (∑ t ∈ Finset.range (span D), Polynomial.monomial t (N t)).coeff s = N s := by
    intro s
    rw [Polynomial.finsetSum_coeff]
    simp only [Polynomial.coeff_monomial]
    rw [Finset.sum_ite_eq']
    by_cases hs : s ∈ Finset.range (span D)
    · simp only [hs, ite_true]
    · simp only [hs, ite_false]
      exact (hzero s (by simpa using hs)).symm
  refine ⟨B, ∑ t ∈ Finset.range (span D), Polynomial.monomial t (N t), hB, fun s => ?_,
    fun s => ?_⟩
  · rw [hco, mul_comm]
    exact (hN s).1.symm
  · rw [hco, (hN s).2, coframeOf_normLetters]

end SkewCoframeRigidity.UnitCase
