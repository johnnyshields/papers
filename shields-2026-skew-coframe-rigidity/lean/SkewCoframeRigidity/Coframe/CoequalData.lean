/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCoframeRigidity.Coframe.Coprime

/-!
# Data of a coequal pair

Formalizes `shields-2026-skew-coframe-rigidity.tex`, `sc:coequal-data`.  Equal physical Schur
polynomials give equal coherent polynomials, equal signed proper corners, equal spans and equal
degree-`M` coefficients of `HG`.  Consequently the defect has no coefficient up to degree `M`
and degree at most `2M - 2`; for two distinct normalized diagrams it is nonzero and `M ≥ 3`.
-/

namespace SkewCoframeRigidity.Coframe

open SkewCofactorIndependence Polynomial
open scoped Polynomial Matrix

variable {n : ℕ}

/-- Equal top quotients and constant terms one force the clipped operator to vanish through
degree `M`. -/
theorem clippedOp_coeff_eq_zero {R : Type*} [CommRing R] (M : ℕ) (G C : R[X])
    (H : PowerSeries R) (hG : G.coeff 0 = 1) (hC : C.coeff 0 = 1)
    (htop : PowerSeries.coeff M (H * (G : PowerSeries R)) =
      PowerSeries.coeff M (H * (C : PowerSeries R))) :
    ∀ k ≤ M, (clippedOp M G C H).coeff k = 0 := by
  intro k hk
  set a1 : PowerSeries R := PowerSeries.mk fun i => PowerSeries.coeff (i + M) (H * G) with ha1
  set b1 : PowerSeries R := PowerSeries.mk fun i => PowerSeries.coeff (i + M) (H * C) with hb1
  have ha := PowerSeries.eq_shift_mul_X_pow_add_trunc M (H * (G : PowerSeries R))
  have hb := PowerSeries.eq_shift_mul_X_pow_add_trunc M (H * (C : PowerSeries R))
  have key : ((clippedOp M G C H : R[X]) : PowerSeries R) =
      PowerSeries.X ^ M * ((C : PowerSeries R) * a1 - (G : PowerSeries R) * b1) := by
    unfold clippedOp
    rw [Polynomial.coe_sub, Polynomial.coe_mul, Polynomial.coe_mul]
    have e1 : ((PowerSeries.trunc M (H * (C : PowerSeries R)) : R[X]) : PowerSeries R) =
        H * (C : PowerSeries R) - b1 * PowerSeries.X ^ M := by
      rw [eq_sub_iff_add_eq]
      rw [add_comm]; exact hb.symm
    have e2 : ((PowerSeries.trunc M (H * (G : PowerSeries R)) : R[X]) : PowerSeries R) =
        H * (G : PowerSeries R) - a1 * PowerSeries.X ^ M := by
      rw [eq_sub_iff_add_eq]
      rw [add_comm]; exact ha.symm
    rw [e1, e2]
    ring
  rw [← Polynomial.coeff_coe, key, PowerSeries.coeff_X_pow_mul']
  by_cases hlt : M ≤ k
  · have : k = M := le_antisymm hk hlt
    subst this
    rw [ite_eq_left le_rfl, Nat.sub_self]
    simp only [map_sub, PowerSeries.coeff_zero_eq_constantCoeff_apply, map_mul,
      Polynomial.constantCoeff_coe, hG, hC, one_mul]
    simp [ha1, hb1, htop]
  · rw [ite_eq_right hlt]

theorem natDegree_coframe_le (D : BetaDiagram (n + 1)) :
    (coframe D).natDegree ≤ span D - 1 := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro N hN
  have h1 : 1 ≤ span D := span_pos D
  change (uniPoly (coframeVecOf cohLetters D) (colPos D)).coeff N = 0
  rw [uniPoly_coeff, ite_eq_right (by omega)]
  simp only [zero_add]
  apply Finset.sum_eq_zero
  intro j _
  have := colPos_lt_span D j
  rw [ite_eq_right (by omega)]

theorem natDegree_numerator_le (D : BetaDiagram (n + 1)) :
    (numerator D).natDegree ≤ span D - 1 := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro N hN
  have h1 : 1 ≤ span D := span_pos D
  unfold numerator
  rw [numeratorOf_coeff, ite_eq_right (by omega)]

theorem natDegree_defect_le {D E : BetaDiagram (n + 1)} (hs : span D = span E) :
    (defect D E).natDegree ≤ 2 * span D - 2 := by
  rw [defect_eq hs]
  have h1 : 1 ≤ span D := span_pos D
  have a := Polynomial.natDegree_mul_le (p := coframe D) (q := numerator E)
  have b := Polynomial.natDegree_mul_le (p := coframe E) (q := numerator D)
  have c1 := natDegree_coframe_le D
  have c2 := natDegree_coframe_le E
  have c3 := natDegree_numerator_le D
  have c4 := natDegree_numerator_le E
  have := Polynomial.natDegree_sub_le (coframe D * numerator E) (coframe E * numerator D)
  omega

theorem largestLabel_eq_of_schur_eq {D E : BetaDiagram (n + 1)} (hD : D.Connected)
    (hE : E.Connected) (h : D.schur = E.schur) : D.largestLabel = E.largestLabel := by
  have h1 := D.largest_mem_vars hD
  have h2 := E.largest_mem_vars hE
  rw [h] at h1
  rw [← h] at h2
  have a := E.vars_le_largestLabel _ h1
  have b := D.vars_le_largestLabel _ h2
  have := D.largestLabel_pos
  have := E.largestLabel_pos
  simp only [PNat.mk_coe] at a b
  omega

theorem cornerCoefficient_eq_of_schur_eq {D E : BetaDiagram (n + 1)} (hD : D.Connected)
    (hE : E.Connected) (h : D.schur = E.schur) : D.cornerCoefficient = E.cornerCoefficient := by
  have hl := largestLabel_eq_of_schur_eq hD hE h
  have h1 := D.pderiv_schur_largest
  have h2 := E.pderiv_schur_largest
  have hv : (⟨D.largestLabel.toNat, by have := D.largestLabel_pos; omega⟩ : ℕ+) =
      ⟨E.largestLabel.toNat, by have := E.largestLabel_pos; omega⟩ := by
    apply PNat.eq
    simp [hl]
  rw [← h1, ← h2, hv, h]

theorem cohCorner_ne_zero {D : BetaDiagram (n + 1)} (hD : D.Connected) : cohCorner D ≠ 0 := by
  unfold cohCorner cornerOf
  exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) (properDet_ne_zero hD)

theorem coequal_data {D E : BetaDiagram (n + 1)} (hD : D.Connected)
    (h : D.schur = E.schur) :
    cohSchur D = cohSchur E ∧ cohCorner D = cohCorner E ∧ span D = span E ∧
      topQuotient D = topQuotient E ∧ (∀ k ≤ span D, (defect D E).coeff k = 0) ∧
      (defect D E).natDegree ≤ 2 * span D - 2 := by
  have hE : E.Connected := D.connected_of_schur_eq E hD h
  have hSchur := cohSchur_eq_of_schur_eq h
  have hCorner := cohCorner_eq_of_corner_eq (cornerCoefficient_eq_of_schur_eq hD hE h)
  have hs : span D = span E := by
    unfold span
    rw [largestLabel_eq_of_schur_eq hD hE h]
  have htop : topQuotient D = topQuotient E := by
    have a := schur_eq_corner_mul_topQuotient hD
    have b := schur_eq_corner_mul_topQuotient hE
    rw [hSchur, hCorner] at a
    have hc : algebraMap CohRing CohField (cohCorner E) ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective CohRing CohField)).2
        (hCorner ▸ cohCorner_ne_zero hD)
    exact mul_left_cancel₀ hc (a.symm.trans b)
  refine ⟨hSchur, hCorner, hs, htop, ?_, natDegree_defect_le hs⟩
  rw [defect]
  refine clippedOp_coeff_eq_zero _ _ _ _ (coframe_coeff_zero D) (coframe_coeff_zero E) ?_
  have hE' : topQuotient E = PowerSeries.coeff (span D)
      (letterSeries * (coframe E : PowerSeries CohField)) := by
    unfold topQuotient topQuotientOf
    rw [hs]
    rfl
  exact htop.trans hE'

theorem coequal_distinct {D E : BetaDiagram (n + 1)} (hD : D.Connected)
    (hDn : D.col (Fin.last n) = 0) (hEn : E.col (Fin.last n) = 0)
    (h : D.schur = E.schur) (hne : D ≠ E) :
    3 ≤ span D ∧ 0 < n ∧ coframe D ≠ coframe E ∧ 0 < (coframe D).natDegree ∧
      0 < (coframe E).natDegree ∧ IsCoprime (coframe D) (coframe E) ∧ defect D E ≠ 0 := by
  have hE : E.Connected := D.connected_of_schur_eq E hD h
  obtain ⟨-, -, hs, -, hord, hdeg⟩ := coequal_data hD h
  have hcf : coframe D ≠ coframe E := by
    intro hc
    exact hne (eq_of_heq (eq_of_coframe_eq hDn hEn hD hE hs hc).2)
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact absurd (by rw [coframe_of_zero, coframe_of_zero]) hcf
    · exact hn
  have hpos : ∀ F : BetaDiagram (n + 1), F.Connected → 0 < (coframe F).natDegree := by
    intro F hF
    let j0 : Fin n := ⟨0, hn⟩
    have h1 : (coframe F).coeff (colPos F j0) ≠ 0 := by
      rw [coframe_coeff_ne_zero_iff hF (colPos_pos F j0)]
      exact Finset.mem_image_of_mem _ (Finset.mem_univ j0)
    exact lt_of_lt_of_le (colPos_pos F j0) (Polynomial.le_natDegree_of_ne_zero h1)
  have hdef : defect D E ≠ 0 := defect_ne_zero hD hE hn hs hcf
  refine ⟨?_, hn, hcf, hpos D hD, hpos E hE, coframe_isCoprime hD hE hcf, hdef⟩
  have hlead := Polynomial.leadingCoeff_ne_zero.2 hdef
  have hM : span D < (defect D E).natDegree := by
    by_contra hcon
    exact hlead (hord _ (not_lt.1 hcon))
  have := span_pos D
  omega

end SkewCoframeRigidity.Coframe
