/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCoframeRigidity.Stationary.UnitCase.Pair
import SkewCoframeRigidity.Stationary.UnitCase.Master
import SkewCoframeRigidity.Stationary.UnitCase.MasterDelta
import SkewCoframeRigidity.Stationary.UnitCase.Masks
import SkewCoframeRigidity.Stationary.UnitCase.CoreIdentify
import SkewCoframeRigidity.Stationary.PositivePower

/-!
# The unit case of one-power stationary separation

Formalizes the true-unit case of `sc:positive-power` in `shields-2026-skew-coframe-rigidity.tex`.
-/

namespace SkewCoframeRigidity.Coframe

open SkewCofactorIndependence Polynomial SkewCoframeRigidity.UnitCase
  SkewCoframeRigidity.UnitRestoration
open scoped Polynomial Matrix

variable {n : ℕ}

/-- The unit-free letter series is the coherent unit times the positive normalized series. -/
theorem unitFreeSeries_eq_C_mul_Ubar :
    unitFreeSeries = PowerSeries.C (cohLetters 0) * Ubar := by
  have hθ : cohLetters 0 ≠ 0 := cohLetters_zero_ne_zero
  ext k
  rw [PowerSeries.coeff_C_mul]
  simp only [unitFreeSeries, Ubar, normLetters, PowerSeries.coeff_mk]
  by_cases hk : k = 0
  · simp [hk]
  · simp only [hk, if_false]
    field_simp

/-- A coefficient of the unit-free series times a polynomial is the coherent unit times the
corresponding coefficient for `Ū`. -/
theorem coeff_unitFree_eq (f : CohField[X]) (k : ℕ) :
    PowerSeries.coeff k (unitFreeSeries * (f : PowerSeries CohField)) =
      cohLetters 0 * PowerSeries.coeff k (Ubar * (f : PowerSeries CohField)) := by
  rw [unitFreeSeries_eq_C_mul_Ubar, mul_assoc, PowerSeries.coeff_C_mul]

/-- The top beta of a diagram with unit top component is both a row and a column position. -/
theorem unit_top_mem {D : BetaDiagram (n + 1)} {p : ℕ} (s : TopSide D p) (hg : s.c.g = 1)
    (hL : s.c.L = 0) : span D - 1 ∈ colSet D ∧ span D - 1 ∈ rowSet D := by
  obtain ⟨fc, fr⟩ := s.hflags
  have hsum := s.hsum
  have h0 : span D - 1 - s.a = 0 := by omega
  refine ⟨(fc _ (by omega)).2 ?_, (fr _ (by omega)).2 (Or.inl (by omega))⟩
  rw [h0, hg]
  simp

/-- No row of the core sits at a unit position of the diagram. -/
theorem core_gap {n m : ℕ} {D : BetaDiagram (n + 1)} {C : BetaDiagram (m + 1)}
    (P : CoreData D C) (hcD : span D - 1 ∈ colSet D) :
    ∀ i : Fin m, rowPos C i ≠ span C - 1 := by
  intro i h
  have hmem : span C - 1 ∈ rowSet C := Finset.mem_image.mpr ⟨i, Finset.mem_univ _, h⟩
  rw [rowSet_core P] at hmem
  exact (Finset.mem_sdiff.mp hmem).2 (by rw [span_core P] at *; exact hcD)

/-- The core coframe has no coefficient at a unit position of the diagram. -/
theorem core_coeff_gap {n m : ℕ} {D : BetaDiagram (n + 1)} {C : BetaDiagram (m + 1)}
    (P : CoreData D C) (hC : C.Connected) (hrD : span D - 1 ∈ rowSet D) (hpos : 0 < span D - 1) :
    (coframe C).coeff (span C - 1) = 0 := by
  by_contra h
  have hs := span_core P
  have h1 := (coframe_coeff_ne_zero_iff hC (s := span C - 1) (by omega)).mp h
  rw [colSet_core P] at h1
  exact (Finset.mem_sdiff.mp h1).2 (by rw [hs] at *; exact hrD)

theorem unit_case_main {D E : BetaDiagram (n + 1)} (hD : D.Connected) (hE : E.Connected)
    (hDn : D.col (Fin.last n) = 0) (hEn : E.col (Fin.last n) = 0) (hschur : D.schur = E.schur)
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
    (hL : sD.c.L = 0) : False := by
  have hcap : FixedCap.CapVanishing cellCap :=
    FixedCap.capVanishing cellCap cellCap_isNorm cellCap_connected
  have hθ : cohLetters 0 ≠ 0 := cohLetters_zero_ne_zero
  obtain ⟨hg1, -⟩ := unit_gk sD.c hL
  have hratio := ratio_unit sD.c hL (by omega)
  -- the potential is `-H^{p-1}`
  have hPQ : P = -(Polynomial.X ^ (p - 1)) * Q := by
    have h0 : Polynomial.aeval (cohLetters 0) (P + Polynomial.X ^ (p - 1) * Q) = 0 := by
      have hQ0 := aeval_theta_ne_zero hQ
      have e : PowerSeries.constantCoeff (potential P Q) =
          Polynomial.aeval (cohLetters 0) P * (Polynomial.aeval (cohLetters 0) Q)⁻¹ := by
        unfold potential
        rw [map_mul, PowerSeries.constantCoeff_inv, constantCoeff_aeval_letterSeries,
          constantCoeff_aeval_letterSeries]
      rw [e, hratio] at hrel
      simp only [map_add, map_mul, map_pow, Polynomial.aeval_X]
      field_simp at hrel
      linear_combination hrel
    have := aeval_theta_eq_zero h0
    linear_combination this
  have hr : potential P Q = -(letterSeries ^ (p - 1)) := by
    unfold potential
    rw [hPQ]
    have hQ0 : PowerSeries.constantCoeff (Polynomial.aeval letterSeries Q) ≠ 0 :=
      potential_const_ne Q hQ
    have hi := PowerSeries.mul_inv_cancel _ hQ0
    simp only [map_mul, map_neg, map_pow, Polynomial.aeval_X]
    linear_combination (-(letterSeries ^ (p - 1))) * hi
  have h : ∀ k < 2 * span D, PowerSeries.coeff k
      (((clippedOp (span D) (coframe D) (coframe E) (PowerSeries.X * letterSeries ^ p) :
          CohField[X]) : PowerSeries CohField) -
        PowerSeries.X * ((defect D E : CohField[X]) : PowerSeries CohField) *
          letterSeries ^ (p - 1)) = 0 := by
    intro k hk
    have := heq k hk
    rw [hr] at this
    rw [← this]
    congr 1
    ring
  -- the unit position
  have hLE : sE.c.L = 0 := by
    have h1 := sE.hsum
    have h2 := sD.hsum
    have h3 := hm.ha
    omega
  obtain ⟨hcD, hrD⟩ := unit_top_mem sD hg1 hL
  obtain ⟨hcE, hrE⟩ := unit_top_mem sE (hg ▸ hg1) hLE
  have hrE' : span D - 1 ∈ rowSet E := by rw [hs]; exact hrE
  -- the cores
  obtain ⟨hcnt, -, hsch⟩ := UnitRestoration.coequal_core hschur
  obtain ⟨c, hc⟩ : ∃ c, coreCount D = c + 1 :=
    ⟨coreCount D - 1, by have := UnitRestoration.coreCount_pos_of_pos D (by omega); omega⟩
  have hc' : coreCount E = c + 1 := hcnt.symm.trans hc
  obtain ⟨CD, PD, hCD, hzD, hsD⟩ := core_presented hD hc
  obtain ⟨CE, PE, hCE, hzE, hsE⟩ := core_presented hE hc'
  have hsch2 : CD.schur = CE.schur := hsD.trans (hsch.trans hsE.symm)
  obtain ⟨β, Gt, Ct, a, b, hβ, hG, hC, hdG, hdC, hrG, hrC, hsG, hsC, hE0, hPE, h00⟩ :=
    pair_package PD PE hD hE hCD hCE hs hq (by omega) h
  have hrowG := hrG _ hrD
  have hrowC := hrC _ hrE'
  have hM1 : 0 < span D - 1 := by omega
  -- the first cap
  have hfo := cap_first_order (M := span D) (by omega) hp hβ (coframe CD) (coframe CE) Gt Ct a b
    hG hC hrowG hrowC hE0
  have hU : PowerSeries.coeff (span CD - 1) (unitFreeSeries * (coframe CD : PowerSeries CohField))
      = PowerSeries.coeff (span CE - 1) (unitFreeSeries * (coframe CE : PowerSeries CohField)) := by
    rw [span_core PD, span_core PE, ← hs, coeff_unitFree_eq, coeff_unitFree_eq]
    rw [Polynomial.coe_sub, mul_sub, map_sub, sub_eq_zero] at hfo
    rw [hfo]
  have hCDE : CD = CE :=
    core_eq_of_first_cap hcap CD CE (core_isNorm PD hDn) (core_isNorm PE hEn) hCD hCE hsch2
      (core_gap PD hcD) (core_gap PE hcE) (core_coeff_gap PD hCD hrD hM1)
      (core_coeff_gap PE hCE hrE (by omega)) hU
  subst hCDE
  -- the second order
  obtain ⟨δ, hδ, hδT⟩ := second_order_vanishing (M := span D) hM hp hβ (coframe CD) Gt Ct a b hG hC
    hdG hdC hrowG hrowC hPE
  have hδ0 : δ.coeff 0 = 0 := by
    simp [hδ 0, Polynomial.coeff_sub, h00]
  have hrDE : rowSet CD = rowSet D \ colSet D := rowSet_core PD
  have hrEE : rowSet CD = rowSet E \ colSet E := rowSet_core PE
  have hrows : ∀ i ∈ rowSet CD,
      PowerSeries.coeff i (unitFreeSeries * (δ : PowerSeries CohField)) = 0 := by
    intro i hi
    have hi0 : i ≠ 0 := by
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hi
      exact (rowPos_pos CD j).ne'
    have h1 := Finset.mem_sdiff.mp (hrDE ▸ hi)
    have h2 := Finset.mem_sdiff.mp (hrEE ▸ hi)
    have := delta_row_zero (coframe CD) Gt Ct a b hG hC i (hsG i hi0 h1.2) (hsC i hi0 h2.2)
      (hrG i h1.1) (hrC i h2.1) δ hδ
    rw [coeff_unitFree_eq, this, mul_zero]
  have hT : clippedOp (span CD) (coframe CD) δ (PowerSeries.X ^ 1 * unitFreeSeries) = 0 := by
    rw [span_core PD, unitFreeSeries_eq_C_mul_Ubar,
      show (PowerSeries.X : PowerSeries CohField) ^ 1 *
        (PowerSeries.C (cohLetters 0) * Ubar) =
        PowerSeries.C (cohLetters 0) * (PowerSeries.X * Ubar) by ring,
      clippedOp_C_mul, hδT, mul_zero]
  have hδz : δ = 0 :=
    finite_injectivity_unitFree hCD hzD 1 (by rw [span_core PD]; omega) δ hδ0 hrows hT
  have hδz' : ∀ s, ((Ct - Gt).coeff s).coeff 1 = 0 := fun s => by
    rw [← hδ s, hδz, Polynomial.coeff_zero]
  obtain ⟨hrs, hcs⟩ := masks_eq_of_delta_zero PD PE hCD hzD hs hβ Gt Ct a b hG hC hrG hrC hsG hsC
    hδz'
  exact hcf (by rw [eq_of_flag_sets hDn hEn hrs hcs hs])

end SkewCoframeRigidity.Coframe
