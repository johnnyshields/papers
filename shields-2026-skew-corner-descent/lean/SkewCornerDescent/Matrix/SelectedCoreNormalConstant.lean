/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalNormalHessenberg
import SkewCornerDescent.Matrix.SelectedCoreProfiles

/-!
# Complete normal series of the proper selected core

Supports `shields-2026-skew-corner-descent.tex` (`lem:early-recovery`).
Strict original generator bounds make every proper-core entry and both endpoint
vectors constant in the genuine normal chart. No constancy premise is assumed.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing MvPolynomial

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Every original polynomial omitting the selected generator has its complete constant
normal series, not merely the same zeroth coefficient. -/
theorem normalPolynomialSeries_of_top_notMem (f : Lambda) (hf : c.top ∉ f.vars) :
    c.normalPolynomialSeries f = PowerSeries.C (c.residueMap f) := by
  have hc := c.normalChart_of_top_notMem f hf
  have he : c.normalPolynomialSeries f = PowerSeries.C
      (algebraMap (OtherPolynomial c.top) (OtherField c.top)
        ((splitGenerator c.top f).coeff 0)) := by
    unfold normalPolynomialSeries
    rw [RingHom.comp_apply, Polynomial.coeToPowerSeries.ringHom_apply, hc, Polynomial.coe_C]
  have hz := c.normalPolynomialSeries_constant f
  rw [he, PowerSeries.constantCoeff_C] at hz
  rw [he, hz]

/-- Negative, zero and positive original indices below the selected top all retain
exactly their constant normal series. -/
theorem normal_hh_of_lt_top (z : ℤ) (hz : z < (c.top : ℤ)) :
    c.normalPolynomialSeries (hh z) = PowerSeries.C (c.residueMap (hh z)) := by
  apply c.normalPolynomialSeries_of_top_notMem
  intro hm
  have h := (mem_supported.mp (hh_mem_strictly_below c.top z hz)) hm
  exact lt_irrefl c.top h

/-- The actual proper selected minor retains every entry, with no positive normal jets. -/
theorem selected_core_normal_matrix_constant {n : ℕ} (P : Profile n)
    (hP : cellSchur D hD.1 = P.schur) :
    (jtMatrix (fun i : Fin n => P.xi i.succ) (fun j => P.zeta j.castSucc)).map
        c.normalPolynomialSeries =
      ((jtMatrix (fun i : Fin n => P.xi i.succ) (fun j => P.zeta j.castSucc)).map
        c.residueMap).map PowerSeries.C := by
  ext i j : 1
  apply c.normal_hh_of_lt_top
  change P.xi i.succ - P.zeta j.castSucc < (c.top : ℤ)
  have hx := P.xi_strictAnti (Fin.succ_pos i)
  have hz := P.zeta_nonneg j.castSucc
  have ht := P.topVar_coe
  rw [← c.top_eq_profile P hP] at ht
  omega

/-- Every entry of the complete proper incoming row has no positive normal jets. -/
theorem selected_core_normal_incoming_constant {n : ℕ} (P : Profile n)
    (hP : cellSchur D hD.1 = P.schur) (j : Fin n) :
    c.normalPolynomialSeries (hh (P.xi 0 - P.zeta j.castSucc)) =
      PowerSeries.C (c.residueMap (hh (P.xi 0 - P.zeta j.castSucc))) := by
  apply c.normal_hh_of_lt_top
  have hz := P.zeta_strictAnti (show j.castSucc < Fin.last n from j.isLt)
  have ht := P.topVar_coe
  rw [P.zeta_last] at hz
  rw [← c.top_eq_profile P hP] at ht
  omega

/-- Every entry of the complete proper outgoing column has no positive normal jets. -/
theorem selected_core_normal_outgoing_constant {n : ℕ} (P : Profile n)
    (hP : cellSchur D hD.1 = P.schur) (i : Fin n) :
    c.normalPolynomialSeries (hh (P.xi i.succ - P.zeta (Fin.last n))) =
      PowerSeries.C (c.residueMap (hh (P.xi i.succ - P.zeta (Fin.last n)))) := by
  apply c.normal_hh_of_lt_top
  have hx := P.xi_strictAnti (Fin.succ_pos i)
  have ht := P.topVar_coe
  rw [P.zeta_last]
  rw [← c.top_eq_profile P hP] at ht
  omega

end SkewCornerDescent.Matrix.SelectedCoordinate
