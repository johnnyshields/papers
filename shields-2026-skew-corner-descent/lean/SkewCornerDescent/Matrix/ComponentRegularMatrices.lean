/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.RegularMatrices
import SkewCornerDescent.Matrix.ComponentDenominators

/-!
# Actual component inverses at a selected prime

Supports `shields-2026-skew-corner-descent.tex`, «Equal windows and the determinant defect»
(`sec:normal-chart`, `lem:actual-elimination`). Actual nonselected connected components,
including span ties, and the proper minor of a selected component supply complete inverses
in the local ring and its residue field. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing MvPolynomial

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- A distinct actual connected profile has a regular full determinant, including equal spans. -/
theorem not_dvd_profile_det {n : ℕ} (P : Profile n)
    (hne : cellSchur D hD.1 ≠ P.schur) :
    ¬ cellSchur D hD.1 ∣ (jtMatrix P.xi P.zeta).det := by
  have hne' : cellSchur D hD.1 ≠ cellSchur P.cells P.isSkew_cells := by
    rwa [cellSchur_cells]
  simpa only [← schur_eq_det_jtMatrix, cellSchur_cells] using
    not_dvd_distinct_component hD P.isConnectedSkew_cells hne'

/-- Produce the full inverse of every nonselected original component in the actual local ring. -/
@[instance_reducible]
noncomputable def profileLocalInverse {n : ℕ} (P : Profile n)
    (hne : cellSchur D hD.1 ≠ P.schur) :
    Invertible ((jtMatrix P.xi P.zeta).map (algebraMap Lambda c.RegularRing)) :=
  c.regularMatrixInverse _ (not_dvd_profile_det (hD := hD) P hne)

/-- Produce the full residue inverse of a nonselected original component. -/
@[instance_reducible]
noncomputable def profileResidueInverse {n : ℕ} (P : Profile n)
    (hne : cellSchur D hD.1 ≠ P.schur) :
    Invertible ((jtMatrix P.xi P.zeta).map c.residueMap) :=
  c.regularResidueMatrixInverse _ (not_dvd_profile_det (hD := hD) P hne)

/-- Every literal profile in the selected connected Schur class has the same
actual geometric top, even when its diagram differs from the chosen representative. -/
theorem top_eq_profile {n : ℕ} (P : Profile n)
    (hP : cellSchur D hD.1 = P.schur) : c.top = P.topVar := by
  apply PNat.coe_injective
  have h := congrArg polynomialSpan hP
  rw [polynomialSpan_cellSchur hD, ← cellSchur_cells,
    polynomialSpan_cellSchur P.isConnectedSkew_cells, P.span_cells_eq_topVar, ← c.span_eq] at h
  exact h

include c in
/-- The proper selected minor is regular by its actual strictly lower generator support. -/
theorem not_dvd_selectedMinor {n : ℕ} (P : Profile n) (hP : cellSchur D hD.1 = P.schur) :
    ¬ cellSchur D hD.1 ∣
      (jtMatrix (fun i : Fin n => P.xi i.succ) (fun j => P.zeta j.castSucc)).det := by
  apply c.not_dvd_lower P.minor_ne_zero
  change betaDet (fun i : Fin n => P.xi i.succ) (fun j => P.zeta j.castSucc) ∈ _
  rw [P.minorDet_eq_interiorSchur, ← map_integralCellSchur]
  apply mem_supported.mpr
  intro j hj
  have h := (mem_supported.mp P.integralInterior_mem_below) (vars_map _ _ hj)
  rwa [c.top_eq_profile P hP]

/-- The selected component itself need not be a unit; its proper removed minor is one. -/
@[instance_reducible]
noncomputable def selectedMinorLocalInverse {n : ℕ} (P : Profile n)
    (hP : cellSchur D hD.1 = P.schur) :
    Invertible ((jtMatrix (fun i : Fin n => P.xi i.succ)
      (fun j => P.zeta j.castSucc)).map (algebraMap Lambda c.RegularRing)) :=
  c.regularMatrixInverse _ (c.not_dvd_selectedMinor P hP)

/-- The same actual proper selected minor remains invertible after residue. -/
@[instance_reducible]
noncomputable def selectedMinorResidueInverse {n : ℕ} (P : Profile n)
    (hP : cellSchur D hD.1 = P.schur) :
    Invertible ((jtMatrix (fun i : Fin n => P.xi i.succ)
      (fun j => P.zeta j.castSucc)).map c.residueMap) :=
  c.regularResidueMatrixInverse _ (c.not_dvd_selectedMinor P hP)

end SkewCornerDescent.Matrix.SelectedCoordinate
