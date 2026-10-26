/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.ProtectedComponentProfiles
import SkewCornerDescent.Matrix.SelectedCoreVectors
import SkewCornerDescent.Matrix.EndpointProfiles

/-!
# Proper selected-core endpoint profiles on the actual chart

Supports `shields-2026-skew-corner-descent.tex` (`lem:early-recovery`,
`prop:closure-pin`). Every selected Schur-class realization supplies its complete
proper inverse. Extreme original cofactors prove each profile coefficient nonzero,
and all coefficients lie in the genuine selected lower field. No literal equality
of selected component diagrams is assumed. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing MvPolynomial
open scoped BigOperators

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The complete incoming row of a selected component after its proper minor is
removed, in the original selected residue field. -/
noncomputable def selectedCoreIncoming {n : ℕ} (P : Profile n)
    (hP : cellSchur D hD.1 = P.schur) : Matrix Unit (Fin n) (OtherField c.top) :=
  letI := c.selectedMinorResidueInverse P hP
  (Matrix.of fun _ j => c.residueMap (hh (P.xi 0 - P.zeta j.castSucc))) *
    ⅟((jtMatrix (fun i : Fin n => P.xi i.succ) (fun j => P.zeta j.castSucc)).map c.residueMap)

/-- The complete outgoing column, with the same full proper inverse. -/
noncomputable def selectedCoreOutgoing {n : ℕ} (P : Profile n)
    (hP : cellSchur D hD.1 = P.schur) : Matrix (Fin n) Unit (OtherField c.top) :=
  letI := c.selectedMinorResidueInverse P hP
  ⅟((jtMatrix (fun i : Fin n => P.xi i.succ) (fun j => P.zeta j.castSucc)).map c.residueMap) *
    (Matrix.of fun i _ => c.residueMap (hh (P.xi i.succ - P.zeta (Fin.last n))))

/-- The original left profile of the selected core, including its constant unit. -/
noncomputable def selectedCoreLeftProfile {n : ℕ} (P : Profile n)
    (hP : cellSchur D hD.1 = P.schur) : LaurentPolynomial (OtherField c.top) :=
  endpointProfile (fun i : Fin n => P.xi 0 - P.xi i.succ)
    (fun i => c.selectedCoreIncoming P hP () i)

/-- The original right profile, with the same normal-dependent selected core. -/
noncomputable def selectedCoreRightProfile {n : ℕ} (P : Profile n)
    (hP : cellSchur D hD.1 = P.schur) : LaurentPolynomial (OtherField c.top) :=
  endpointProfile (fun i : Fin n => P.zeta i.castSucc - P.zeta (Fin.last n))
    (fun i => c.selectedCoreOutgoing P hP i ())

/-- The selected component's complete original determinant vanishes on exactly
this chart, independently of which Schur-class realization supplies it. -/
theorem selected_core_residue_det_zero {n : ℕ} (P : Profile n)
    (hP : cellSchur D hD.1 = P.schur) :
    ((jtMatrix P.xi P.zeta).map c.residueMap).det = 0 := by
  have hm := c.residueMap.map_det (jtMatrix P.xi P.zeta)
  change c.residueMap (jtMatrix P.xi P.zeta).det =
    ((jtMatrix P.xi P.zeta).map c.residueMap).det at hm
  rw [← hm, ← schur_eq_det_jtMatrix, ← hP]
  exact (c.residueMap_eq_zero_iff _).mpr dvd_rfl

/-- Every incoming selected-core coefficient is nonzero; an extreme complete
cofactor supplies its numerator, not a per-entry nonvanishing assumption. -/
theorem selected_core_incoming_ne_zero {n : ℕ} (P : Profile n)
    (hP : cellSchur D hD.1 = P.schur) (i : Fin n) : c.selectedCoreIncoming P hP () i ≠ 0 := by
  let A := (jtMatrix P.xi P.zeta).map c.residueMap
  let : Invertible (A.submatrix Fin.succ Fin.castSucc) := c.selectedMinorResidueInverse P hP
  have h := selected_core_incoming_adjugate A (c.selected_core_residue_det_zero P hP) (Fin.last n) i
  change A.adjugate (Fin.last n) i.succ =
    -A.adjugate (Fin.last n) 0 * c.selectedCoreIncoming P hP () i at h
  intro hz
  rw [hz, mul_zero] at h
  exact c.residue_least_column_cofactor_ne_zero P (c.top_eq_profile P hP).symm.le i.succ h

/-- Every outgoing selected-core coefficient is likewise nonzero. -/
theorem selected_core_outgoing_ne_zero {n : ℕ} (P : Profile n)
    (hP : cellSchur D hD.1 = P.schur) (i : Fin n) : c.selectedCoreOutgoing P hP i () ≠ 0 := by
  let A := (jtMatrix P.xi P.zeta).map c.residueMap
  let : Invertible (A.submatrix Fin.succ Fin.castSucc) := c.selectedMinorResidueInverse P hP
  have h := selected_core_outgoing_adjugate A (c.selected_core_residue_det_zero P hP) i
  change A.adjugate i.castSucc 0 =
    -A.adjugate (Fin.last n) 0 * c.selectedCoreOutgoing P hP i () at h
  intro hz
  rw [hz, mul_zero] at h
  exact c.residue_greatest_row_cofactor_ne_zero P (c.top_eq_profile P hP).symm.le i.castSucc h

/-- Every entry of the actual proper selected inverse is in the strict selected
lower field, including empty-row pivots and complete off-diagonal couplings. -/
theorem selected_core_inverse_mem_lower {n : ℕ} (P : Profile n)
    (hP : cellSchur D hD.1 = P.schur) (i j : Fin n) :
    letI := c.selectedMinorResidueInverse P hP
    ⅟((jtMatrix (fun i : Fin n => P.xi i.succ) (fun j => P.zeta j.castSucc)).map c.residueMap)
      i j ∈ residueLowerField c.top c.top := by
  let := c.selectedMinorResidueInverse P hP
  apply inverse_entries_mem_subfield
  intro a b
  apply c.residue_lower_polynomial
  apply hh_mem_strictly_below
  change P.xi a.succ - P.zeta b.castSucc < (c.top : ℤ)
  have hx := P.xi_strictAnti (Fin.succ_pos a)
  have hz := P.zeta_nonneg b.castSucc
  have htop := P.topVar_coe
  have heq := c.top_eq_profile P hP
  rw [← heq] at htop
  omega

/-- Incoming profile coefficients have only genuine smaller original generators. -/
theorem selected_core_incoming_mem_lower {n : ℕ} (P : Profile n)
    (hP : cellSchur D hD.1 = P.schur) (i : Fin n) :
    c.selectedCoreIncoming P hP () i ∈ residueLowerField c.top c.top := by
  let := c.selectedMinorResidueInverse P hP
  change (∑ j, c.residueMap (hh (P.xi 0 - P.zeta j.castSucc)) *
    ⅟((jtMatrix (fun i : Fin n => P.xi i.succ)
      (fun j => P.zeta j.castSucc)).map c.residueMap) j i) ∈ _
  apply (residueLowerField c.top c.top).sum_mem
  intro j _
  apply (residueLowerField c.top c.top).mul_mem
  · apply c.residue_lower_polynomial
    apply hh_mem_strictly_below
    have hz := P.zeta_strictAnti (Fin.castSucc_lt_last j)
    rw [P.zeta_last] at hz
    have htop := P.topVar_coe
    rw [← c.top_eq_profile P hP] at htop
    omega
  · exact c.selected_core_inverse_mem_lower P hP j i

/-- Outgoing coefficients lie in that same actual lower field. -/
theorem selected_core_outgoing_mem_lower {n : ℕ} (P : Profile n)
    (hP : cellSchur D hD.1 = P.schur) (i : Fin n) :
    c.selectedCoreOutgoing P hP i () ∈ residueLowerField c.top c.top := by
  let := c.selectedMinorResidueInverse P hP
  change (∑ j, ⅟((jtMatrix (fun i : Fin n => P.xi i.succ)
    (fun j => P.zeta j.castSucc)).map c.residueMap) i j *
      c.residueMap (hh (P.xi j.succ - P.zeta (Fin.last n)))) ∈ _
  apply (residueLowerField c.top c.top).sum_mem
  intro j _
  apply (residueLowerField c.top c.top).mul_mem
  · exact c.selected_core_inverse_mem_lower P hP i j
  · apply c.residue_lower_polynomial
    apply hh_mem_strictly_below
    have hx := P.xi_strictAnti (Fin.succ_pos j)
    have htop := P.topVar_coe
    rw [← c.top_eq_profile P hP] at htop
    rw [P.zeta_last]
    omega

end SkewCornerDescent.Matrix.SelectedCoordinate
