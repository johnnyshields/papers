/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.ProtectedComponentInverse
import SkewCornerDescent.Matrix.ResidueLowerBounds
import SkewCornerDescent.Matrix.LowerResponses

/-!
# Protected coefficients of complete component endpoint profiles

Supports `shields-2026-skew-corner-descent.tex` (`lem:early-recovery`). Every
incoming row coefficient has the same protected top from the least original
column, with its nonzero extreme inverse entry as coefficient. Outgoing column
coefficients have the symmetric greatest-row top. Complete inverses are retained;
no individual internal inverse entry is assumed nonzero. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing MvPolynomial
open scoped BigOperators

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- An original entry of index at most the selected span belongs to the actual
strict lower coefficient field: the selected top itself is solved by its genuine
affine prime relation. -/
theorem residue_hh_mem_selected_lower (z : ℤ) (hz : z ≤ (c.top : ℤ)) :
    c.residueMap (hh z) ∈ residueLowerField c.top c.top := by
  by_cases heq : z = (c.top : ℤ)
  · rw [heq, hh_pnat]
    exact c.residue_top_mem_lower
  · apply c.residue_lower_polynomial
    exact hh_mem_strictly_below c.top z (lt_of_le_of_ne hz heq)

/-- Every full unit-component inverse entry is already in the strictly lower
selected coefficient field, even when its original determinant has the same span
as the selected component and involves its top variable. -/
theorem component_residue_inverse_mem_selected_lower {n : ℕ} (P : Profile n)
    (hne : cellSchur D hD.1 ≠ P.schur) (hspan : P.topVar ≤ c.top) (i j : Fin (n + 1)) :
    letI := c.profileResidueInverse P hne
    ⅟((jtMatrix P.xi P.zeta).map c.residueMap) i j ∈ residueLowerField c.top c.top := by
  let := c.profileResidueInverse P hne
  apply inverse_entries_mem_subfield
  intro a b
  apply c.residue_hh_mem_selected_lower
  have hidx := P.xi_sub_zeta_le a b
  have htop := P.topVar_coe
  have hPN : (P.topVar : ℤ) ≤ (c.top : ℤ) := by exact_mod_cast hspan
  omega

/-- Every inverse entry of a maximal-span-bounded actual unit component stays
below any protected generator strictly above the selected span. -/
theorem component_residue_inverse_mem_lower {n : ℕ} (P : Profile n)
    (hne : cellSchur D hD.1 ≠ P.schur) (hspan : P.topVar ≤ c.top)
    (J : ℕ+) (hJ : c.top < J) (i j : Fin (n + 1)) :
    letI := c.profileResidueInverse P hne
    ⅟((jtMatrix P.xi P.zeta).map c.residueMap) i j ∈ residueLowerField c.top J := by
  let := c.profileResidueInverse P hne
  apply inverse_entries_mem_subfield
  intro a b
  apply c.residue_hh_mem_lower J hJ
  have hidx := P.xi_sub_zeta_le a b
  have htop := P.topVar_coe
  have hPN : (P.topVar : ℤ) ≤ (c.top : ℤ) := by exact_mod_cast hspan
  have hNJ : (c.top : ℤ) < (J : ℤ) := by exact_mod_cast hJ
  omega

/-- Every incoming coefficient is affine at the original least-column top,
with a produced lower remainder and a protected nonzero coefficient. The input
endpoint is measured relative to the component's normalized least column. -/
theorem component_incoming_protected_coefficient {n : ℕ} (P : Profile n)
    (hne : cellSchur D hD.1 ≠ P.schur) (hspan : P.topVar ≤ c.top)
    (J : ℕ+) (hJ : c.top < J) (j : Fin (n + 1)) :
    letI := c.profileResidueInverse P hne
    let I := ⅟((jtMatrix P.xi P.zeta).map c.residueMap)
    I (Fin.last n) j ≠ 0 ∧ I (Fin.last n) j ∈ residueLowerField c.top J ∧
      ∃ R ∈ residueLowerField c.top J,
        (∑ i, c.residueMap (hh ((J : ℤ) - P.zeta i)) * I i j) =
          residueGenerator c.top ⟨J, ne_of_gt hJ⟩ * I (Fin.last n) j + R := by
  classical
  let := c.profileResidueInverse P hne
  let I := ⅟((jtMatrix P.xi P.zeta).map c.residueMap)
  let R := ∑ i ∈ Finset.univ.erase (Fin.last n),
    c.residueMap (hh ((J : ℤ) - P.zeta i)) * I i j
  have hR : R ∈ residueLowerField c.top J := by
    apply (residueLowerField c.top J).sum_mem
    intro i hi
    apply (residueLowerField c.top J).mul_mem
    · apply c.residue_hh_mem_lower J hJ
      have hlast : i < Fin.last n := lt_of_le_of_ne (Fin.le_last i) (Finset.mem_erase.mp hi).1
      have hz := P.zeta_strictAnti hlast
      rw [P.zeta_last] at hz
      omega
    · exact c.component_residue_inverse_mem_lower P hne hspan J hJ i j
  have hlast : c.residueMap (hh ((J : ℤ) - P.zeta (Fin.last n))) =
      residueGenerator c.top ⟨J, ne_of_gt hJ⟩ := by
    rw [P.zeta_last, sub_zero, hh_pnat, c.residueMap_other J (ne_of_gt hJ)]
    rfl
  refine ⟨c.residue_inverse_least_column_entry_ne_zero P hne hspan j,
    c.component_residue_inverse_mem_lower P hne hspan J hJ (Fin.last n) j, R, hR, ?_⟩
  rw [← Finset.add_sum_erase Finset.univ
    (fun i => c.residueMap (hh ((J : ℤ) - P.zeta i)) * I i j) (Finset.mem_univ (Fin.last n)), hlast]

/-- Every outgoing coefficient has the analogous protected greatest-row top.
The actual endpoint is `xi(0)-J`, not an independently assigned row response. -/
theorem component_outgoing_protected_coefficient {n : ℕ} (P : Profile n)
    (hne : cellSchur D hD.1 ≠ P.schur) (hspan : P.topVar ≤ c.top)
    (J : ℕ+) (hJ : c.top < J) (i : Fin (n + 1)) :
    letI := c.profileResidueInverse P hne
    let I := ⅟((jtMatrix P.xi P.zeta).map c.residueMap)
    I i 0 ≠ 0 ∧ I i 0 ∈ residueLowerField c.top J ∧
      ∃ R ∈ residueLowerField c.top J,
        (∑ j, I i j * c.residueMap (hh (P.xi j - (P.xi 0 - (J : ℤ))))) =
          I i 0 * residueGenerator c.top ⟨J, ne_of_gt hJ⟩ + R := by
  classical
  let := c.profileResidueInverse P hne
  let I := ⅟((jtMatrix P.xi P.zeta).map c.residueMap)
  let R := ∑ j ∈ Finset.univ.erase (0 : Fin (n + 1)),
    I i j * c.residueMap (hh (P.xi j - (P.xi 0 - (J : ℤ))))
  have hR : R ∈ residueLowerField c.top J := by
    apply (residueLowerField c.top J).sum_mem
    intro j hj
    apply (residueLowerField c.top J).mul_mem
    · exact c.component_residue_inverse_mem_lower P hne hspan J hJ i j
    · apply c.residue_hh_mem_lower J hJ
      have hjpos : (0 : Fin (n + 1)) < j := lt_of_le_of_ne (Fin.zero_le j)
        (Ne.symm (Finset.mem_erase.mp hj).1)
      have hx := P.xi_strictAnti hjpos
      omega
  have hfirst : c.residueMap (hh (P.xi 0 - (P.xi 0 - (J : ℤ)))) =
      residueGenerator c.top ⟨J, ne_of_gt hJ⟩ := by
    rw [sub_sub_cancel, hh_pnat, c.residueMap_other J (ne_of_gt hJ)]
    rfl
  refine ⟨c.residue_inverse_greatest_row_entry_ne_zero P hne hspan i,
    c.component_residue_inverse_mem_lower P hne hspan J hJ i 0, R, hR, ?_⟩
  rw [← Finset.add_sum_erase Finset.univ
    (fun j => I i j * c.residueMap (hh (P.xi j - (P.xi 0 - (J : ℤ))))) (Finset.mem_univ 0), hfirst]

end SkewCornerDescent.Matrix.SelectedCoordinate
