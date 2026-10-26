/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/


import SkewCornerDescent.Matrix.OriginalInternalSourceRowGap
import SkewCornerDescent.Matrix.OriginalPairedEndpointProfiles

/-!
# Physical source ranks recovered from literal original intervals

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
A complete paired interval copy at the same actual height transports both
endpoint polynomials and the entire ending selected core. The resulting
original row-count identity recovers the physical starting-row gap.
This is stronger than equality of response values alone. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate
open SkewGluing
variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Both complete endpoint polynomials transport through a genuine paired copy. -/
theorem originalInternal_literal_endpoint_profiles {n : ℕ} (P : Profile n)
    (i j : Fin (originalSelectedCount (hD := hD) P - 1))
    (hheight : originalHessenbergDistance (hD := hD) P
        (originalInternalStateIndex P i) (originalInternalStateIndex P i) =
      originalHessenbergDistance (hD := hD) P
        (originalInternalStateIndex P j) (originalInternalStateIndex P j))
    (hcopy : originalInternalLiteralCopy P i j) :
    c.originalInternalEndpointProfiles P i = c.originalInternalEndpointProfiles P j := by
  let ai : Fin (originalSelectedCount (hD := hD) P) := ⟨i.val, by have := i.isLt; omega⟩
  let bi : Fin (originalSelectedCount (hD := hD) P) := ⟨i.val+1, by have := i.isLt; omega⟩
  let aj : Fin (originalSelectedCount (hD := hD) P) := ⟨j.val, by have := j.isLt; omega⟩
  let bj : Fin (originalSelectedCount (hD := hD) P) := ⟨j.val+1, by have := j.isLt; omega⟩
  let E := originalSelectedEnumeration (hD := hD) P
  let x := fun a => P.xi (originalRowSplitEquiv (hD := hD) P (.inl (some (E a))))
  let y := fun a => P.zeta (originalColSplitEquiv (hD := hD) P (.inl (some (E a))))
  have hh : x ai - y bi = x aj - y bj := by
    change P.xi (originalRowSplitEquiv P (.inl (originalHessenbergRows P ai.succ))) -
        P.zeta (originalColSplitEquiv P (.inl (originalHessenbergCols P bi.castSucc))) =
      P.xi (originalRowSplitEquiv P (.inl (originalHessenbergRows P aj.succ))) -
        P.zeta (originalColSplitEquiv P (.inl (originalHessenbergCols P bj.castSucc))) at hheight
    simpa only [originalHessenbergRows_succ, originalHessenbergCols_castSucc] using hheight
  obtain ⟨e, he⟩ := hcopy
  have hx : x aj = x ai + originalInternalIntervalShift P i j := by
    change x aj = x ai + (x aj - x ai)
    ring
  have hy : y bj = y bi + originalInternalIntervalShift P i j := by
    change y bj = y bi + (x aj - x ai)
    omega
  have hp := c.original_interval_endpoint_polynomials_of_copy P P
    (E ai) (E bi) (E aj) (E bj) (originalInternalIntervalShift P i j) e he hx hy
  exact Prod.ext hp.1 hp.2

/-- The whole ending selected core, and hence its original row length, is recovered. -/
theorem originalInternal_literal_end_length {n : ℕ} (P : Profile n)
    (i j : Fin (originalSelectedCount (hD := hD) P - 1))
    (hheight : originalHessenbergDistance (hD := hD) P
        (originalInternalStateIndex P i) (originalInternalStateIndex P i) =
      originalHessenbergDistance (hD := hD) P
        (originalInternalStateIndex P j) (originalInternalStateIndex P j))
    (hcopy : originalInternalLiteralCopy P i j) :
    interiorBlockLength P (originalSelectedEnumeration (hD := hD) P
        ⟨i.val+1, by have := i.isLt; omega⟩).val.val =
      interiorBlockLength P (originalSelectedEnumeration (hD := hD) P
        ⟨j.val+1, by have := j.isLt; omega⟩).val.val := by
  obtain ⟨coord⟩ := exists_selectedCoordinate hD
  let ai : Fin (originalSelectedCount (hD := hD) P) := ⟨i.val, by have := i.isLt; omega⟩
  let bi : Fin (originalSelectedCount (hD := hD) P) := ⟨i.val+1, by have := i.isLt; omega⟩
  let aj : Fin (originalSelectedCount (hD := hD) P) := ⟨j.val, by have := j.isLt; omega⟩
  let bj : Fin (originalSelectedCount (hD := hD) P) := ⟨j.val+1, by have := j.isLt; omega⟩
  let E := originalSelectedEnumeration (hD := hD) P
  have hp := congrArg Prod.snd
    (coord.originalInternal_literal_endpoint_profiles P i j hheight hcopy)
  have hcells := coord.original_selected_end_core_literal P P (E ai) (E bi) (E aj) (E bj)
    (original_consecutive_endpoint_label_le P ai bi rfl)
    (original_consecutive_endpoint_label_le P aj bj rfl)
    _ (coord.originalInternal_height_gt_twice_top P i)
    (fun k _ => congrArg (fun p => p.coeff k) hp)
  have hc := congrArg (fun X : Diagram => (X.image Prod.fst).card) hcells
  simp only [Profile.rowCount_cells] at hc
  exact Nat.add_right_cancel hc

/-- Full literal interval copies preserve the actual selected-start row separation. -/
theorem originalInternal_literal_source_row_gap {n : ℕ} (P : Profile n)
    (i j : Fin (originalSelectedCount (hD := hD) P - 1))
    (hheight : originalHessenbergDistance (hD := hD) P
        (originalInternalStateIndex P i) (originalInternalStateIndex P i) =
      originalHessenbergDistance (hD := hD) P
        (originalInternalStateIndex P j) (originalInternalStateIndex P j))
    (hcopy : originalInternalLiteralCopy P i j) :
    originalInternalSourceRowGap P i = originalInternalSourceRowGap P j := by
  have hlen := originalInternal_literal_end_length P i j hheight hcopy
  have hcard := Fintype.card_congr (Classical.choose hcopy)
  rw [originalInternal_source_row_gap_card P i, originalInternal_source_row_gap_card P j,
    hlen, hcard]

end SkewCornerDescent.Matrix.SelectedCoordinate
