/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/


import SkewCornerDescent.Matrix.OriginalLiteralIntervalRanks

/-!
# Initial selected-core row length from complete literal interval copies

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
The full incoming endpoint polynomial recovers the entire normalized
initial selected core, hence its physical row length. Together with the
ending-core reconstruction this identifies both proper-strip boundaries.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate
open SkewGluing
variable {D : Diagram} {hD : IsConnectedSkew D}

/-- A genuine full interval copy recovers the entire initial selected core row length. -/
theorem originalInternal_literal_start_length {n : ℕ} (P : Profile n)
    (i j : Fin (originalSelectedCount (hD := hD) P - 1))
    (hheight : originalHessenbergDistance (hD := hD) P
        (originalInternalStateIndex P i) (originalInternalStateIndex P i) =
      originalHessenbergDistance (hD := hD) P
        (originalInternalStateIndex P j) (originalInternalStateIndex P j))
    (hcopy : originalInternalLiteralCopy P i j) :
    interiorBlockLength P (originalSelectedEnumeration (hD := hD) P
        ⟨i.val, by have := i.isLt; omega⟩).val.val =
      interiorBlockLength P (originalSelectedEnumeration (hD := hD) P
        ⟨j.val, by have := j.isLt; omega⟩).val.val := by
  obtain ⟨coord⟩ := exists_selectedCoordinate hD
  let ai : Fin (originalSelectedCount (hD := hD) P) := ⟨i.val, by have := i.isLt; omega⟩
  let bi : Fin (originalSelectedCount (hD := hD) P) := ⟨i.val+1, by have := i.isLt; omega⟩
  let aj : Fin (originalSelectedCount (hD := hD) P) := ⟨j.val, by have := j.isLt; omega⟩
  let bj : Fin (originalSelectedCount (hD := hD) P) := ⟨j.val+1, by have := j.isLt; omega⟩
  let E := originalSelectedEnumeration (hD := hD) P
  have hp := congrArg Prod.fst
    (coord.originalInternal_literal_endpoint_profiles P i j hheight hcopy)
  have hcells := coord.original_selected_start_core_literal P P (E ai) (E bi) (E aj) (E bj)
    (original_consecutive_endpoint_label_le P ai bi rfl)
    (original_consecutive_endpoint_label_le P aj bj rfl)
    _ (coord.originalInternal_height_gt_twice_top P i)
    (fun k _ => congrArg (fun p => p.coeff k) hp)
  have hc := congrArg (fun X : Diagram => (X.image Prod.fst).card) hcells
  simp only [Profile.rowCount_cells] at hc
  exact Nat.add_right_cancel hc

end SkewCornerDescent.Matrix.SelectedCoordinate
