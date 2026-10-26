/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/


import SkewCornerDescent.Matrix.OriginalInternalFullFrame

/-!
# Physical positions of all four original endpoint pivots

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
Literal initial-core recovery and the complete physical row frame identify
the two starting-row pivots and the two last-column pivots in the full
source interval. Restoring them uses the same physical frame map as every
removed row and column. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate
open SkewGluing
variable {D : Diagram} {hD : IsConnectedSkew D}

/-- The physical last source index of the initial selected component. -/
noncomputable def originalInternalInitialLast {n : ℕ} (P : Profile n)
    (i : Fin (originalSelectedCount (hD := hD) P - 1)) : ℕ :=
  (interiorBlockLast P (originalSelectedEnumeration (hD := hD) P
    ⟨i.val, by have := i.isLt; omega⟩).val.val).val

/-- The initial selected proper strip lies before the next selected starting row. -/
theorem originalInternal_initial_frame_bounds {n : ℕ} (P : Profile n)
    (i : Fin (originalSelectedCount (hD := hD) P - 1)) :
    originalInternalRowStart P i ≤ originalInternalInitialLast P i ∧
      originalInternalInitialLast P i < originalInternalRowEnd P i := by
  let a : Fin (originalSelectedCount (hD := hD) P) := ⟨i.val, by have := i.isLt; omega⟩
  let b : Fin (originalSelectedCount (hD := hD) P) := ⟨i.val+1, by have := i.isLt; omega⟩
  let E := originalSelectedEnumeration (hD := hD) P
  have ha := interiorBlockFirst_le_last P (E a).val.val
  rw [(E a).val.property] at ha
  have hab : interiorBlockLast P (E a).val.val < (E b).val.val := by
    apply interiorBlock_index_lt P
    rw [interiorBlockLast_label]
    exact originalSelectedEnumeration_label_strictMono P
      (show a < b by change i.val < i.val+1; omega)
  exact ⟨ha, hab⟩

/-- The initial full component length is its exact physical endpoint difference. -/
theorem originalInternal_initial_last_sub_start {n : ℕ} (P : Profile n)
    (i : Fin (originalSelectedCount (hD := hD) P - 1)) :
    originalInternalInitialLast P i - originalInternalRowStart P i =
      interiorBlockLength P (originalSelectedEnumeration (hD := hD) P
        ⟨i.val, by have := i.isLt; omega⟩).val.val := by
  unfold interiorBlockLength
  rw [(originalSelectedEnumeration (hD := hD) P ⟨i.val, by have := i.isLt; omega⟩).val.property]
  rfl

/-- The complete original frame map identifies all four actual endpoint pivot positions. -/
theorem originalInternal_literal_full_pivot_ranks {n : ℕ} (P : Profile n)
    (i j : Fin (originalSelectedCount (hD := hD) P - 1))
    (hheight : originalHessenbergDistance (hD := hD) P
        (originalInternalStateIndex P i) (originalInternalStateIndex P i) =
      originalHessenbergDistance (hD := hD) P
        (originalInternalStateIndex P j) (originalInternalStateIndex P j))
    (hcopy : originalInternalLiteralCopy P i j) (k : OriginalInternalFullIndex P i) :
    let hL := (originalInternal_literal_row_frame P i j hheight hcopy).1
    let source := originalInternalFullSourceIndex P i k
    let target := originalInternalFullSourceIndex P j (Fin.cast hL k)
    (source.val = originalInternalRowStart P i → target.val = originalInternalRowStart P j) ∧
    (source.val = originalInternalRowEnd P i → target.val = originalInternalRowEnd P j) ∧
    (source.val = originalInternalInitialLast P i → target.val = originalInternalInitialLast P j) ∧
    (source.val = originalInternalRowLast P i → target.val = originalInternalRowLast P j) := by
  have hf := originalInternal_literal_row_frame P i j hheight hcopy
  have hi := originalInternal_row_frame_bounds P i
  have hj := originalInternal_row_frame_bounds P j
  have hai := originalInternal_initial_frame_bounds P i
  have haj := originalInternal_initial_frame_bounds P j
  have hlen : originalInternalInitialLast P i - originalInternalRowStart P i =
      originalInternalInitialLast P j - originalInternalRowStart P j := by
    rw [originalInternal_initial_last_sub_start, originalInternal_initial_last_sub_start]
    exact originalInternal_literal_start_length P i j hheight hcopy
  have hrelative := originalInternalFullSourceIndex_relative P i j hf.1 k
  have hsi := originalInternalFullSourceIndex_bounds P i k
  have htj := originalInternalFullSourceIndex_bounds P j (Fin.cast hf.1 k)
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro hk <;> omega

end SkewCornerDescent.Matrix.SelectedCoordinate
