/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/


import SkewCornerDescent.Matrix.OriginalLiteralIntervalColumnRanks

/-!
# Complete original source frames with both selected pivots restored

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
The full physical index frame includes every source row and column between
the selected endpoint components. Its exact source equivalence restores both
pivots rather than restricting to the removed interval. Equal extents
preserve the full relative source position. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate
open SkewGluing
variable {D : Diagram} {hD : IsConnectedSkew D}

/-- All local physical source positions, including both retained selected pivots. -/
abbrev OriginalInternalFullIndex {n : ℕ} (P : Profile n)
    (i : Fin (originalSelectedCount (hD := hD) P - 1)) :=
  Fin (originalInternalRowLast P i + 1 - originalInternalRowStart P i)

/-- The genuine original complementary source index at a full-frame position. -/
noncomputable def originalInternalFullSourceIndex {n : ℕ} (P : Profile n)
    (i : Fin (originalSelectedCount (hD := hD) P - 1))
    (k : OriginalInternalFullIndex P i) : Fin n :=
  ⟨originalInternalRowStart P i + k.val, by
    have hf := originalInternal_row_frame_bounds P i
    have hk := k.isLt
    omega⟩

/-- Every full-frame position lies in the complete original source interval. -/
theorem originalInternalFullSourceIndex_bounds {n : ℕ} (P : Profile n)
    (i : Fin (originalSelectedCount (hD := hD) P - 1)) (k : OriginalInternalFullIndex P i) :
    originalInternalRowStart P i ≤ (originalInternalFullSourceIndex P i k).val ∧
      (originalInternalFullSourceIndex P i k).val ≤ originalInternalRowLast P i := by
  have hf := originalInternal_row_frame_bounds P i
  have hk := k.isLt
  change originalInternalRowStart P i ≤ originalInternalRowStart P i + k.val ∧
    originalInternalRowStart P i + k.val ≤ originalInternalRowLast P i
  omega

/-- The complete local frame is bijective with every original source index in its range. -/
noncomputable def originalInternalFullSourceEquiv {n : ℕ} (P : Profile n)
    (i : Fin (originalSelectedCount (hD := hD) P - 1)) :
    OriginalInternalFullIndex P i ≃
      {t : Fin n // originalInternalRowStart P i ≤ t.val ∧
        t.val ≤ originalInternalRowLast P i} where
  toFun k := ⟨originalInternalFullSourceIndex P i k, originalInternalFullSourceIndex_bounds P i k⟩
  invFun t := ⟨t.val.val-originalInternalRowStart P i, by
    have ht := t.property
    have hf := originalInternal_row_frame_bounds P i
    omega⟩
  left_inv k := by
    apply Fin.ext
    change originalInternalRowStart P i + k.val-originalInternalRowStart P i = k.val
    omega
  right_inv t := by
    apply Subtype.ext
    apply Fin.ext
    change originalInternalRowStart P i + (t.val.val-originalInternalRowStart P i) = t.val.val
    have := t.property.1
    omega

/-- Identical full frame extents preserve relative physical source positions. -/
theorem originalInternalFullSourceIndex_relative {n : ℕ} (P : Profile n)
    (i j : Fin (originalSelectedCount (hD := hD) P - 1))
    (hL : originalInternalRowLast P i + 1 - originalInternalRowStart P i =
      originalInternalRowLast P j + 1 - originalInternalRowStart P j)
    (k : OriginalInternalFullIndex P i) :
    (originalInternalFullSourceIndex P j (Fin.cast hL k)).val - originalInternalRowStart P j =
      (originalInternalFullSourceIndex P i k).val - originalInternalRowStart P i := by
  change originalInternalRowStart P j + k.val - originalInternalRowStart P j =
    originalInternalRowStart P i + k.val - originalInternalRowStart P i
  omega

end SkewCornerDescent.Matrix.SelectedCoordinate
