/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/


import SkewCornerDescent.Matrix.FiniteRowDisplacement

/-!
# Common physical selected-row displacement from actual gap periods

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
The exact original selected-row ranks accumulate a finite physical gap
period into one common row displacement, including all eligible endpoint
positions. No wrapped or synthetic selected occurrence is used. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate
open SkewGluing
variable {D : Diagram} {hD : IsConnectedSkew D}

/-- The physical complementary source-row rank of a selected occurrence. -/
noncomputable def originalSelectedSourceRow {n : ℕ} (P : Profile n)
    (i : Fin (originalSelectedCount (hD := hD) P)) : ℤ :=
  ((originalSelectedEnumeration (hD := hD) P i).val.val.val : ℤ)

/-- Actual consecutive row-gap periods produce one common full-period row displacement. -/
theorem originalSelected_source_row_displacement {n : ℕ} (P : Profile n) (r B : ℕ)
    (hB : B < originalSelectedCount (hD := hD) P) (hr : r ≤ B)
    (hperiod : ∀ i : Fin (originalSelectedCount (hD := hD) P - 1), (hi : i.val + r < B) →
      originalInternalSourceRowGap P ⟨i.val + r, by omega⟩ = originalInternalSourceRowGap P i)
    (i : ℕ) (hi : i + r ≤ B) :
    originalSelectedSourceRow P ⟨i + r, by omega⟩ -
        originalSelectedSourceRow P ⟨i, by omega⟩ =
      originalSelectedSourceRow P ⟨r, by omega⟩ -
        originalSelectedSourceRow P ⟨0, by omega⟩ := by
  let s : ℕ → ℤ := fun j => if h : j < originalSelectedCount (hD := hD) P then
    originalSelectedSourceRow P ⟨j, h⟩ else 0
  have hs (j : ℕ) (hj : j < originalSelectedCount (hD := hD) P) :
      s j = originalSelectedSourceRow P ⟨j, hj⟩ := dite_eq_left hj
  have hstep (j : ℕ) (hj : j + r < B) : s (j + r + 1) - s (j + r) = s (j + 1) - s j := by
    have hp := hperiod ⟨j, by omega⟩ hj
    rw [hs (j+r+1) (by omega), hs (j+r) (by omega), hs (j+1) (by omega), hs j (by omega)]
    exact hp
  have he := finite_row_displacement_of_periodic_differences s r B hstep i hi
  rw [hs (i+r) (by omega), hs i (by omega), hs r (by omega), hs 0 (by omega)] at he
  exact he

end SkewCornerDescent.Matrix.SelectedCoordinate
