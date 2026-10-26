/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalVerticalClosureEnumeration

/-!
# Actual canonical endpoint coordinates in the vertical closure

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
The complete selected-copy enumeration identifies each original retained row
and column with its exact content shift. The vertical join is not erased.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

include c in
/-- Every canonical vertical selected occurrence has both of its genuine endpoint coordinates. -/
theorem originalVerticalClosure_ordered_endpoints {n m : ℕ}
    (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalVerticalClosure P = translate v Q.cells) (upper : Bool)
    (i : Fin (originalSelectedCount (hD := hD) P)) :
    let j := originalVerticalClosureSelectedIndex P Q v hQ upper i
    Q.xi (originalRowSplitEquiv Q (.inl (some (originalSelectedEnumeration Q j)))) =
      P.xi (originalRowSplitEquiv P (.inl (some (originalSelectedEnumeration P i)))) +
        (if upper then P.xi 0 else 0) ∧
    Q.zeta (originalColSplitEquiv Q (.inl (some (originalSelectedEnumeration Q j)))) =
      P.zeta (originalColSplitEquiv P (.inl (some (originalSelectedEnumeration P i)))) +
        (if upper then P.xi 0 else 0) := by
  have he := c.originalVerticalClosure_retained_endpoints P Q v hQ upper
    (originalSelectedEnumeration P i)
  dsimp only
  rw [originalVerticalClosure_enumeration_copy]
  exact he

end SkewCornerDescent.Matrix.SelectedCoordinate
