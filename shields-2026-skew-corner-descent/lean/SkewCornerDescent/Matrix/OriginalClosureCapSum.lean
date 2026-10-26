/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalClosureCentralResponse

/-!
# Actual closure response top is the true-cap top sum

Supports `shields-2026-skew-corner-descent.tex` (`prop:closure-pin`, `cor:row-pencil`).
The full original cap-splice geometry supplies the exact central response top
as the sum of both actual cap tops. Neither a gap period nor an independent
cap model is assumed. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

include c in
/-- The central full closure interval has the exact sum of both original true
cap tops; this is a produced original endpoint identity. -/
theorem originalHorizontalClosure_central_cap_sum {n m : ℕ}
    (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalHorizontalClosure P = translate v Q.cells)
    (hB : 0 < originalSelectedCount (hD := hD) P) :
    let middle : Fin (originalSelectedCount (hD := hD) Q + 1) :=
      ⟨originalSelectedCount (hD := hD) P, by
        rw [originalHorizontalClosure_profile_selected_count P Q v hQ]; omega⟩
    originalHessenbergDistance (hD := hD) Q middle middle =
      originalHessenbergDistance (hD := hD) P 0 0 +
        originalHessenbergDistance (hD := hD) P (Fin.last _) (Fin.last _) := by
  have h := c.originalHorizontalClosure_central_distance P Q v hQ hB
  dsimp only at h ⊢
  have hlast : (⟨originalSelectedCount (hD := hD) P - 1, by omega⟩ :
      Fin (originalSelectedCount (hD := hD) P)).val + 1 = originalSelectedCount (hD := hD) P := by
    change originalSelectedCount (hD := hD) P - 1 + 1 = originalSelectedCount (hD := hD) P
    omega
  simp only [originalCompletedGap, ite_eq_left hlast] at h
  omega

end SkewCornerDescent.Matrix.SelectedCoordinate
