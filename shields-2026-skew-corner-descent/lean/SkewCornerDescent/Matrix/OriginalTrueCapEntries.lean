/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalClosureResponseWord

/-!
# Actual true exterior entries and their local retained responses

Supports `shields-2026-skew-corner-descent.tex` (`lem:actual-words`). Both actual
Hessenberg exterior entries are the complete local responses at the canonical first
and last selected occurrences. The boundary endpoints are never replaced. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The actual first Hessenberg entry is the full true upper exterior response. -/
theorem originalHessenberg_true_left_eq_local {n : ℕ} (P : Profile n)
    (hB : 0 < originalSelectedCount (hD := hD) P) :
    c.originalHessenbergResponse P 0 0 = c.originalLocalResponse P none
      (some (originalSelectedEnumeration (hD := hD) P ⟨0, hB⟩)) := by
  change c.originalLocalResponse P (originalHessenbergRows P 0)
    (originalHessenbergCols P (⟨0, hB⟩ : Fin (originalSelectedCount (hD := hD) P)).castSucc) = _
  rw [originalHessenbergRows_zero, originalHessenbergCols_castSucc]

/-- The actual last Hessenberg entry is the full true lower exterior response. -/
theorem originalHessenberg_true_right_eq_local {n : ℕ} (P : Profile n)
    (hB : 0 < originalSelectedCount (hD := hD) P) :
    c.originalHessenbergResponse P (Fin.last _) (Fin.last _) = c.originalLocalResponse P
      (some (originalSelectedEnumeration (hD := hD) P
        ⟨originalSelectedCount (hD := hD) P - 1, by omega⟩)) none := by
  let i : Fin (originalSelectedCount (hD := hD) P) :=
    ⟨originalSelectedCount (hD := hD) P - 1, by omega⟩
  have hi : i.succ = Fin.last (originalSelectedCount (hD := hD) P) := by
    apply Fin.ext
    change originalSelectedCount (hD := hD) P - 1 + 1 = originalSelectedCount (hD := hD) P
    omega
  change c.originalLocalResponse P (originalHessenbergRows P (Fin.last _))
    (originalHessenbergCols P (Fin.last _)) = _
  rw [originalHessenbergCols_last, ← hi, originalHessenbergRows_succ]

end SkewCornerDescent.Matrix.SelectedCoordinate
