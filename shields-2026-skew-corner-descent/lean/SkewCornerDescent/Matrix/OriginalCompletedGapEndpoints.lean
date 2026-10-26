/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalCompletedGaps

/-!
# Actual endpoint coordinates of every completed gap

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
Internal gaps retain their two consecutive selected occurrences. The final gap
retains both true cap endpoints, including the normalized empty boundaries.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Every nonfinal completed gap uses its actual consecutive selected endpoints. -/
theorem originalCompletedGap_internal_endpoints {n : ℕ} (P : Profile n)
    (k : Fin (originalSelectedCount (hD := hD) P))
    (hk : k.val + 1 < originalSelectedCount (hD := hD) P) :
    c.originalCompletedGap P k =
      P.xi (originalRowSplitEquiv P (.inl (some (originalSelectedEnumeration P k)))) -
        P.zeta (originalColSplitEquiv P (.inl (some (originalSelectedEnumeration P
          ⟨k.val + 1, hk⟩)))) - (c.top : ℤ) := by
  have hn : k.val + 1 ≠ originalSelectedCount (hD := hD) P := by omega
  rw [originalCompletedGap, ite_eq_right hn, originalHessenbergDistance,
    originalHessenbergRows_succ]
  have he : k.succ = (⟨k.val + 1, hk⟩ : Fin (originalSelectedCount (hD := hD) P)).castSucc :=
    Fin.ext rfl
  rw [he, originalHessenbergCols_castSucc]

/-- The final completed gap is the sum of its two genuine source cap distances,
minus the selected span. Both endpoint occurrences remain explicit. -/
theorem originalCompletedGap_last_endpoints {n : ℕ} (P : Profile n)
    (hB : 0 < originalSelectedCount (hD := hD) P) :
    let first : Fin (originalSelectedCount (hD := hD) P) := ⟨0, hB⟩
    let last : Fin (originalSelectedCount (hD := hD) P) :=
      ⟨originalSelectedCount (hD := hD) P - 1, by omega⟩
    c.originalCompletedGap P last =
      P.xi 0 -
        P.zeta (originalColSplitEquiv P (.inl (some (originalSelectedEnumeration P first)))) +
        P.xi (originalRowSplitEquiv P (.inl (some (originalSelectedEnumeration P last)))) -
        P.zeta (Fin.last n) - (c.top : ℤ) := by
  dsimp only
  rw [originalCompletedGap, ite_eq_left (by
      change (originalSelectedCount (hD := hD) P - 1) + 1 =
        originalSelectedCount (hD := hD) P
      omega),
    originalHessenbergDistance_first P hB, originalHessenbergDistance_last P hB]
  simp only [originalFirstCapDistance, originalLastCapDistance,
    originalRowSplitEquiv_selected, originalColSplitEquiv_selected]
  ring

end SkewCornerDescent.Matrix.SelectedCoordinate
