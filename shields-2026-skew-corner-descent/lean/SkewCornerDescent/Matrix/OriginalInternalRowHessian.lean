/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalRowHessian
import SkewCornerDescent.Matrix.OriginalCapNormalization
import SkewCornerDescent.Matrix.OriginalHessenbergTops

/-!
# Complete actual internal row-response integer jets

Supports `shields-2026-skew-corner-descent.tex` (`cor:row-pencil`).
Each full original internal response supplies its own two selected endpoint
occurrences and their actual order. The row-inventory mixed-jet bound therefore
applies to the unchanged source internal word, not to a surrogate row pencil.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Every actual internal response on an all-row inventory has the normalized
integer mixed-jet bound at a pair summing to its actual original top. -/
theorem originalInternal_row_hessian_bound {n : ℕ} (P : Profile n)
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ))
    (hrows : ∀ C ∈ edgeComponents (diagramInterior P.cells), (C.image Prod.fst).card = 1)
    (i : Fin (originalSelectedCount (hD := hD) P - 1))
    (p q : ℕ+) (hp : c.top < p) (hq : c.top < q)
    (hsum : (p : ℤ) + (q : ℤ) = originalHessenbergDistance (hD := hD) P
      ⟨i.val + 1, by omega⟩ ⟨i.val + 1, by omega⟩) :
    ∃ k : ℕ, k ≤ (if p = q then 1 else 2) ∧
      residueGeneratorDeriv c.top ⟨p, ne_of_gt hp⟩
        (residueGeneratorDeriv c.top ⟨q, ne_of_gt hq⟩ (c.originalInternalResidue P i)) =
        -(if p = q then 2 else 1 : OtherField c.top) * (k : OtherField c.top) := by
  let a : Fin (originalSelectedCount (hD := hD) P) := ⟨i.val, by omega⟩
  let b : Fin (originalSelectedCount (hD := hD) P) := ⟨i.val + 1, by omega⟩
  have hab : a < b := by change i.val < i.val + 1; omega
  have hs := hsum
  change (p : ℤ) + (q : ℤ) = originalHessenbergDistance (hD := hD) P a.succ b.castSucc at hs
  simp only [originalHessenbergDistance, originalHessenbergRows_succ,
    originalHessenbergCols_castSucc] at hs
  have h := c.original_row_response_hessian_bound P (originalSelectedEnumeration P a)
    (originalSelectedEnumeration P b) (originalSelectedEnumeration_label_strictMono P hab).le
    hmax hrows p q hp hq hs
  have hv : c.originalInternalResidue P i =
      c.regularResidue (c.originalLocalResponse P
        (some (originalSelectedEnumeration P a)) (some (originalSelectedEnumeration P b))) := by
    change c.regularResidue (c.originalHessenbergResponse P a.succ b.castSucc) = _
    simp only [originalHessenbergResponse, Matrix.submatrix_apply,
      originalHessenbergRows_succ, originalHessenbergCols_castSucc]
  rw [hv]
  exact h

end SkewCornerDescent.Matrix.SelectedCoordinate
