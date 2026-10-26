/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalClosureComponents
import SkewCornerDescent.Matrix.OriginalClosureCentralResponse
import SkewGluing.ProfileStatistics

/-!
# Actual horizontal closure preserves the full all-row inventory

Supports `shields-2026-skew-corner-descent.tex` (`cor:row-pencil`).
Both literal component copies in the actual closure preserve their geometric
row counts. The profile realization transports that same inventory, rather
than assuming row-shaped unit responses. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

/-- The complete horizontal closure has only row components when the actual
source has only row components; both full inventories remain. -/
theorem originalHorizontalClosure_components_all_rows {n : ℕ} (P : Profile n)
    (hrows : ∀ C ∈ edgeComponents (diagramInterior P.cells), (C.image Prod.fst).card = 1) :
    ∀ C ∈ edgeComponents (diagramInterior (originalHorizontalClosure P)),
      (C.image Prod.fst).card = 1 := by
  intro C hC
  rw [originalHorizontalClosure_components] at hC
  rcases Finset.mem_union.mp hC with hC | hC
  · exact hrows C hC
  · obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hC
    rw [rowCount_translate]
    exact hrows A hA

/-- Every actual translated profile of the horizontal closure inherits the
same all-row geometric component hypothesis. -/
theorem originalHorizontalClosure_profile_all_rows {n m : ℕ}
    (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalHorizontalClosure P = translate v Q.cells)
    (hrows : ∀ C ∈ edgeComponents (diagramInterior P.cells), (C.image Prod.fst).card = 1) :
    ∀ C ∈ edgeComponents (diagramInterior Q.cells), (C.image Prod.fst).card = 1 := by
  intro C hC
  have ht : translate v C ∈ edgeComponents (diagramInterior (originalHorizontalClosure P)) := by
    rw [hQ, interior_translate, edgeComponents_translate]
    exact Finset.mem_image.mpr ⟨C, hC, rfl⟩
  have h := originalHorizontalClosure_components_all_rows P hrows _ ht
  rwa [rowCount_translate] at h

end SkewCornerDescent.Matrix.SelectedCoordinate
