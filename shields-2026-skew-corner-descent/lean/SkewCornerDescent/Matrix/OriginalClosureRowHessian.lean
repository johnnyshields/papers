/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalClosureRowInventory
import SkewCornerDescent.Matrix.OriginalClosureCapSum
import SkewCornerDescent.Matrix.OriginalInternalRowHessian

/-!
# Actual all-row closure supplies the integer mixed-jet origin

Supports `shields-2026-skew-corner-descent.tex` (`cor:row-pencil`).
Both complete literal component copies preserve the all-row hypothesis. The
actual central response is internal, and its produced top is the sum of the
original cap tops. It therefore supplies an integer mixed-jet origin before
any rational plane label is analyzed. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The actual central response of a complete all-row closure supplies the
integer origin for all its rational plane labels. Literal closure geometry
produces its internal index, inherited rows and maximal component span. -/
theorem originalHorizontalClosure_row_hessian_bound {n m : ℕ}
    (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalHorizontalClosure P = translate v Q.cells)
    (hB : 0 < originalSelectedCount (hD := hD) P)
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ))
    (hrows : ∀ C ∈ edgeComponents (diagramInterior P.cells), (C.image Prod.fst).card = 1)
    (p q : ℕ+) (hp : c.top < p) (hq : c.top < q)
    (hpTop : originalHessenbergDistance (hD := hD) P 0 0 = (p : ℤ))
    (hqTop : originalHessenbergDistance (hD := hD) P (Fin.last _) (Fin.last _) = (q : ℤ)) :
    let middle : Fin (originalSelectedCount (hD := hD) Q + 1) :=
      ⟨originalSelectedCount (hD := hD) P, by
        rw [originalHorizontalClosure_profile_selected_count P Q v hQ]; omega⟩
    ∃ k : ℕ, k ≤ (if p = q then 1 else 2) ∧
      residueGeneratorDeriv c.top ⟨p, ne_of_gt hp⟩
        (residueGeneratorDeriv c.top ⟨q, ne_of_gt hq⟩
          (c.regularResidue (c.originalHessenbergResponse Q middle middle))) =
        -(if p = q then 2 else 1 : OtherField c.top) * (k : OtherField c.top) := by
  have hc := originalHorizontalClosure_profile_selected_count (hD := hD) P Q v hQ
  let middle : Fin (originalSelectedCount (hD := hD) Q + 1) :=
    ⟨originalSelectedCount (hD := hD) P, by omega⟩
  let i : Fin (originalSelectedCount (hD := hD) Q - 1) :=
    ⟨originalSelectedCount (hD := hD) P - 1, by omega⟩
  have hi : (⟨i.val + 1, by omega⟩ : Fin (originalSelectedCount (hD := hD) Q + 1)) = middle := by
    apply Fin.ext
    dsimp only [i, middle]
    omega
  have hsum := c.originalHorizontalClosure_central_cap_sum P Q v hQ hB
  dsimp only at hsum
  rw [hpTop, hqTop] at hsum
  have hs : (p : ℤ) + (q : ℤ) = originalHessenbergDistance (hD := hD) Q
      ⟨i.val + 1, by omega⟩ ⟨i.val + 1, by omega⟩ := by
    rw [hi]
    exact hsum.symm
  have h := c.originalInternal_row_hessian_bound Q
    (c.originalHorizontalClosure_profile_component_span P Q v hQ hmax)
    (originalHorizontalClosure_profile_all_rows P Q v hQ hrows) i p q hp hq hs
  have hv : c.originalInternalResidue Q i =
      c.regularResidue (c.originalHessenbergResponse Q middle middle) := by
    unfold originalInternalResidue
    rw [hi]
  dsimp only
  rw [← hv]
  exact h

end SkewCornerDescent.Matrix.SelectedCoordinate
