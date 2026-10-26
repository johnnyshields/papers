/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalVerticalResponse
import SkewCornerDescent.Matrix.OriginalVerticalClosureEnumeration
import SkewCornerDescent.Matrix.OriginalNormalResidueCycles
import SkewCornerDescent.Matrix.OriginalInternalPeriodEntryGradient

/-!
# Actual central internal positions in both ordinary closures

Supports `shields-2026-skew-corner-descent.tex` (`prop:closure-pin`,
`thm:pure-primitive-first`). The canonical vertical enumeration identifies
its real two central selected occurrences with the literal upper-last
and lower-first copies. This bridges the actual internal residue to the
complete ordinary-plane response without assuming a center identification.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate
open SkewGluing
variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The actual horizontal internal center is its original full retained
central diagonal, with the one-position indexing shift proved. -/
theorem originalHorizontalClosure_internal_center_response {n m : ℕ}
    (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalHorizontalClosure P = translate v Q.cells)
    (hB : 0 < originalSelectedCount (hD := hD) P) :
    let center : Fin (originalSelectedCount (hD := hD) Q - 1) :=
      ⟨originalSelectedCount (hD := hD) P - 1, by
        rw [originalHorizontalClosure_profile_selected_count P Q v hQ]; omega⟩
    let middle : Fin (originalSelectedCount (hD := hD) Q + 1) :=
      ⟨originalSelectedCount (hD := hD) P, by
        rw [originalHorizontalClosure_profile_selected_count P Q v hQ]; omega⟩
    c.originalInternalResidue Q center =
      c.regularResidue (c.originalHessenbergResponse Q middle middle) := by
  intro center middle
  have he : (⟨center.val+1, by have := center.isLt; omega⟩ :
      Fin (originalSelectedCount (hD := hD) Q + 1)) = middle := by
    apply Fin.ext
    dsimp only [center, middle]
    omega
  exact congrArg (fun i => c.regularResidue (c.originalHessenbergResponse Q i i)) he

/-- The actual vertical internal center, not a freely selected response,
is the full horizontal central response minus the true-cap product. -/
theorem originalVerticalClosure_internal_center_response {n m s : ℕ}
    (P : Profile n) (V : Profile m) (H : Profile s) (v w : ℤ × ℤ)
    (hV : originalVerticalClosure P = translate v V.cells)
    (hH : originalHorizontalClosure P = translate w H.cells)
    (hB : 0 < originalSelectedCount (hD := hD) P) :
    let center : Fin (originalSelectedCount (hD := hD) V - 1) :=
      ⟨originalSelectedCount (hD := hD) P - 1, by
        rw [originalVerticalClosure_profile_selected_count P V v hV]; omega⟩
    let middle : Fin (originalSelectedCount (hD := hD) H + 1) :=
      ⟨originalSelectedCount (hD := hD) P, by
        rw [originalHorizontalClosure_profile_selected_count P H w hH]; omega⟩
    c.originalInternalResidue V center =
      c.regularResidue (c.originalHessenbergResponse H middle middle) -
        c.originalTrueCapProduct P := by
  let first : Fin (originalSelectedCount (hD := hD) P) := ⟨0, hB⟩
  let last : Fin (originalSelectedCount (hD := hD) P) :=
    ⟨originalSelectedCount (hD := hD) P - 1, by omega⟩
  let center : Fin (originalSelectedCount (hD := hD) V - 1) :=
    ⟨originalSelectedCount (hD := hD) P - 1, by
      rw [originalVerticalClosure_profile_selected_count P V v hV]; omega⟩
  have hu := originalVerticalClosure_enumeration_copy P V v hV true last
  simp only [originalVerticalClosureSelectedIndex, ite_true, zero_add] at hu
  have he := c.originalInternalResponseMatrix_selected_entry V center center
  have hlow : center.val+1 = originalSelectedCount (hD := hD) P := by
    dsimp only [center]; omega
  rw [hu, show (⟨center.val+1, by have := center.isLt; omega⟩ :
      Fin (originalSelectedCount (hD := hD) V)) =
      originalVerticalClosureSelectedIndex P V v hV false first from by
        apply Fin.ext
        simpa only [originalVerticalClosureSelectedIndex, Bool.false_eq_true,
          ite_false, first, Fin.val_mk, add_zero] using hlow,
    originalVerticalClosure_enumeration_copy] at he
  have hr : c.originalInternalResidue V center =
      c.regularResidue (c.originalInternalResponseMatrix V center center) := rfl
  dsimp only
  rw [hr, he]
  exact c.originalVerticalClosure_central_response P V H v w hV hH hB

end SkewCornerDescent.Matrix.SelectedCoordinate
