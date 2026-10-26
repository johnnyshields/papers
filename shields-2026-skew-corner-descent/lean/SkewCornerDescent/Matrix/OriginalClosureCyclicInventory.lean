/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.OriginalClosureResponseWord
import SkewCornerDescent.Matrix.OriginalCapNormalization
import SkewCornerDescent.FiniteClosureWindows

/-!
# Complete cyclic inventory of the actual horizontal closure

Supports `shields-2026-skew-corner-descent.tex` (`lem:original-transfer`).
The literal matrix word supplies the cycle and its central response. Its linear
window sum retains one complete source inventory and every closure-cycle start,
including full-length windows and repeated equal responses. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing CyclicWindows

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The joining response and complete source word produce the exact closure-cycle inventory.
No cyclic correspondence or inventory identity is an input. -/
theorem originalHorizontalClosure_linear_inventory {n m : ℕ}
    (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalHorizontalClosure P = translate v Q.cells)
    (hB : 0 < originalSelectedCount (hD := hD) P)
    [NeZero (originalSelectedCount (hD := hD) P)]
    (j : ℕ) (hj : j ≤ originalSelectedCount (hD := hD) P) :
    let middle : Fin (originalSelectedCount (hD := hD) Q + 1) :=
      ⟨originalSelectedCount (hD := hD) P, by
        rw [originalHorizontalClosure_profile_selected_count P Q v hQ]; omega⟩
    let S := c.regularResidue (c.originalHessenbergResponse Q middle middle)
    linearInverseWindowSum (c.originalInternalResidue Q) j =
      linearInverseWindowSum (c.originalInternalResidue P) j +
        inverseWindowSum (completeResponseCycle (c.originalInternalResidue P) S) j := by
  let middle : Fin (originalSelectedCount (hD := hD) Q + 1) :=
    ⟨originalSelectedCount (hD := hD) P, by
      rw [originalHorizontalClosure_profile_selected_count P Q v hQ]; omega⟩
  let S := c.regularResidue (c.originalHessenbergResponse Q middle middle)
  have hlen : originalSelectedCount (hD := hD) Q - 1 =
      2 * originalSelectedCount (hD := hD) P - 1 := by
    rw [originalHorizontalClosure_profile_selected_count P Q v hQ]
  have hw (i : Fin (originalSelectedCount (hD := hD) Q - 1)) :
      c.originalInternalResidue Q i =
        completeResponseCycle (c.originalInternalResidue P) S
          ((finCongr hlen i).val : ZMod (originalSelectedCount (hD := hD) P)) := by
    change c.regularResidue (c.originalInternalResponse Q i) = _
    rw [c.originalHorizontalClosure_internal_response_word P Q v hQ hB i,
      completeResponseCycle_double]
    simp only [finCongr_apply, Fin.val_cast]
    split_ifs <;> rfl
  dsimp only
  rw [linearInverseWindowSum_fin_congr hlen (c.originalInternalResidue Q)
    (fun i => completeResponseCycle (c.originalInternalResidue P) S
      (i.val : ZMod (originalSelectedCount (hD := hD) P))) hw j]
  exact linearInverseWindowSum_complete_double (c.originalInternalResidue P) S j hj

end SkewCornerDescent.Matrix.SelectedCoordinate
