/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalVerticalSelectedOrder
import Mathlib.Order.Preorder.Finite

/-!
# Complete canonical enumeration of the actual vertical selected copies

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
Strict literal order and the exact selected cardinality identify both complete
vertical copy segments with the canonical original occurrence enumeration.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D}

/-- Concatenation of both complete literal selected-copy inventories in source order. -/
noncomputable def originalVerticalClosureEnumeration {n m : ℕ}
    (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalVerticalClosure P = translate v Q.cells)
    (i : Fin (2 * originalSelectedCount (hD := hD) P)) :
    OriginalSelectedBlocks (hD := hD) Q :=
  if hi : i.val < originalSelectedCount (hD := hD) P then
    originalVerticalClosureSelectedCopy P Q v hQ true
      (originalSelectedEnumeration (hD := hD) P ⟨i.val, hi⟩)
  else
    originalVerticalClosureSelectedCopy P Q v hQ false
      (originalSelectedEnumeration (hD := hD) P ⟨i.val - originalSelectedCount (hD := hD) P,
        by have h := i.isLt; omega⟩)

/-- The concatenated literal inventory is strictly increasing in actual source order. -/
theorem originalVerticalClosureEnumeration_strictMono {n m : ℕ}
    (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalVerticalClosure P = translate v Q.cells) :
    StrictMono (originalVerticalClosureEnumeration (hD := hD) P Q v hQ) := by
  intro i j hij
  have hij' : i.val < j.val := hij
  unfold originalVerticalClosureEnumeration
  split_ifs with hi hj hj
  · apply originalVerticalClosureSelectedCopy_strictMono P Q v hQ true
    exact (originalSelectedEnumeration (hD := hD) P).strictMono hij'
  · exact originalVerticalClosureSelectedCopy_before P Q v hQ _ _
  · omega
  · apply originalVerticalClosureSelectedCopy_strictMono P Q v hQ false
    apply (originalSelectedEnumeration (hD := hD) P).strictMono
    change i.val - originalSelectedCount (hD := hD) P <
      j.val - originalSelectedCount (hD := hD) P
    omega

/-- The constructed concatenation is the canonical original enumeration, not another ordering. -/
theorem originalVerticalClosureEnumeration_eq_original {n m : ℕ}
    (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalVerticalClosure P = translate v Q.cells)
    (i : Fin (2 * originalSelectedCount (hD := hD) P)) :
    originalVerticalClosureEnumeration P Q v hQ i =
      originalSelectedEnumeration (hD := hD) Q ⟨i.val, by
        rw [originalVerticalClosure_profile_selected_count P Q v hQ]
        exact i.isLt⟩ := by
  have hc := originalVerticalClosure_profile_selected_count (hD := hD) P Q v hQ
  let g : Fin (2 * originalSelectedCount (hD := hD) P) →
      Fin (2 * originalSelectedCount (hD := hD) P) := fun j =>
    ⟨((originalSelectedEnumeration (hD := hD) Q).symm
      (originalVerticalClosureEnumeration P Q v hQ j)).val, by
      rw [← hc]
      exact ((originalSelectedEnumeration (hD := hD) Q).symm
        (originalVerticalClosureEnumeration P Q v hQ j)).isLt⟩
  have hg : StrictMono g := by
    intro j k hjk
    exact (originalSelectedEnumeration (hD := hD) Q).symm.strictMono
      (originalVerticalClosureEnumeration_strictMono P Q v hQ hjk)
  have hi := congrFun hg.eq_id i
  apply (originalSelectedEnumeration (hD := hD) Q).symm.injective
  rw [OrderIso.symm_apply_apply]
  apply Fin.ext
  exact congrArg (fun j : Fin (2 * originalSelectedCount (hD := hD) P) => j.val) hi

/-- The first complete selected segment is the translated source copy, occurrence by occurrence. -/
theorem originalVerticalClosure_enumeration_upper_cells {n m : ℕ}
    (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalVerticalClosure P = translate v Q.cells)
    (i : Fin (originalSelectedCount (hD := hD) P)) :
    translate v (interiorBlockCells Q
      (originalSelectedEnumeration (hD := hD) Q ⟨i.val, by
        rw [originalVerticalClosure_profile_selected_count P Q v hQ]; omega⟩).val.val) =
      translate (vH P.cells - eCell) (interiorBlockCells P
        (originalSelectedEnumeration (hD := hD) P i).val.val) := by
  have he := originalVerticalClosureEnumeration_eq_original P Q v hQ
    (⟨i.val, by have hi := i.isLt; omega⟩ : Fin (2 * originalSelectedCount (hD := hD) P))
  simp only [originalVerticalClosureEnumeration, i.isLt, ↓reduceDIte] at he
  rw [← he]
  exact originalVerticalClosureSelectedCopy_cells P Q v hQ true _

/-- The second complete selected segment is the unshifted source copy, occurrence by occurrence. -/
theorem originalVerticalClosure_enumeration_lower_cells {n m : ℕ}
    (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalVerticalClosure P = translate v Q.cells)
    (i : Fin (originalSelectedCount (hD := hD) P)) :
    translate v (interiorBlockCells Q
      (originalSelectedEnumeration (hD := hD) Q
        ⟨originalSelectedCount (hD := hD) P + i.val, by
          rw [originalVerticalClosure_profile_selected_count P Q v hQ]; omega⟩).val.val) =
      interiorBlockCells P (originalSelectedEnumeration (hD := hD) P i).val.val := by
  have he := originalVerticalClosureEnumeration_eq_original P Q v hQ
    (⟨originalSelectedCount (hD := hD) P + i.val, by have hi := i.isLt; omega⟩ :
      Fin (2 * originalSelectedCount (hD := hD) P))
  have hn : ¬ originalSelectedCount (hD := hD) P + i.val <
      originalSelectedCount (hD := hD) P := by omega
  simp only [originalVerticalClosureEnumeration, hn, ↓reduceDIte, Nat.add_sub_cancel_left]
    at he
  rw [← he]
  exact originalVerticalClosureSelectedCopy_cells P Q v hQ false _

/-- The canonical selected rank of one whole source occurrence in the vertical closure. -/
noncomputable def originalVerticalClosureSelectedIndex {n m : ℕ}
    (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalVerticalClosure P = translate v Q.cells) (upper : Bool)
    (i : Fin (originalSelectedCount (hD := hD) P)) :
    Fin (originalSelectedCount (hD := hD) Q) :=
  ⟨(if upper then 0 else originalSelectedCount (hD := hD) P) + i.val, by
    rw [originalVerticalClosure_profile_selected_count P Q v hQ]
    have hi := i.isLt
    split <;> omega⟩

/-- Both actual vertical copy maps agree with the complete canonical enumeration. -/
theorem originalVerticalClosure_enumeration_copy {n m : ℕ}
    (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalVerticalClosure P = translate v Q.cells) (upper : Bool)
    (i : Fin (originalSelectedCount (hD := hD) P)) :
    originalSelectedEnumeration Q (originalVerticalClosureSelectedIndex P Q v hQ upper i) =
      originalVerticalClosureSelectedCopy P Q v hQ upper (originalSelectedEnumeration P i) := by
  apply originalSelectedBlock_cells_injective Q
  apply translate_injective v
  rw [originalVerticalClosureSelectedCopy_cells]
  cases upper
  · simpa only [originalVerticalClosureSelectedIndex, Bool.false_eq_true, ite_false] using
      originalVerticalClosure_enumeration_lower_cells P Q v hQ i
  · simpa only [originalVerticalClosureSelectedIndex, ite_true, zero_add] using
      originalVerticalClosure_enumeration_upper_cells P Q v hQ i

end SkewCornerDescent.Matrix.SelectedCoordinate
