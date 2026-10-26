/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.OriginalClosureSelectedOrder
import Mathlib.Order.Preorder.Finite

/-!
# The complete original closure enumeration

Supports `shields-2026-skew-corner-descent.tex`, «Actual responses and residue classes»
(`sec:normal-chart`, `lem:actual-words`). The actual source enumeration consists of the
entire translated copy followed by the entire unshifted copy. Its index formula is
produced from literal component matching, strict order and the actual cardinality.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

attribute [local instance] Classical.propDecidable

variable {D : Diagram} {hD : IsConnectedSkew D}

/-- Concatenation of both complete literal selected-copy inventories in source order. -/
noncomputable def originalHorizontalClosureEnumeration {n m : ℕ}
    (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalHorizontalClosure P = translate v Q.cells)
    (i : Fin (2 * originalSelectedCount (hD := hD) P)) :
    OriginalSelectedBlocks (hD := hD) Q :=
  if hi : i.val < originalSelectedCount (hD := hD) P then
    originalHorizontalClosureSelectedCopy P Q v hQ true
      (originalSelectedEnumeration (hD := hD) P ⟨i.val, hi⟩)
  else
    originalHorizontalClosureSelectedCopy P Q v hQ false
      (originalSelectedEnumeration (hD := hD) P ⟨i.val - originalSelectedCount (hD := hD) P,
        by have h := i.isLt; omega⟩)

/-- The concatenated literal inventory is strictly increasing in actual source order. -/
theorem originalHorizontalClosureEnumeration_strictMono {n m : ℕ}
    (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalHorizontalClosure P = translate v Q.cells) :
    StrictMono (originalHorizontalClosureEnumeration (hD := hD) P Q v hQ) := by
  intro i j hij
  have hij' : i.val < j.val := hij
  unfold originalHorizontalClosureEnumeration
  split_ifs with hi hj hj
  · apply originalHorizontalClosureSelectedCopy_strictMono P Q v hQ true
    exact (originalSelectedEnumeration (hD := hD) P).strictMono hij'
  · exact originalHorizontalClosureSelectedCopy_before P Q v hQ _ _
  · omega
  · apply originalHorizontalClosureSelectedCopy_strictMono P Q v hQ false
    apply (originalSelectedEnumeration (hD := hD) P).strictMono
    change i.val - originalSelectedCount (hD := hD) P <
      j.val - originalSelectedCount (hD := hD) P
    omega

/-- The constructed concatenation is the canonical original enumeration, not another ordering. -/
theorem originalHorizontalClosureEnumeration_eq_original {n m : ℕ}
    (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalHorizontalClosure P = translate v Q.cells)
    (i : Fin (2 * originalSelectedCount (hD := hD) P)) :
    originalHorizontalClosureEnumeration P Q v hQ i =
      originalSelectedEnumeration (hD := hD) Q ⟨i.val, by
        rw [originalHorizontalClosure_profile_selected_count P Q v hQ]
        exact i.isLt⟩ := by
  have hc := originalHorizontalClosure_profile_selected_count (hD := hD) P Q v hQ
  let g : Fin (2 * originalSelectedCount (hD := hD) P) →
      Fin (2 * originalSelectedCount (hD := hD) P) := fun j =>
    ⟨((originalSelectedEnumeration (hD := hD) Q).symm
      (originalHorizontalClosureEnumeration P Q v hQ j)).val, by
      rw [← hc]
      exact ((originalSelectedEnumeration (hD := hD) Q).symm
        (originalHorizontalClosureEnumeration P Q v hQ j)).isLt⟩
  have hg : StrictMono g := by
    intro j k hjk
    exact (originalSelectedEnumeration (hD := hD) Q).symm.strictMono
      (originalHorizontalClosureEnumeration_strictMono P Q v hQ hjk)
  have hi := congrFun hg.eq_id i
  apply (originalSelectedEnumeration (hD := hD) Q).symm.injective
  rw [OrderIso.symm_apply_apply]
  apply Fin.ext
  exact congrArg (fun j : Fin (2 * originalSelectedCount (hD := hD) P) => j.val) hi

/-- The first complete selected segment is the translated source copy, occurrence by occurrence. -/
theorem originalHorizontalClosure_enumeration_upper_cells {n m : ℕ}
    (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalHorizontalClosure P = translate v Q.cells)
    (i : Fin (originalSelectedCount (hD := hD) P)) :
    translate v (interiorBlockCells Q
      (originalSelectedEnumeration (hD := hD) Q ⟨i.val, by
        rw [originalHorizontalClosure_profile_selected_count P Q v hQ]; omega⟩).val.val) =
      translate (vH P.cells) (interiorBlockCells P
        (originalSelectedEnumeration (hD := hD) P i).val.val) := by
  have he := originalHorizontalClosureEnumeration_eq_original P Q v hQ
    (⟨i.val, by have hi := i.isLt; omega⟩ : Fin (2 * originalSelectedCount (hD := hD) P))
  simp only [originalHorizontalClosureEnumeration, i.isLt, ↓reduceDIte] at he
  rw [← he]
  exact originalHorizontalClosureSelectedCopy_cells P Q v hQ true _

/-- The second complete selected segment is the unshifted source copy, occurrence by occurrence. -/
theorem originalHorizontalClosure_enumeration_lower_cells {n m : ℕ}
    (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalHorizontalClosure P = translate v Q.cells)
    (i : Fin (originalSelectedCount (hD := hD) P)) :
    translate v (interiorBlockCells Q
      (originalSelectedEnumeration (hD := hD) Q
        ⟨originalSelectedCount (hD := hD) P + i.val, by
          rw [originalHorizontalClosure_profile_selected_count P Q v hQ]; omega⟩).val.val) =
      interiorBlockCells P (originalSelectedEnumeration (hD := hD) P i).val.val := by
  have he := originalHorizontalClosureEnumeration_eq_original P Q v hQ
    (⟨originalSelectedCount (hD := hD) P + i.val, by have hi := i.isLt; omega⟩ :
      Fin (2 * originalSelectedCount (hD := hD) P))
  have hn : ¬ originalSelectedCount (hD := hD) P + i.val <
      originalSelectedCount (hD := hD) P := by omega
  simp only [originalHorizontalClosureEnumeration, hn, ↓reduceDIte, Nat.add_sub_cancel_left]
    at he
  rw [← he]
  exact originalHorizontalClosureSelectedCopy_cells P Q v hQ false _

end SkewCornerDescent.Matrix.SelectedCoordinate
