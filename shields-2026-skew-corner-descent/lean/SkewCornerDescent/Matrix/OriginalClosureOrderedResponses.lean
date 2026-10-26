/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.OriginalClosureCapResponses
import SkewCornerDescent.Matrix.OriginalClosureEnumeration

/-!
# Actual ordered full responses in both closure copies

Supports `shields-2026-skew-corner-descent.tex` (`lem:actual-words`). Canonical occurrence
indices identify both complete source response matrices and the two genuine exterior cap
families inside the literal closure. Equal values retain distinct positions. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D}

/-- The canonical selected rank of a literal source occurrence in the closure. -/
noncomputable def originalClosureSelectedIndex {n m : ℕ}
    (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalHorizontalClosure P = translate v Q.cells) (upper : Bool)
    (i : Fin (originalSelectedCount (hD := hD) P)) :
    Fin (originalSelectedCount (hD := hD) Q) :=
  ⟨(if upper then 0 else originalSelectedCount (hD := hD) P) + i.val, by
    rw [originalHorizontalClosure_profile_selected_count P Q v hQ]
    have hi := i.isLt
    split <;> omega⟩

/-- Canonical enumeration places the entire literal copied occurrence at its actual rank. -/
theorem originalHorizontalClosure_enumeration_copy {n m : ℕ}
    (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalHorizontalClosure P = translate v Q.cells) (upper : Bool)
    (i : Fin (originalSelectedCount (hD := hD) P)) :
    originalSelectedEnumeration Q (originalClosureSelectedIndex P Q v hQ upper i) =
      originalHorizontalClosureSelectedCopy P Q v hQ upper (originalSelectedEnumeration P i) := by
  apply originalSelectedBlock_cells_injective Q
  apply translate_injective v
  rw [originalHorizontalClosureSelectedCopy_cells]
  cases upper
  · simpa only [originalClosureSelectedIndex, Bool.false_eq_true, ite_false] using
      originalHorizontalClosure_enumeration_lower_cells P Q v hQ i
  · simpa only [originalClosureSelectedIndex, ite_true, zero_add] using
      originalHorizontalClosure_enumeration_upper_cells P Q v hQ i

/-- Every full response between selected occurrences stays unchanged in either literal copy. -/
theorem originalHorizontalClosure_ordered_response {n m : ℕ}
    (c : SelectedCoordinate D hD) (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalHorizontalClosure P = translate v Q.cells) (upper : Bool)
    (i j : Fin (originalSelectedCount (hD := hD) P)) :
    c.originalHessenbergResponse Q
      (originalClosureSelectedIndex P Q v hQ upper i).succ
      (originalClosureSelectedIndex P Q v hQ upper j).castSucc =
        c.originalHessenbergResponse P i.succ j.castSucc := by
  change c.originalLocalResponse Q _ _ = c.originalLocalResponse P _ _
  rw [originalHessenbergRows_succ, originalHessenbergCols_castSucc,
    originalHessenbergRows_succ, originalHessenbergCols_castSucc,
    originalHorizontalClosure_enumeration_copy, originalHorizontalClosure_enumeration_copy]
  exact originalHorizontalClosure_local_response c P Q v hQ upper _ _

/-- The actual global left endpoint retains every complete upper-copy source cap response. -/
theorem originalHorizontalClosure_ordered_left_response {n m : ℕ}
    (c : SelectedCoordinate D hD) (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalHorizontalClosure P = translate v Q.cells)
    (i : Fin (originalSelectedCount (hD := hD) P)) :
    c.originalHessenbergResponse Q 0
      (originalClosureSelectedIndex P Q v hQ true i).castSucc =
        c.originalHessenbergResponse P 0 i.castSucc := by
  change c.originalLocalResponse Q _ _ = c.originalLocalResponse P _ _
  rw [originalHessenbergRows_zero, originalHessenbergRows_zero,
    originalHessenbergCols_castSucc, originalHessenbergCols_castSucc,
    originalHorizontalClosure_enumeration_copy]
  simpa only [originalClosureCapLeft, originalClosureCapRight, ite_true] using
    originalHorizontalClosure_cap_response c P Q v hQ true (originalSelectedEnumeration P i)

/-- The actual global right endpoint retains every complete lower-copy source cap response. -/
theorem originalHorizontalClosure_ordered_right_response {n m : ℕ}
    (c : SelectedCoordinate D hD) (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalHorizontalClosure P = translate v Q.cells)
    (i : Fin (originalSelectedCount (hD := hD) P)) :
    c.originalHessenbergResponse Q
      (originalClosureSelectedIndex P Q v hQ false i).succ (Fin.last _) =
        c.originalHessenbergResponse P i.succ (Fin.last _) := by
  change c.originalLocalResponse Q _ _ = c.originalLocalResponse P _ _
  rw [originalHessenbergCols_last, originalHessenbergCols_last,
    originalHessenbergRows_succ, originalHessenbergRows_succ,
    originalHorizontalClosure_enumeration_copy]
  simpa only [originalClosureCapLeft, originalClosureCapRight, Bool.false_eq_true, ite_false] using
    originalHorizontalClosure_cap_response c P Q v hQ false (originalSelectedEnumeration P i)

end SkewCornerDescent.Matrix.SelectedCoordinate
