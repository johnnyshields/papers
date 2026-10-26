/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.OriginalClosureOrderedResponses

/-!
# The complete actual internal response word of the literal closure

Supports `shields-2026-skew-corner-descent.tex` (`lem:actual-words`). Both complete source
internal words occur in the actual regular-ring diagonal, separated by the single actual
central response. Every repeated response keeps its original occurrence position. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The actual internal response at each original selected interval, with both true caps omitted. -/
noncomputable def originalInternalResponse {n : ℕ} (P : Profile n)
    (i : Fin (originalSelectedCount (hD := hD) P - 1)) : c.RegularRing :=
  c.originalHessenbergResponse P ⟨i.val + 1, by have hi := i.isLt; omega⟩
    ⟨i.val + 1, by have hi := i.isLt; omega⟩

/-- An internal word entry is the full local response between consecutive actual occurrences. -/
theorem originalInternalResponse_eq_local {n : ℕ} (P : Profile n)
    (i : Fin (originalSelectedCount (hD := hD) P - 1)) :
    c.originalInternalResponse P i =
      c.originalLocalResponse P
        (some (originalSelectedEnumeration (hD := hD) P
          ⟨i.val, by have hi := i.isLt; omega⟩))
        (some (originalSelectedEnumeration (hD := hD) P
          ⟨i.val + 1, by have hi := i.isLt; omega⟩)) := by
  unfold originalInternalResponse originalHessenbergResponse Matrix.submatrix
  change c.originalLocalResponse P
    (originalHessenbergRows P
      (⟨i.val, by have hi := i.isLt; omega⟩ : Fin (originalSelectedCount (hD := hD) P)).succ)
    (originalHessenbergCols P
      (⟨i.val + 1, by have hi := i.isLt; omega⟩ :
        Fin (originalSelectedCount (hD := hD) P)).castSucc) = _
  rw [originalHessenbergRows_succ, originalHessenbergCols_castSucc]

/-- Every position of either entire internal source word is its actual closure response. -/
theorem originalHorizontalClosure_internal_response_copy {n m : ℕ}
    (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalHorizontalClosure P = translate v Q.cells) (upper : Bool)
    (i : Fin (originalSelectedCount (hD := hD) P - 1)) :
    c.originalInternalResponse Q
      ⟨(if upper then 0 else originalSelectedCount (hD := hD) P) + i.val, by
        rw [originalHorizontalClosure_profile_selected_count P Q v hQ]
        have hi := i.isLt
        split <;> omega⟩ = c.originalInternalResponse P i := by
  let a : Fin (originalSelectedCount (hD := hD) P) := ⟨i.val, by have hi := i.isLt; omega⟩
  let b : Fin (originalSelectedCount (hD := hD) P) := ⟨i.val + 1, by have hi := i.isLt; omega⟩
  have he := originalHorizontalClosure_ordered_response c P Q v hQ upper a b
  change c.originalHessenbergResponse Q _ _ = c.originalHessenbergResponse P _ _
  convert he using 1 <;> congr 1

/-- The complete internal closure word is two original words with its actual central entry. -/
theorem originalHorizontalClosure_internal_response_word {n m : ℕ}
    (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalHorizontalClosure P = translate v Q.cells)
    (hB : 0 < originalSelectedCount (hD := hD) P)
    (i : Fin (originalSelectedCount (hD := hD) Q - 1)) :
    c.originalInternalResponse Q i =
      if hi : i.val < originalSelectedCount (hD := hD) P - 1 then
        c.originalInternalResponse P ⟨i.val, hi⟩
      else if hm : i.val = originalSelectedCount (hD := hD) P - 1 then
        c.originalHessenbergResponse Q
          ⟨originalSelectedCount (hD := hD) P, by
            rw [originalHorizontalClosure_profile_selected_count P Q v hQ]; omega⟩
          ⟨originalSelectedCount (hD := hD) P, by
            rw [originalHorizontalClosure_profile_selected_count P Q v hQ]; omega⟩
      else c.originalInternalResponse P
        ⟨i.val - originalSelectedCount (hD := hD) P, by
          have _hi := i.isLt
          have hc := originalHorizontalClosure_profile_selected_count (hD := hD) P Q v hQ
          omega⟩ := by
  split_ifs with hi hm
  · have he := c.originalHorizontalClosure_internal_response_copy P Q v hQ true ⟨i.val, hi⟩
    simpa only [ite_true, zero_add] using he
  · unfold originalInternalResponse
    congr 1 <;> apply Fin.ext <;> simp only <;> omega
  · have hj : i.val - originalSelectedCount (hD := hD) P <
        originalSelectedCount (hD := hD) P - 1 := by
      have h := i.isLt
      have hc := originalHorizontalClosure_profile_selected_count (hD := hD) P Q v hQ
      omega
    have he := c.originalHorizontalClosure_internal_response_copy P Q v hQ false
      ⟨i.val - originalSelectedCount (hD := hD) P, hj⟩
    have ha : originalSelectedCount (hD := hD) P +
        (i.val - originalSelectedCount (hD := hD) P) = i.val := by omega
    simpa only [Bool.false_eq_true, ite_false, ha] using he

end SkewCornerDescent.Matrix.SelectedCoordinate
