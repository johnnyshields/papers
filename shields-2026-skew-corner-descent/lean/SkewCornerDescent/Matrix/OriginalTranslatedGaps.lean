/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.OriginalClosureGaps
import SkewCornerDescent.Matrix.OriginalWindowLowerWord

/-!
# Internal gap distances of complete translated selected components

Supports `shields-2026-skew-corner-descent.tex` (`lem:actual-words`). Consecutive complete
selected occurrences determine their actual gap by their least contents. Literal end
windows supply the translated occurrences and their rank offsets. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

include c

/-- A complete translated pair preserves its actual intervening gap distance. -/
theorem originalInternalDistance_of_translated_cells {n m : ℕ}
    (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (a b : Fin (originalSelectedCount (hD := hD) P)) (hab : a.val + 1 = b.val)
    (qa qb : Fin (originalSelectedCount (hD := hD) Q)) (hqab : qa.val + 1 = qb.val)
    (ha : translate v (interiorBlockCells P (originalSelectedEnumeration P a).val.val) =
      interiorBlockCells Q (originalSelectedEnumeration Q qa).val.val)
    (hb : translate v (interiorBlockCells P (originalSelectedEnumeration P b).val.val) =
      interiorBlockCells Q (originalSelectedEnumeration Q qb).val.val) :
    originalHessenbergDistance (hD := hD) Q qa.succ qa.succ =
      originalHessenbergDistance (hD := hD) P a.succ a.succ := by
  have hza := originalSelected_minContent_of_translated_cells P Q
    (originalSelectedEnumeration P a) (originalSelectedEnumeration Q qa) v 0
    (by simpa only [translate_zero] using ha.symm)
  have hzb := originalSelected_minContent_of_translated_cells P Q
    (originalSelectedEnumeration P b) (originalSelectedEnumeration Q qb) v 0
    (by simpa only [translate_zero] using hb.symm)
  rw [c.originalHessenbergDistance_between Q qa qb hqab,
    c.originalHessenbergDistance_between P a b hab]
  simp only [content, Prod.fst_zero, Prod.snd_zero, sub_self, add_zero] at hza hzb
  omega

/-- A literal lower end window has the final source gap word, at its actual rank offset. -/
theorem originalWindow_lower_internal_distance {n m : ℕ} (P : Profile n) (Q : Profile m)
    (q : ℤ) (v : ℤ × ℤ)
    (hwindow : Q.cells = translate v
      (P.cells.filter fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hq : ∀ x ∈ diagramInterior P.cells, content x ≠ 0)
    (hL : ∀ x ∈ diagramInterior P.cells, content x ≠ P.xi 0 - q)
    (i : Fin (originalSelectedCount (hD := hD) Q - 1)) :
    ∃ a : Fin (originalSelectedCount (hD := hD) P),
      a.val = i.val + (originalSelectedCount (hD := hD) P -
        originalSelectedCount (hD := hD) Q) ∧
      originalHessenbergDistance (hD := hD) Q
        (⟨i.val, by have := i.isLt; omega⟩ : Fin _).succ
        (⟨i.val, by have := i.isLt; omega⟩ : Fin _).succ =
      originalHessenbergDistance (hD := hD) P a.succ a.succ := by
  let qa : Fin (originalSelectedCount (hD := hD) Q) := ⟨i.val, by have := i.isLt; omega⟩
  let qb : Fin (originalSelectedCount (hD := hD) Q) := ⟨i.val + 1, by have := i.isLt; omega⟩
  obtain ⟨a, ha, _, hea⟩ := originalWindow_lower_restriction_selected_rank
    P Q q v hwindow hq hL qa
  obtain ⟨b, hb, _, heb⟩ := originalWindow_lower_restriction_selected_rank
    P Q q v hwindow hq hL qb
  refine ⟨a, ha, ?_⟩
  exact c.originalInternalDistance_of_translated_cells P Q v a b
    (by dsimp only [qa, qb] at ha hb; omega) qa qb rfl hea heb

/-- A literal upper end window has the initial source gap word, without a rank shift. -/
theorem originalWindow_upper_internal_distance {n m : ℕ} (P : Profile n) (Q : Profile m)
    (q : ℤ) (v : ℤ × ℤ)
    (hwindow : Q.cells = translate v
      (P.cells.filter fun x => q ≤ content x ∧ content x < P.xi 0))
    (hq : ∀ x ∈ diagramInterior P.cells, content x ≠ q)
    (hL : ∀ x ∈ diagramInterior P.cells, content x ≠ P.xi 0)
    (i : Fin (originalSelectedCount (hD := hD) Q - 1)) :
    ∃ a : Fin (originalSelectedCount (hD := hD) P), a.val = i.val ∧
      originalHessenbergDistance (hD := hD) Q
        (⟨i.val, by have := i.isLt; omega⟩ : Fin _).succ
        (⟨i.val, by have := i.isLt; omega⟩ : Fin _).succ =
      originalHessenbergDistance (hD := hD) P a.succ a.succ := by
  let qa : Fin (originalSelectedCount (hD := hD) Q) := ⟨i.val, by have := i.isLt; omega⟩
  let qb : Fin (originalSelectedCount (hD := hD) Q) := ⟨i.val + 1, by have := i.isLt; omega⟩
  obtain ⟨a, ha, _, hea⟩ := originalWindow_restriction_selected_rank
    P Q q v hwindow hq hL qa
  obtain ⟨b, hb, _, heb⟩ := originalWindow_restriction_selected_rank
    P Q q v hwindow hq hL qb
  refine ⟨a, ha, ?_⟩
  exact c.originalInternalDistance_of_translated_cells P Q v a b
    (by dsimp only [qa, qb] at ha hb; omega) qa qb rfl hea heb

end SkewCornerDescent.Matrix.SelectedCoordinate
