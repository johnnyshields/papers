/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalVerticalClosureEnumeration
import SkewCornerDescent.Matrix.OriginalVerticalEndLogLocality
import SkewCornerDescent.Matrix.OriginalWindowOrderedResponses
import SkewCornerDescent.Matrix.OriginalWindowOrderedLowerResponses

/-!
# Complete ordered response matrices in the actual vertical copies

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
Both complete literal end windows preserve every ordered response and its
whole removed inverse. Only the crossing interval contains the extra join vertex.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Every ordered between-occurrence response inside either actual vertical
copy is its complete source response, at its original canonical endpoint ranks. -/
theorem originalVerticalClosure_ordered_response {n m : ℕ}
    (P : Profile n) (Q : Profile m) (z : ℤ × ℤ)
    (hQ : originalVerticalClosure P = translate z Q.cells) (upper : Bool)
    (i j : Fin (originalSelectedCount (hD := hD) P)) :
    c.originalHessenbergResponse Q
      (originalVerticalClosureSelectedIndex P Q z hQ upper i).succ
      (originalVerticalClosureSelectedIndex P Q z hQ upper j).castSucc =
      c.originalHessenbergResponse P i.succ j.castSucc := by
  have htop := originalVerticalClosure_profile_top P Q z hQ
  have hjoin := originalVerticalClosure_profile_join_no_interior P Q z hQ
  have h0 := (originalProfile_interior_boundary_gaps Q).1
  have hL := (originalProfile_interior_boundary_gaps Q).2
  have hmid : ∀ x ∈ diagramInterior Q.cells, content x ≠ Q.xi 0 - P.xi 0 := by
    rw [htop, show 2 * P.xi 0 - P.xi 0 = P.xi 0 by ring]
    exact hjoin
  cases upper with
  | true =>
    have hwindow : P.cells = translate (z - (vH P.cells - eCell))
        (Q.cells.filter fun x => P.xi 0 ≤ content x ∧ content x < Q.xi 0) := by
      rw [htop, originalVerticalClosure_upper_window P Q z hQ, translate_translate,
        show z - (vH P.cells - eCell) + (vH P.cells - eCell - z) = 0 by abel,
        translate_zero]
    obtain ⟨_, he⟩ := c.originalWindow_upper_ordered_responses Q P (P.xi 0)
      (z - (vH P.cells - eCell)) hwindow hjoin hL
    simpa only [originalVerticalClosureSelectedIndex, ite_true, zero_add] using (he i j).symm
  | false =>
    have hwindow : P.cells = translate z
        (Q.cells.filter fun x => 0 ≤ content x ∧ content x < Q.xi 0 - P.xi 0) := by
      rw [htop, show 2 * P.xi 0 - P.xi 0 = P.xi 0 by ring,
        originalVerticalClosure_lower_window P Q z hQ, translate_translate,
        add_neg_cancel, translate_zero]
    obtain ⟨_, he⟩ := c.originalWindow_lower_ordered_responses Q P (P.xi 0) z
      hwindow h0 hmid
    have hcount := originalVerticalClosure_profile_selected_count (hD := hD) P Q z hQ
    have hshift : originalSelectedCount (hD := hD) Q - originalSelectedCount (hD := hD) P =
        originalSelectedCount (hD := hD) P := by omega
    simpa only [originalVerticalClosureSelectedIndex, Bool.false_eq_true, ite_false,
      hshift, Nat.add_comm] using (he i j).symm

end SkewCornerDescent.Matrix.SelectedCoordinate
