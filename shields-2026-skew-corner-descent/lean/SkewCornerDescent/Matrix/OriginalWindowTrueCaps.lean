/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalTrueCapEntries
import SkewCornerDescent.Matrix.OriginalWindowLowerCapResponse
import SkewCornerDescent.Matrix.OriginalWindowLowerRanks
import SkewCornerDescent.Matrix.OriginalWindowRestrictionRanks
import SkewCornerDescent.Matrix.OriginalWindowRestrictionWord

/-!
# Canonical true exterior germs of complete literal end windows

Supports `shields-2026-skew-corner-descent.tex` (`lem:actual-words`). Complete
window geometry produces the canonical first and last source ranks. Both true cap
germs retain all original endpoint positions and inverse corrections. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The true upper exterior entry of a complete window equals the actual source entry. -/
theorem originalWindow_true_left_response {n m : ℕ} (P : Profile n) (Q : Profile m)
    (q : ℤ) (v : ℤ × ℤ)
    (hwindow : Q.cells = translate v
      (P.cells.filter fun x => q ≤ content x ∧ content x < P.xi 0))
    (hq : ∀ x ∈ diagramInterior P.cells, content x ≠ q)
    (hL : ∀ x ∈ diagramInterior P.cells, content x ≠ P.xi 0)
    (hQ : 0 < originalSelectedCount (hD := hD) Q) :
    c.originalHessenbergResponse Q 0 0 = c.originalHessenbergResponse P 0 0 := by
  have hc := originalLiteralWindow_selected_count_le (hD := hD) P Q q (P.xi 0) v
    hwindow hq hL
  have hP : 0 < originalSelectedCount (hD := hD) P := hQ.trans_le hc
  let i : Fin (originalSelectedCount (hD := hD) Q) := ⟨0, hQ⟩
  obtain ⟨j, hj, hb, he⟩ := originalWindow_restriction_selected_rank P Q q v hwindow hq hL i
  have hj0 : j = ⟨0, hP⟩ := Fin.ext hj
  let EP := originalSelectedEnumeration (hD := hD) P
  let EQ := originalSelectedEnumeration (hD := hD) Q
  have hr := c.originalWindow_upper_cap_response P Q q v hwindow hq hL (EP j) (EQ i)
    (Or.inl ⟨originalBlockSelected_nonempty P (EP j).val (EP j).property, hb⟩) he
  rw [hj0] at hr
  rw [c.originalHessenberg_true_left_eq_local Q hQ, c.originalHessenberg_true_left_eq_local P hP]
  exact hr

/-- The true lower exterior entry of a complete window equals the actual source entry. -/
theorem originalWindow_true_right_response {n m : ℕ} (P : Profile n) (Q : Profile m)
    (q : ℤ) (v : ℤ × ℤ)
    (hwindow : Q.cells = translate v
      (P.cells.filter fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (h0 : ∀ x ∈ diagramInterior P.cells, content x ≠ 0)
    (hLq : ∀ x ∈ diagramInterior P.cells, content x ≠ P.xi 0 - q)
    (hQ : 0 < originalSelectedCount (hD := hD) Q) :
    c.originalHessenbergResponse Q (Fin.last _) (Fin.last _) =
      c.originalHessenbergResponse P (Fin.last _) (Fin.last _) := by
  have hc := originalLiteralWindow_selected_count_le (hD := hD) P Q 0 (P.xi 0 - q) v
    hwindow h0 hLq
  have hP : 0 < originalSelectedCount (hD := hD) P := hQ.trans_le hc
  let i : Fin (originalSelectedCount (hD := hD) Q) :=
    ⟨originalSelectedCount (hD := hD) Q - 1, by omega⟩
  obtain ⟨j, hj, hb, he⟩ := originalWindow_lower_restriction_selected_rank P Q q v
    hwindow h0 hLq i
  have hj0 : j = ⟨originalSelectedCount (hD := hD) P - 1, by omega⟩ := by
    apply Fin.ext
    change j.val = originalSelectedCount (hD := hD) P - 1
    change j.val = originalSelectedCount (hD := hD) Q - 1 +
      (originalSelectedCount (hD := hD) P - originalSelectedCount (hD := hD) Q) at hj
    omega
  let EP := originalSelectedEnumeration (hD := hD) P
  let EQ := originalSelectedEnumeration (hD := hD) Q
  have hr := c.originalWindow_lower_cap_response P Q (P.xi 0 - q) v hwindow h0 hLq
    (EP j) (EQ i) (Or.inl
      ⟨originalBlockSelected_nonempty P (EP j).val (EP j).property, hb⟩) he
  rw [hj0] at hr
  rw [c.originalHessenberg_true_right_eq_local Q hQ,
    c.originalHessenberg_true_right_eq_local P hP]
  exact hr

end SkewCornerDescent.Matrix.SelectedCoordinate
