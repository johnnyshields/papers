/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalWindowZeroBlocks

/-!
# Row alignment of congruent complete end windows

Supports `shields-2026-skew-corner-descent.tex` (`lem:shared-core`,
`eq:residue-match`). Literal upper and lower windows produce their translations
and parent-prefix/suffix row alignment. No beta-list correspondence is assumed.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

/-- The two complete end windows force the actual row displacement of their
congruence. Their translations are produced from literal cell equality. -/
theorem originalWindow_row_alignment {n k : ℕ} (P : Profile n) (W : Profile k)
    (q : ℤ) (v z : ℤ × ℤ) (hqtop : q < P.xi 0)
    (hwindow : P.cells.filter (fun x => q ≤ content x ∧ content x < P.xi 0) =
      translate v (P.cells.filter fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hW : translate z W.cells = P.cells.filter
      (fun x => 0 ≤ content x ∧ content x < P.xi 0 - q)) :
    k ≤ n ∧ z.1 = (n : ℤ) - k ∧ v.1 = (k : ℤ) - n ∧ content z = 0 := by
  have hlower : W.cells = translate (-z) (P.cells.filter
      (fun x => 0 ≤ content x ∧ content x < P.xi 0 - q)) := by
    rw [← hW, translate_translate, neg_add_cancel, translate_zero]
  have hupper : W.cells = translate (-(v + z)) (P.cells.filter
      (fun x => q ≤ content x ∧ content x < P.xi 0)) := by
    rw [hwindow, ← hW, translate_translate, translate_translate,
      add_assoc, neg_add_cancel, translate_zero]
  have hhi : 0 < P.xi 0 - q := by omega
  obtain ⟨hn, hz⟩ := originalLiteralWindow_lower_row_offset P W (P.xi 0 - q)
    (-z) hhi hlower
  have hv := (originalLiteralWindow_upper_row_offset P W q (-(v + z)) hqtop hupper).2
  have hc := originalLiteralWindow_lower_shift P W (P.xi 0 - q) (-z) hhi hlower
  simp only [Prod.fst_neg, Prod.fst_add] at hz hv
  dsimp only [content, Prod.fst_neg, Prod.snd_neg] at hc ⊢
  exact ⟨hn, by omega, by omega, by omega⟩

/-- The complete lower window's corner matrix is literally the parent's suffix
corner matrix. Its clipped top endpoint is outside the retained core. -/
theorem originalLiteralWindow_lower_corner_matrix {n m : ℕ} (P : Profile n) (Q : Profile m)
    (hi : ℤ) (v : ℤ × ℤ) (hhi : 0 < hi)
    (hwindow : Q.cells = translate v (P.cells.filter fun x => 0 ≤ content x ∧ content x < hi)) :
    ∃ h : m ≤ n,
      jtMatrix (fun j : Fin m => Q.xi j.succ) (fun j => Q.zeta j.castSucc) =
        jtMatrix (fun j : Fin m => P.xi ⟨n - m + j.val + 1, by
          have := j.isLt; omega⟩)
          (fun j => P.zeta ⟨n - m + j.val, by have := j.isLt; omega⟩) := by
  obtain ⟨hn, hx⟩ := originalLiteralWindow_lower_core_xi P Q hi v hhi hwindow
  obtain ⟨_, hz⟩ := originalLiteralWindow_lower_zeta P Q hi v hhi hwindow
  refine ⟨hn, ?_⟩
  ext i j
  simp only [jtMatrix, Matrix.of_apply, hx i, hz j.castSucc, Fin.val_castSucc]

/-- The complete upper window's corner matrix is literally the parent's prefix
corner matrix. The common translation cancels entrywise, not only in its determinant. -/
theorem originalLiteralWindow_upper_corner_matrix {n m : ℕ} (P : Profile n) (Q : Profile m)
    (lo : ℤ) (v : ℤ × ℤ) (hlo : lo < P.xi 0)
    (hwindow : Q.cells = translate v
      (P.cells.filter fun x => lo ≤ content x ∧ content x < P.xi 0)) :
    ∃ h : m ≤ n,
      jtMatrix (fun j : Fin m => Q.xi j.succ) (fun j => Q.zeta j.castSucc) =
        jtMatrix (fun j : Fin m => P.xi ⟨j.val + 1, by have := j.isLt; omega⟩)
          (fun j => P.zeta ⟨j.val, by have := j.isLt; omega⟩) := by
  obtain ⟨hn, he⟩ := originalLiteralWindow_upper_endpoints P Q lo v hlo hwindow
  obtain ⟨_, hz⟩ := originalLiteralWindow_upper_core_zeta P Q lo v hlo hwindow
  refine ⟨hn, ?_⟩
  ext i j
  simp only [jtMatrix, Matrix.of_apply, (he i.succ).2, hz j, Fin.val_succ,
    add_sub_add_right_eq_sub]

end SkewCornerDescent.Matrix.SelectedCoordinate
