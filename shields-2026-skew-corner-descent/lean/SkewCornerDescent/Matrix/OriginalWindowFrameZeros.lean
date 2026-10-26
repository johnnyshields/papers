/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalProfileFrame
import SkewCornerDescent.Matrix.OriginalWindowZeroBlocks

/-!
# Original end-window zero blocks in compatible frames

Supports `shields-2026-skew-corner-descent.tex` (`lem:shared-core`,
`eq:residue-match`). Literal profile windows supply the zero rectangles in the
full original matrix's actual compatible row and column frame. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

/-- A complete lower window supplies the left/core zero rectangle in the whole
source matrix's compatible frame, including every zero-gap boundary. -/
theorem originalLowerWindow_frame_zero {n : ℕ} (P : Profile n) (a b : ℕ)
    (W : Profile (b + 1)) (hi : ℤ) (v : ℤ × ℤ) (hhi : 0 < hi)
    (hwindow : W.cells = translate v (P.cells.filter fun x => 0 ≤ content x ∧ content x < hi))
    (hsize : n = a + (b + 1)) :
    ∀ (i : Unit ⊕ Fin b) (j : Fin a),
      originalProfileFrame P a b 0 (by omega) (.inr (.inl i))
        (commonCoreColumnEquiv (Fin a) (Fin b) (Fin 0) (.inl j)) = 0 := by
  obtain ⟨hn, hz⟩ := originalLiteralWindow_lower_core_zero P W hi v hhi hwindow
  intro i j
  have hd : n + 1 = a + 1 + (b + 1 + 0) := by omega
  let row := (commonCoreFiniteRows a b 0).trans (finCongr hd.symm)
  let col := (commonCoreFiniteCols a b 0).trans (finCongr hd.symm)
  change hh (P.xi (row (.inr (.inl i))) - P.zeta (col (.inl (.inl j)))) = 0
  have hr : (row (.inr (.inl i))).val = a + 1 + (commonCoreFinEquiv b i).val := by
    change (commonCoreFiniteRows a b 0 (.inr (.inl i))).val = _
    exact commonCoreFiniteRows_core a b 0 i
  have hc : (col (.inl (.inl j))).val = j.val := by
    change (commonCoreFiniteCols a b 0 (.inl (.inl j))).val = _
    exact commonCoreFiniteCols_left a b 0 j
  have hrow : row (.inr (.inl i)) =
      ⟨n - (b + 1) + (commonCoreFinEquiv b i).val + 1, by
        have := (commonCoreFinEquiv b i).isLt; omega⟩ := by
    apply Fin.ext
    change (row (.inr (.inl i))).val = n - (b + 1) + (commonCoreFinEquiv b i).val + 1
    omega
  have hcol : col (.inl (.inl j)) = ⟨j.val, by have := j.isLt; omega⟩ := Fin.ext hc
  rw [hrow, hcol]
  exact hz ⟨j.val, by have := j.isLt; omega⟩ (commonCoreFinEquiv b i) (by
    have := j.isLt; omega)

/-- A complete upper window supplies the right/core zero rectangle in the whole
source matrix's compatible frame. The right-splice column is not declared zero. -/
theorem originalUpperWindow_frame_zero {n : ℕ} (P : Profile n) (a b : ℕ)
    (W : Profile (b + 1)) (lo : ℤ) (v : ℤ × ℤ) (hlo : lo < P.xi 0)
    (hwindow : W.cells = translate v
      (P.cells.filter fun x => lo ≤ content x ∧ content x < P.xi 0))
    (hsize : n = a + (b + 1)) :
    ∀ (i : Fin a) (j : Unit ⊕ Fin b),
      originalProfileFrame P 0 b a (by omega) (.inr (.inr i))
        (commonCoreColumnEquiv (Fin 0) (Fin b) (Fin a) (.inr (.inl j))) = 0 := by
  obtain ⟨hn, hz⟩ := originalLiteralWindow_upper_core_zero P W lo v hlo hwindow
  intro i j
  have hd : n + 1 = 0 + 1 + (b + 1 + a) := by omega
  let row := (commonCoreFiniteRows 0 b a).trans (finCongr hd.symm)
  let col := (commonCoreFiniteCols 0 b a).trans (finCongr hd.symm)
  change hh (P.xi (row (.inr (.inr i))) -
    P.zeta (col (commonCoreColumnEquiv (Fin 0) (Fin b) (Fin a) (.inr (.inl j))))) = 0
  have hr : (row (.inr (.inr i))).val = 1 + (b + 1 + i.val) := by
    change (commonCoreFiniteRows 0 b a (.inr (.inr i))).val = _
    simpa only [Nat.zero_add] using commonCoreFiniteRows_right 0 b a i
  have hc : (col (commonCoreColumnEquiv (Fin 0) (Fin b) (Fin a) (.inr (.inl j)))).val =
      (commonCoreFinEquiv b j).val := by
    rcases j with u | j
    · cases u
      change (commonCoreFiniteCols 0 b a (.inl (.inr ()))).val = 0
      exact commonCoreFiniteCols_top 0 b a
    · change (commonCoreFiniteCols 0 b a (.inr (.inl (.inr j)))).val = j.val + 1
      have he := commonCoreFiniteCols_tail 0 b a j
      omega
  have hcol : col (commonCoreColumnEquiv (Fin 0) (Fin b) (Fin a) (.inr (.inl j))) =
      ⟨(commonCoreFinEquiv b j).val, by have := (commonCoreFinEquiv b j).isLt; omega⟩ :=
    Fin.ext hc
  rw [hcol]
  exact hz (row (.inr (.inr i))) (commonCoreFinEquiv b j) (by omega)

end SkewCornerDescent.Matrix.SelectedCoordinate
