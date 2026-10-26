/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalWindowFrameZeros
import SkewCornerDescent.Matrix.OriginalWindowRowAlignment

/-!
# Identifying original window cores in compatible matrix frames

Supports `shields-2026-skew-corner-descent.tex` (`lem:shared-core`,
`eq:residue-match`). The complete literal windows identify the extracted core
entrywise with their genuine Jacobi--Trudi corner matrix. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

/-- The lower window's literal corner is the whole source frame's extracted core. -/
theorem originalLowerWindow_frame_core {n : ℕ} (P : Profile n) (a b : ℕ)
    (W : Profile (b + 1)) (hi : ℤ) (v : ℤ × ℤ) (hhi : 0 < hi)
    (hwindow : W.cells = translate v (P.cells.filter fun x => 0 ≤ content x ∧ content x < hi))
    (hsize : n = a + (b + 1)) :
    (originalProfileFrame P a b 0 (by omega)).submatrix
        (fun i => .inr (.inl i))
        (fun j => commonCoreColumnEquiv (Fin a) (Fin b) (Fin 0) (.inr (.inl j))) =
      (jtMatrix (fun j : Fin (b + 1) => W.xi j.succ) (fun j => W.zeta j.castSucc)).submatrix
        (commonCoreFinEquiv b) (commonCoreFinEquiv b) := by
  obtain ⟨hn, hC⟩ := originalLiteralWindow_lower_corner_matrix P W hi v hhi hwindow
  apply Matrix.ext
  intro i j
  have hd : n + 1 = a + 1 + (b + 1 + 0) := by omega
  let row := (commonCoreFiniteRows a b 0).trans (finCongr hd.symm)
  let col := (commonCoreFiniteCols a b 0).trans (finCongr hd.symm)
  have hr : (row (.inr (.inl i))).val = a + 1 + (commonCoreFinEquiv b i).val := by
    change (commonCoreFiniteRows a b 0 (.inr (.inl i))).val = _
    exact commonCoreFiniteRows_core a b 0 i
  have hc : (col (commonCoreColumnEquiv (Fin a) (Fin b) (Fin 0) (.inr (.inl j)))).val =
      a + (commonCoreFinEquiv b j).val := by
    change (commonCoreFiniteCols a b 0
      (commonCoreColumnEquiv (Fin a) (Fin b) (Fin 0) (.inr (.inl j)))).val = _
    exact commonCoreFiniteCols_core a b 0 j
  have hrow : row (.inr (.inl i)) =
      ⟨n - (b + 1) + (commonCoreFinEquiv b i).val + 1, by
        have := (commonCoreFinEquiv b i).isLt; omega⟩ := by
    apply Fin.ext
    change (row (.inr (.inl i))).val = n - (b + 1) + (commonCoreFinEquiv b i).val + 1
    omega
  have hcol : col (commonCoreColumnEquiv (Fin a) (Fin b) (Fin 0) (.inr (.inl j))) =
      ⟨n - (b + 1) + (commonCoreFinEquiv b j).val, by
        have := (commonCoreFinEquiv b j).isLt; omega⟩ := by
    apply Fin.ext
    change (col (commonCoreColumnEquiv (Fin a) (Fin b) (Fin 0) (.inr (.inl j)))).val =
      n - (b + 1) + (commonCoreFinEquiv b j).val
    omega
  have he := congrArg (fun M => M (commonCoreFinEquiv b i) (commonCoreFinEquiv b j)) hC
  simp only [jtMatrix, Matrix.of_apply] at he
  change hh (P.xi (row (.inr (.inl i))) -
      P.zeta (col (commonCoreColumnEquiv (Fin a) (Fin b) (Fin 0) (.inr (.inl j))))) = _
  rw [hrow, hcol]
  exact he.symm

/-- The upper window's literal corner is the whole source frame's extracted core;
the actual translation cancels in every entry. -/
theorem originalUpperWindow_frame_core {n : ℕ} (P : Profile n) (a b : ℕ)
    (W : Profile (b + 1)) (lo : ℤ) (v : ℤ × ℤ) (hlo : lo < P.xi 0)
    (hwindow : W.cells = translate v
      (P.cells.filter fun x => lo ≤ content x ∧ content x < P.xi 0))
    (hsize : n = a + (b + 1)) :
    (originalProfileFrame P 0 b a (by omega)).submatrix
        (fun i => .inr (.inl i))
        (fun j => commonCoreColumnEquiv (Fin 0) (Fin b) (Fin a) (.inr (.inl j))) =
      (jtMatrix (fun j : Fin (b + 1) => W.xi j.succ) (fun j => W.zeta j.castSucc)).submatrix
        (commonCoreFinEquiv b) (commonCoreFinEquiv b) := by
  obtain ⟨hn, hC⟩ := originalLiteralWindow_upper_corner_matrix P W lo v hlo hwindow
  apply Matrix.ext
  intro i j
  have hd : n + 1 = 0 + 1 + (b + 1 + a) := by omega
  let row := (commonCoreFiniteRows 0 b a).trans (finCongr hd.symm)
  let col := (commonCoreFiniteCols 0 b a).trans (finCongr hd.symm)
  have hr : (row (.inr (.inl i))).val = 1 + (commonCoreFinEquiv b i).val := by
    change (commonCoreFiniteRows 0 b a (.inr (.inl i))).val = _
    simpa only [Nat.zero_add] using commonCoreFiniteRows_core 0 b a i
  have hc : (col (commonCoreColumnEquiv (Fin 0) (Fin b) (Fin a) (.inr (.inl j)))).val =
      (commonCoreFinEquiv b j).val := by
    change (commonCoreFiniteCols 0 b a
      (commonCoreColumnEquiv (Fin 0) (Fin b) (Fin a) (.inr (.inl j)))).val = _
    simpa only [Nat.zero_add] using commonCoreFiniteCols_core 0 b a j
  have hrow : row (.inr (.inl i)) = ⟨(commonCoreFinEquiv b i).val + 1, by
      have := (commonCoreFinEquiv b i).isLt; omega⟩ := by
    apply Fin.ext
    change (row (.inr (.inl i))).val = (commonCoreFinEquiv b i).val + 1
    omega
  have hcol : col (commonCoreColumnEquiv (Fin 0) (Fin b) (Fin a) (.inr (.inl j))) =
      ⟨(commonCoreFinEquiv b j).val, by have := (commonCoreFinEquiv b j).isLt; omega⟩ :=
    Fin.ext hc
  have he := congrArg (fun M => M (commonCoreFinEquiv b i) (commonCoreFinEquiv b j)) hC
  simp only [jtMatrix, Matrix.of_apply] at he
  change hh (P.xi (row (.inr (.inl i))) -
      P.zeta (col (commonCoreColumnEquiv (Fin 0) (Fin b) (Fin a) (.inr (.inl j))))) = _
  rw [hrow, hcol]
  exact he.symm

end SkewCornerDescent.Matrix.SelectedCoordinate
