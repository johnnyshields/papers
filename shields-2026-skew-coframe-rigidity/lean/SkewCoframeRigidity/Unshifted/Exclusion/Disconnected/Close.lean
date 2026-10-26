/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCoframeRigidity.Unshifted.Exclusion.Disconnected.Facts

/-!
# The balanced closing configurations `M = 7, 8`

Formalizes `shields-2026-skew-coframe-rigidity.tex`, «Unshifted opposite-end exclusion»
(`ph:unshifted-exclusion`, disconnected corner, the closing step).  When both end components are
the two-cell row, the top proper row of `V` sits at `M - 1` over the column `M - 3`, the bottom
at `3` over the column `1`, and every intervening position lies in `[4, M - 4]`; for `M = 7, 8`
the board is its own half-turn.
-/

namespace SkewCoframeRigidity.Unshifted

open SkewCofactorIndependence SkewCoframeRigidity.Coframe SkewCoframeRigidity Polynomial
open scoped Polynomial Matrix

variable {n : ℕ}

theorem small_closure {V W : BetaDiagram (n + 1)} {c0 : ℤ}
    (hr : ∀ i, W.row i = c0 - V.col i.rev) (hc : ∀ i, W.col i = c0 - V.row i.rev)
    (hVn : V.col (Fin.last n) = 0) (hWn : W.col (Fin.last n) = 0) (hn : 1 < n)
    (hM : span V = 7 ∨ span V = 8)
    (hbV : ∀ i : Fin n, blockIdx V i = 0 ↔ i.val < 1)
    (hbW : ∀ i : Fin n, blockIdx W i = 0 ↔ i.val < 1)
    (hVA : colPos V ⟨0, by omega⟩ = span V - 3) (hWA : colPos W ⟨0, by omega⟩ = span V - 3)
    (hVp : rowPos V ⟨0, by omega⟩ + 1 = span V) (hWp : rowPos W ⟨0, by omega⟩ + 1 = span V) :
    V.Symmetric := by
  have hspan : span W = span V := span_rot hr hc hWn
  set M := span V with hMdef
  have cV := top_cut V hVn 1 hbV one_pos hn
  have cW := top_cut W hWn 1 hbW one_pos hn
  have cV' : rowPos V ⟨1, hn⟩ < M - 3 := by
    have e : colPos V ⟨1 - 1, by omega⟩ = M - 3 := hVA
    have := cV.2; rw [e] at this; exact this
  have cW' : rowPos W ⟨1, hn⟩ < M - 3 := by
    have e : colPos W ⟨1 - 1, by omega⟩ = M - 3 := hWA
    have := cW.2; rw [e] at this; exact this
  have rev0 : (⟨0, by omega⟩ : Fin n).rev = ⟨n - 1, by omega⟩ := by ext; simp [Fin.val_rev]
  have hlast_row : rowPos V ⟨n - 1, by omega⟩ = 3 := by
    have := colPos_rot hc hWn ⟨0, by omega⟩
    rw [rev0, hWA] at this
    have := rowPos_lt_span V ⟨n - 1, by omega⟩
    omega
  have hlast_col : colPos V ⟨n - 1, by omega⟩ = 1 := by
    have := rowPos_rot hr hc hWn ⟨0, by omega⟩
    rw [rev0] at this
    have := colPos_lt_span V ⟨n - 1, by omega⟩
    omega
  -- monotonicity of the positions
  have rowMono : ∀ i j : Fin n, i ≤ j → rowPos V j ≤ rowPos V i := fun i j hij => by
    have := V.row_strictAnti.antitone (Fin.succ_le_succ_iff.mpr hij)
    have a := rowPos_cast V i
    have b := rowPos_cast V j
    have : (rowPos V j : ℤ) ≤ rowPos V i := by omega
    exact_mod_cast this
  have colMono : ∀ i j : Fin n, i ≤ j → colPos V j ≤ colPos V i := fun i j hij => by
    have := V.col_strictAnti.antitone (Fin.castSucc_le_castSucc_iff.mpr hij)
    have a := colPos_cast V i
    have b := colPos_cast V j
    have : (colPos V j : ℤ) ≤ colPos V i := by omega
    exact_mod_cast this
  have rowMonoW : ∀ i j : Fin n, i ≤ j → rowPos W j ≤ rowPos W i := fun i j hij => by
    have := W.row_strictAnti.antitone (Fin.succ_le_succ_iff.mpr hij)
    have a := rowPos_cast W i
    have b := rowPos_cast W j
    have : (rowPos W j : ℤ) ≤ rowPos W i := by omega
    exact_mod_cast this
  have rowLt : ∀ i j : Fin n, i < j → rowPos V j < rowPos V i := fun i j hij => by
    have := V.row_strictAnti (Fin.succ_lt_succ_iff.mpr hij)
    have a := rowPos_cast V i
    have b := rowPos_cast V j
    have : (rowPos V j : ℤ) < rowPos V i := by omega
    exact_mod_cast this
  have colLt : ∀ i j : Fin n, i < j → colPos V j < colPos V i := fun i j hij => by
    have := V.col_strictAnti (Fin.castSucc_lt_castSucc_iff.mpr hij)
    have a := colPos_cast V i
    have b := colPos_cast V j
    have : (colPos V j : ℤ) < colPos V i := by omega
    exact_mod_cast this
  -- row positions
  have hrowpos : ∀ k : Fin n, rowPos V k = M - 1 ∨ rowPos V k = 3 ∨
      (4 ≤ rowPos V k ∧ rowPos V k ≤ M - 4) := by
    intro k
    by_cases h0 : k.val = 0
    · left
      have : k = ⟨0, by omega⟩ := Fin.ext h0
      rw [this]; omega
    · by_cases h1 : k.val = n - 1
      · right; left
        have : k = ⟨n - 1, by omega⟩ := Fin.ext h1
        rw [this]; exact hlast_row
      · right; right
        have a := rowMono ⟨1, hn⟩ k (by rw [Fin.le_iff_val_le_val]; simp; omega)
        have b := rowLt k ⟨n - 1, by omega⟩ (by rw [Fin.lt_def]; simp; omega)
        omega
  have hcolpos : ∀ k : Fin n, colPos V k = M - 3 ∨ colPos V k = 1 ∨
      (4 ≤ colPos V k ∧ colPos V k ≤ M - 4) := by
    intro k
    by_cases h0 : k.val = 0
    · left
      have : k = ⟨0, by omega⟩ := Fin.ext h0
      rw [this]; omega
    · by_cases h1 : k.val = n - 1
      · right; left
        have : k = ⟨n - 1, by omega⟩ := Fin.ext h1
        rw [this]; exact hlast_col
      · right; right
        have a := colLt ⟨0, by omega⟩ k (by rw [Fin.lt_def]; simp; omega)
        have b := rowPos_rot hr hc hWn k.rev
        rw [Fin.rev_rev] at b
        have c := rowMonoW ⟨1, hn⟩ k.rev (by rw [Fin.le_iff_val_le_val]; simp [Fin.val_rev]; omega)
        have d := rowPos_lt_span V ⟨0, by omega⟩
        omega
  have h0 := row_zero_eq V hVn
  have hMz : ((span V : ℕ) : ℤ) = 7 ∨ ((span V : ℕ) : ℤ) = 8 := by
    rcases hM with h | h
    · left; exact_mod_cast h
    · right; exact_mod_cast h
  refine balanced_flag_symmetric (span V : ℤ) hMz V hVn h0 ?_ ?_ ?_ ?_ ?_ ?_
  · intro i hi
    induction i using Fin.cases with
    | zero => exact absurd rfl hi
    | succ k =>
      rw [row_succ_eq V hVn k]
      rcases hrowpos k with h | h | ⟨h1, h2⟩
      · left; omega
      · right; left; omega
      · right; right; omega
  · intro j hj
    induction j using Fin.lastCases with
    | last => exact absurd rfl hj
    | cast k =>
      rw [col_castSucc_eq V hVn k]
      rcases hcolpos k with h | h | ⟨h1, h2⟩
      · left; omega
      · right; left; omega
      · right; right; omega
  · exact ⟨(⟨0, by omega⟩ : Fin n).succ, by rw [row_succ_eq V hVn]; omega⟩
  · exact ⟨(⟨n - 1, by omega⟩ : Fin n).succ, by rw [row_succ_eq V hVn, hlast_row]; norm_num⟩
  · exact ⟨(⟨0, by omega⟩ : Fin n).castSucc, by rw [col_castSucc_eq V hVn]; omega⟩
  · exact ⟨(⟨n - 1, by omega⟩ : Fin n).castSucc, by rw [col_castSucc_eq V hVn, hlast_col]; norm_num⟩

end SkewCoframeRigidity.Unshifted
