/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.OriginalClosureExterior

/-!
# Literal row placement of the horizontal closure

Supports `shields-2026-skew-corner-descent.tex` (`lem:actual-words`). The extreme cells of
a normalized source profile determine its complete horizontal displacement and the row
normalization of every actual closure profile. Sorry-free.
-/

namespace SkewCornerDescent.Matrix

open SkewGluing

/-- The actual northeast cell of a normalized profile is its first row's right endpoint. -/
theorem originalProfile_ne {n : ℕ} (P : Profile n) :
    ne P.cells = (0, P.xi 0 - 1) := by
  have hlo : diagLo P.cells (P.xi 0 - 1) = 0 := by
    apply diagLo_eq_of
    · simpa only [Fin.val_zero, Nat.cast_zero, zero_add, add_zero]
        using P.row_right_mem_cells 0
    · intro i hi
      exact (P.row_bounds_of_mem_cells hi).1
  unfold ne
  rw [Profile.maxContent_cells, hlo]
  simp only [zero_add]

/-- The actual southwest cell of a normalized profile is its last row's left endpoint. -/
theorem originalProfile_sw {n : ℕ} (P : Profile n) :
    sw P.cells = ((n : ℤ), (n : ℤ)) := by
  have hlo : diagLo P.cells 0 = n := by
    apply diagLo_eq_of
    · simpa only [P.zeta_last, Fin.val_last, zero_add, add_zero]
        using P.row_left_mem_cells (Fin.last n)
    · intro i hi
      obtain ⟨j, hj, hcols⟩ := P.mem_cells.mp hi
      have hz : P.zeta j ≤ 0 := by omega
      have hlast : n ≤ j.val := by
        by_contra h
        have hlt : j < Fin.last n := by change j.val < n; omega
        have hs := P.zeta_strictAnti hlt
        rw [P.zeta_last] at hs
        omega
      omega
  unfold sw
  rw [Profile.minContent_cells, hlo]
  simp only [add_zero]

/-- The complete geometric horizontal displacement, including its row coordinate. -/
theorem originalHorizontalDisplacement_pair {n : ℕ} (P : Profile n) :
    vH P.cells = (-(n : ℤ), P.xi 0 - n) := by
  unfold vH
  rw [originalProfile_ne, originalProfile_sw]
  ext <;> simp only [Prod.fst_add, Prod.fst_sub, Prod.snd_add, Prod.snd_sub]
  · omega
  · omega

/-- Every literal closure cell lies in the exact source-to-source row band. -/
theorem originalHorizontalClosure_row_bounds {n : ℕ} (P : Profile n)
    {x : ℤ × ℤ} (hx : x ∈ originalHorizontalClosure P) :
    -(n : ℤ) ≤ x.1 ∧ x.1 ≤ n := by
  rw [originalHorizontalClosure_cells] at hx
  rcases Finset.mem_union.mp hx with hx | hx
  · have h := P.row_bounds_of_mem_cells hx
    omega
  · have h := P.row_bounds_of_mem_cells (mem_translate.mp hx)
    rw [originalHorizontalDisplacement_pair] at h
    dsimp only at h
    omega

/-- A translated canonical closure profile has twice the source height and the exact
normalizing translation; no row-count or endpoint-matching data is assumed. -/
theorem originalHorizontalClosure_profile_rows {n m : ℕ}
    (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalHorizontalClosure P = translate v Q.cells) :
    m = 2 * n ∧ v = (-(n : ℤ), -(n : ℤ)) := by
  have h0 : ((0 : ℤ), Q.zeta 0) + v ∈ originalHorizontalClosure P := by
    rw [hQ]
    apply mem_translate.mpr
    simpa only [add_sub_cancel_right, Fin.val_zero, Nat.cast_zero, add_zero]
      using Q.row_left_mem_cells 0
  have hl : ((m : ℤ), (m : ℤ)) + v ∈ originalHorizontalClosure P := by
    rw [hQ]
    apply mem_translate.mpr
    simpa only [add_sub_cancel_right, Q.zeta_last, Fin.val_last, zero_add]
      using Q.row_left_mem_cells (Fin.last m)
  have hs : ((n : ℤ), (n : ℤ)) ∈ originalHorizontalClosure P := by
    rw [originalHorizontalClosure_cells]
    apply Finset.mem_union_left
    simpa only [P.zeta_last, Fin.val_last, zero_add]
      using P.row_left_mem_cells (Fin.last n)
  have ht : ((0 : ℤ), P.zeta 0) + vH P.cells ∈ originalHorizontalClosure P := by
    rw [originalHorizontalClosure_cells]
    apply Finset.mem_union_right
    apply mem_translate.mpr
    simpa only [add_sub_cancel_right, Fin.val_zero, Nat.cast_zero, add_zero]
      using P.row_left_mem_cells 0
  have hb0 := originalHorizontalClosure_row_bounds P h0
  have hbl := originalHorizontalClosure_row_bounds P hl
  rw [hQ] at hs ht
  have hbs := Q.row_bounds_of_mem_cells (mem_translate.mp hs)
  have hbt := Q.row_bounds_of_mem_cells (mem_translate.mp ht)
  rw [originalHorizontalDisplacement_pair] at hbt
  simp only [Prod.fst_add, zero_add] at hb0 hbl hbs hbt
  have hv0 : v.1 = -(n : ℤ) := by omega
  have hm : m = 2 * n := by omega
  have hv := (originalHorizontalClosure_profile_endpoints P Q v hQ).1
  unfold content at hv
  refine ⟨hm, ?_⟩
  ext
  · exact hv0
  · omega

/-- Literal point membership identifies both complete source copies, including their shared row. -/
theorem originalHorizontalClosure_profile_point {n m : ℕ}
    (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalHorizontalClosure P = translate v Q.cells) (i j : ℤ) :
    (i, j) ∈ Q.cells ↔
      (i - n, j - n) ∈ P.cells ∨ (i, j - P.xi 0) ∈ P.cells := by
  have hv := (originalHorizontalClosure_profile_rows P Q v hQ).2
  have he : (i, j) ∈ Q.cells ↔ (i, j) + v ∈ originalHorizontalClosure P := by
    rw [hQ, mem_translate, add_sub_cancel_right]
  rw [he, originalHorizontalClosure_cells, Finset.mem_union, mem_translate, hv,
    originalHorizontalDisplacement_pair]
  have hleft : (i, j) + (-(n : ℤ), -(n : ℤ)) = (i - n, j - n) := by
    ext <;> simp only [Prod.fst_add, Prod.snd_add] <;> ring
  have hright : (i, j) + (-(n : ℤ), -(n : ℤ)) -
      (-(n : ℤ), P.xi 0 - n) = (i, j - P.xi 0) := by
    ext <;> simp only [Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub] <;> ring
  rw [hright, hleft]

end SkewCornerDescent.Matrix
