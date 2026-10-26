/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.OriginalClosureCentralResponse

/-!
# Literal exterior endpoints of the horizontal closure

Supports `shields-2026-skew-corner-descent.tex`, «Actual responses and residue classes»
(`sec:normal-chart`, `lem:actual-words`). The complete two-copy cell union determines both
actual exterior endpoints of every translated closure profile. Sorry-free.
-/

namespace SkewCornerDescent.Matrix

open SkewGluing

/-- The actual empty horizontal closure is the complete two-copy cell union. -/
theorem originalHorizontalClosure_cells {n : ℕ} (P : Profile n) :
    originalHorizontalClosure P = P.cells ∪ translate (vH P.cells) P.cells := by
  unfold originalHorizontalClosure
  rw [MarkedInner.compose_horizontalRow (emptyMarkH P.cells) (by decide : 1 ≤ 2)]
  simp only [MarkedInner.rowCopies, show (2 : ℕ) = (0 + 1) + 1 from rfl,
    Finset.range_add_one, Finset.range_zero, Finset.biUnion_insert, Finset.biUnion_empty,
    Nat.cast_zero, Nat.cast_one, zero_smul, one_smul, emptyMarkH,
    SkewGluing.translate_zero, Finset.empty_union, Finset.union_comm]

/-- The literal closure keeps the original least content, including its extreme cell. -/
theorem originalHorizontalClosure_minContent {n : ℕ} (P : Profile n) :
    minContent (originalHorizontalClosure P) = 0 := by
  apply minContent_eq_of
  · have hx := Finset.mem_union_left
      (translate (vH P.cells) P.cells) (P.row_left_mem_cells (Fin.last n))
    rw [← originalHorizontalClosure_cells] at hx
    have h := content_mem_contents hx
    simpa only [content, P.zeta_last, zero_add, sub_self] using h
  · intro k hk
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hk
    rw [originalHorizontalClosure_cells] at hx
    rcases Finset.mem_union.mp hx with hx | hx
    · have h := minContent_le (content_mem_contents hx)
      rw [Profile.minContent_cells] at h
      exact h
    · have h := minContent_le (content_mem_contents (mem_translate.mp hx))
      rw [Profile.minContent_cells, MarkedInner.content_sub, originalHorizontalDisplacement_content,
        P.zeta_last] at h
      have hp := P.xi_pos 0
      omega

/-- The literal closure has the exact doubled parent top, not just a span upper bound. -/
theorem originalHorizontalClosure_maxContent {n : ℕ} (P : Profile n) :
    maxContent (originalHorizontalClosure P) = 2 * P.xi 0 - 1 := by
  apply maxContent_eq_of
  · have hx : ((0 : ℤ), P.xi 0 - 1) ∈ P.cells := by
      simpa only [Fin.val_zero, Nat.cast_zero, zero_add, add_zero]
        using P.row_right_mem_cells 0
    have ht : ((0 : ℤ), P.xi 0 - 1) + vH P.cells ∈ originalHorizontalClosure P := by
      rw [originalHorizontalClosure_cells]
      exact Finset.mem_union_right _ (mem_translate.mpr (by simpa only [add_sub_cancel_right]
        using hx))
    have hc : content (((0 : ℤ), P.xi 0 - 1) + vH P.cells) = 2 * P.xi 0 - 1 := by
      rw [content_add, originalHorizontalDisplacement_content, P.zeta_last]
      simp only [content, sub_zero]
      ring
    exact hc ▸ content_mem_contents ht
  · intro k hk
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hk
    rw [originalHorizontalClosure_cells] at hx
    rcases Finset.mem_union.mp hx with hx | hx
    · have h := le_maxContent (content_mem_contents hx)
      rw [Profile.maxContent_cells] at h
      have hp := P.xi_pos 0
      omega
    · have h := le_maxContent (content_mem_contents (mem_translate.mp hx))
      rw [Profile.maxContent_cells, MarkedInner.content_sub,
        originalHorizontalDisplacement_content, P.zeta_last] at h
      omega

/-- Every normalized closure profile has the produced extremal endpoints and translation content. -/
theorem originalHorizontalClosure_profile_endpoints {n m : ℕ}
    (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalHorizontalClosure P = translate v Q.cells) :
    content v = 0 ∧ Q.xi 0 = 2 * P.xi 0 := by
  have hmin := originalHorizontalClosure_minContent P
  have hmax := originalHorizontalClosure_maxContent P
  rw [hQ, minContent_translate Q.isConnectedSkew_cells.2.1, Profile.minContent_cells,
    zero_add] at hmin
  rw [hQ, maxContent_translate Q.isConnectedSkew_cells.2.1, Profile.maxContent_cells] at hmax
  exact ⟨hmin, by omega⟩

end SkewCornerDescent.Matrix
