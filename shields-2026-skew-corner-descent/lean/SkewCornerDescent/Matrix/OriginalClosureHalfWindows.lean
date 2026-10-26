/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalClosurePrivateCut
import SkewCornerDescent.Matrix.OriginalFilteredCapProjection

/-!
# Literal half windows of the complete horizontal closure

Supports `shields-2026-skew-corner-descent.tex` (`prop:closure-pin`).
Both normalized closure half windows are complete translated source diagrams.
Every source block lies in its full content window, including empty unit blocks.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix

open SkewGluing

/-- The actual lower half window of the canonical closure is the entire
unshifted source copy, with its row normalization. -/
theorem originalHorizontalClosure_lower_window {n m : ℕ}
    (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalHorizontalClosure P = translate v Q.cells) :
    Q.cells.filter (fun x => 0 ≤ content x ∧ content x < P.xi 0) =
      translate ((n : ℤ), (n : ℤ)) P.cells := by
  ext x
  rcases x with ⟨i, j⟩
  rw [Finset.mem_filter, mem_translate]
  change ((i, j) ∈ Q.cells ∧ 0 ≤ j - i ∧ j - i < P.xi 0) ↔
    (i - n, j - n) ∈ P.cells
  rw [originalHorizontalClosure_profile_point P Q v hQ]
  constructor
  · rintro ⟨h | h, hb⟩
    · exact h
    · have hc := P.content_bounds_cells h
      dsimp only [content] at hc
      omega
  · intro h
    have hc := P.content_bounds_cells h
    dsimp only [content] at hc
    exact ⟨Or.inl h, by omega, by omega⟩

/-- The actual upper half window is the other complete source copy, with
its genuine span displacement. -/
theorem originalHorizontalClosure_upper_window {n m : ℕ}
    (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalHorizontalClosure P = translate v Q.cells) :
    Q.cells.filter (fun x => P.xi 0 ≤ content x ∧ content x < 2 * P.xi 0) =
      translate (0, P.xi 0) P.cells := by
  ext x
  rcases x with ⟨i, j⟩
  rw [Finset.mem_filter, mem_translate]
  simp only [Prod.mk_sub_mk, sub_zero]
  change ((i, j) ∈ Q.cells ∧ P.xi 0 ≤ j - i ∧ j - i < 2 * P.xi 0) ↔
    (i, j - P.xi 0) ∈ P.cells
  rw [originalHorizontalClosure_profile_point P Q v hQ]
  constructor
  · rintro ⟨h | h, hb⟩
    · have hc := P.content_bounds_cells h
      dsimp only [content] at hc
      omega
    · exact h
  · intro h
    have hc := P.content_bounds_cells h
    dsimp only [content] at hc
    exact ⟨Or.inr h, by omega, by omega⟩

namespace SelectedCoordinate

variable {D : Diagram} {hD : IsConnectedSkew D}

/-- All actual full blocks belong to the complete source content window.
The empty-block clause uses strict internal beta bounds, not vacuous cell support. -/
theorem originalBlockInWindow_full {n : ℕ} (P : Profile n) (b : OriginalBlocks P) :
    originalBlockInWindow P 0 (P.xi 0) b := by
  by_cases hpos : P.zeta b.val.castSucc < P.xi b.val.succ
  · left
    refine ⟨hpos, ?_⟩
    intro x hx
    exact P.content_bounds_cells
      (Finset.mem_filter.mp (interiorSliceCells_subset P _ _ _ hx)).1
  · right
    have hle := P.zeta_le_xi_succ b.val
    have hlo := P.zeta_strictAnti (show b.val.castSucc < Fin.last n by
      change b.val.val < n
      exact b.val.isLt)
    rw [P.zeta_last] at hlo
    have hhi := P.xi_strictAnti (show (0 : Fin (n + 1)) < b.val.succ by
      change 0 < b.val.val + 1
      omega)
    exact ⟨by omega, hlo, hhi⟩

end SelectedCoordinate
end SkewCornerDescent.Matrix
