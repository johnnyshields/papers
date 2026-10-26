/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalVerticalInterior
import SkewCornerDescent.Matrix.OriginalClosureRows

/-!
# Complete normalized half windows of the literal vertical closure

Supports `shields-2026-skew-corner-descent.tex` (`prop:closure-pin`).
The actual union determines both content extrema and the zero content shift
of every canonical profile presentation. Its two whole half windows are the
complete source copies, without a supplied endpoint match. Sorry-free.
-/

namespace SkewCornerDescent.Matrix

open SkewGluing

/-- Every actual vertical closure cell lies in its complete two-copy content band. -/
theorem originalVerticalClosure_content_bounds {n : ℕ} (P : Profile n)
    {x : ℤ × ℤ} (hx : x ∈ originalVerticalClosure P) :
    0 ≤ content x ∧ content x < 2 * P.xi 0 := by
  rw [originalVerticalClosure_union] at hx
  have hL := P.xi_pos (0 : Fin (n + 1))
  rcases Finset.mem_union.mp hx with hx | hx
  · have hb := P.content_bounds_cells hx
    omega
  · have hb := P.content_bounds_cells (mem_translate.mp hx)
    have hw := originalVerticalDisplacement_content P
    simp only [content, eCell, Prod.fst_sub, Prod.snd_sub] at hb hw
    dsimp only [content]
    omega

/-- The actual vertical closure has exactly the complete source's doubled
content interval, independently of its row normalization. -/
theorem originalVerticalClosure_content_extrema {n : ℕ} (P : Profile n) :
    minContent (originalVerticalClosure P) = 0 ∧
      maxContent (originalVerticalClosure P) = 2 * P.xi 0 - 1 := by
  have hlow : ((n : ℤ), (n : ℤ)) ∈ originalVerticalClosure P := by
    rw [originalVerticalClosure_union]
    apply Finset.mem_union_left
    simpa only [P.zeta_last, Fin.val_last, zero_add] using P.row_left_mem_cells (Fin.last n)
  have hhigh : (0, P.xi 0 - 1) + (vH P.cells - eCell) ∈ originalVerticalClosure P := by
    rw [originalVerticalClosure_union]
    apply Finset.mem_union_right
    apply mem_translate.mpr
    simpa only [add_sub_cancel_right, Fin.val_zero, Nat.cast_zero, add_zero]
      using P.row_right_mem_cells 0
  have hc : content ((0, P.xi 0 - 1) + (vH P.cells - eCell)) = 2 * P.xi 0 - 1 := by
    have hw := originalVerticalDisplacement_content P
    simp only [content, eCell, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub] at *
    omega
  constructor
  · apply minContent_eq_of (Finset.mem_image.mpr ⟨((n : ℤ), (n : ℤ)), hlow, by simp [content]⟩)
    intro k hk
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hk
    exact (originalVerticalClosure_content_bounds P hx).1
  · apply maxContent_eq_of (Finset.mem_image.mpr ⟨_, hhigh, hc⟩)
    intro k hk
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hk
    have hb := (originalVerticalClosure_content_bounds P hx).2
    omega

/-- The canonical vertical profile normalization shifts no content. -/
theorem originalVerticalClosure_profile_content {n m : ℕ}
    (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalVerticalClosure P = translate v Q.cells) : content v = 0 := by
  have h := congrArg minContent hQ
  rw [(originalVerticalClosure_content_extrema P).1,
    minContent_translate Q.isConnectedSkew_cells.2.1, Q.minContent_cells] at h
  omega

/-- Both source copies determine the actual vertical profile's global top. -/
theorem originalVerticalClosure_profile_top {n m : ℕ}
    (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalVerticalClosure P = translate v Q.cells) : Q.xi 0 = 2 * P.xi 0 := by
  have h := congrArg maxContent hQ
  rw [(originalVerticalClosure_content_extrema P).2,
    maxContent_translate Q.isConnectedSkew_cells.2.1, Q.maxContent_cells,
    originalVerticalClosure_profile_content P Q v hQ] at h
  omega

/-- The lower half of the canonical vertical profile is the whole unshifted
source copy, transported by the actual normalization. -/
theorem originalVerticalClosure_lower_window {n m : ℕ}
    (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalVerticalClosure P = translate v Q.cells) :
    Q.cells.filter (fun x => 0 ≤ content x ∧ content x < P.xi 0) = translate (-v) P.cells := by
  have hv := originalVerticalClosure_profile_content P Q v hQ
  have hw := originalVerticalDisplacement_content P
  ext x
  rw [Finset.mem_filter, mem_translate, sub_neg_eq_add]
  have hpoint : x ∈ Q.cells ↔ x + v ∈ originalVerticalClosure P := by
    rw [hQ, mem_translate, add_sub_cancel_right]
  rw [hpoint, originalVerticalClosure_union, Finset.mem_union, mem_translate]
  constructor
  · rintro ⟨hx | hx, hb⟩
    · exact hx
    · have h := P.content_bounds_cells hx
      simp only [content, eCell, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub] at *
      omega
  · intro hx
    have h := P.content_bounds_cells hx
    refine ⟨Or.inl hx, ?_⟩
    simp only [content, Prod.fst_add, Prod.snd_add] at *
    omega

/-- The upper half contains the other complete original source copy. The
vertical displacement is retained, rather than replaced by horizontal rows. -/
theorem originalVerticalClosure_upper_window {n m : ℕ}
    (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalVerticalClosure P = translate v Q.cells) :
    Q.cells.filter (fun x => P.xi 0 ≤ content x ∧ content x < 2 * P.xi 0) =
      translate (vH P.cells - eCell - v) P.cells := by
  have hv := originalVerticalClosure_profile_content P Q v hQ
  have hw := originalVerticalDisplacement_content P
  ext x
  rw [Finset.mem_filter, mem_translate]
  rw [show x - (vH P.cells - eCell - v) = x + v - (vH P.cells - eCell) by abel]
  have hpoint : x ∈ Q.cells ↔ x + v ∈ originalVerticalClosure P := by
    rw [hQ, mem_translate, add_sub_cancel_right]
  rw [hpoint, originalVerticalClosure_union, Finset.mem_union, mem_translate]
  constructor
  · rintro ⟨hx | hx, hb⟩
    · have h := P.content_bounds_cells hx
      simp only [content, Prod.fst_add, Prod.snd_add] at *
      omega
    · exact hx
  · intro hx
    have h := P.content_bounds_cells hx
    refine ⟨Or.inr hx, ?_⟩
    simp only [content, eCell, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub] at *
    omega

end SkewCornerDescent.Matrix
