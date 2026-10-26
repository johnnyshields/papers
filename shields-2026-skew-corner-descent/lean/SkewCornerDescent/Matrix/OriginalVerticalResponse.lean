/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalVerticalResponseCorrection
import SkewCornerDescent.Matrix.OriginalHorizontalCutResponses
import SkewCornerDescent.Matrix.OriginalClosurePhaseHessian

/-!
# Actual vertical closure response and its complete true-cap correction

Formalizes `shields-2026-skew-corner-descent.tex` (`prop:closure-pin`).
The literal vertical profile, its complete selected join interval, and every
old inverse entry produce the full response relation S_V = S_H - F. The
correction is the actual source true-cap product, not a mixed-jet surrogate
or an assumed determinant-orientation sign. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Every actual upper-to-lower vertical selected response is the corresponding
literal horizontal response minus its complete original cap pair. -/
theorem originalVerticalClosure_local_response {n m s : ℕ}
    (P : Profile n) (V : Profile m) (H : Profile s) (v w : ℤ × ℤ)
    (hV : originalVerticalClosure P = translate v V.cells)
    (hH : originalHorizontalClosure P = translate w H.cells)
    (b d : OriginalSelectedBlocks (hD := hD) P) :
    c.regularResidue (c.originalLocalResponse V
        (some (originalVerticalClosureSelectedCopy P V v hV true b))
        (some (originalVerticalClosureSelectedCopy P V v hV false d))) =
      c.regularResidue (c.originalLocalResponse H
          (some (originalHorizontalClosureSelectedCopy P H w hH true b))
          (some (originalHorizontalClosureSelectedCopy P H w hH false d))) -
        c.regularResidue (c.originalLocalResponse P (some b) none) *
          c.regularResidue (c.originalLocalResponse P none (some d)) := by
  have h := c.originalVerticalClosure_response_correction P V H v w hV hH b d
  dsimp only at h
  rw [c.originalHorizontalClosure_into_cut_response P H w hH b d,
    c.originalHorizontalClosure_out_of_cut_response P H w hH b d] at h
  exact h

/-- The actual vertical closure's omitted-phase response is exactly its
actual horizontal reference minus the entire true-cap product. The two caps
and their order are identified from the original finite source enumeration. -/
theorem originalVerticalClosure_central_response {n m s : ℕ}
    (P : Profile n) (V : Profile m) (H : Profile s) (v w : ℤ × ℤ)
    (hV : originalVerticalClosure P = translate v V.cells)
    (hH : originalHorizontalClosure P = translate w H.cells)
    (hB : 0 < originalSelectedCount (hD := hD) P) :
    let first : Fin (originalSelectedCount (hD := hD) P) := ⟨0, hB⟩
    let last : Fin (originalSelectedCount (hD := hD) P) :=
      ⟨originalSelectedCount (hD := hD) P - 1, by omega⟩
    let middle : Fin (originalSelectedCount (hD := hD) H + 1) :=
      ⟨originalSelectedCount (hD := hD) P, by
        rw [originalHorizontalClosure_profile_selected_count P H w hH]
        omega⟩
    c.regularResidue (c.originalLocalResponse V
        (some (originalVerticalClosureSelectedCopy P V v hV true
          (originalSelectedEnumeration (hD := hD) P last)))
        (some (originalVerticalClosureSelectedCopy P V v hV false
          (originalSelectedEnumeration (hD := hD) P first)))) =
      c.regularResidue (c.originalHessenbergResponse H middle middle) -
        c.originalTrueCapProduct P := by
  intro first last middle
  let E := originalSelectedEnumeration (hD := hD) P
  have h := c.originalVerticalClosure_local_response P V H v w hV hH (E last) (E first)
  have hmiddle := c.originalHorizontalClosure_middle_local_response P H w hH hB
  dsimp only at hmiddle
  rw [← hmiddle] at h
  have hfirst : c.originalHessenbergResponse P 0 0 =
      c.originalLocalResponse P none (some (E first)) := by
    unfold originalHessenbergResponse
    change c.originalLocalResponse P (originalHessenbergRows (hD := hD) P 0)
      (originalHessenbergCols (hD := hD) P 0) = _
    rw [originalHessenbergRows_zero]
    have hi : (0 : Fin (originalSelectedCount (hD := hD) P + 1)) = first.castSucc := rfl
    rw [hi, originalHessenbergCols_castSucc]
  have hlast : c.originalHessenbergResponse P (Fin.last _) (Fin.last _) =
      c.originalLocalResponse P (some (E last)) none := by
    unfold originalHessenbergResponse
    change c.originalLocalResponse P (originalHessenbergRows (hD := hD) P (Fin.last _))
      (originalHessenbergCols (hD := hD) P (Fin.last _)) = _
    rw [originalHessenbergCols_last]
    have hi : (Fin.last (originalSelectedCount (hD := hD) P)) = last.succ := by
      apply Fin.ext
      simp only [Fin.val_last, Fin.val_succ]
      dsimp only [last]
      omega
    rw [hi, originalHessenbergRows_succ]
  unfold originalTrueCapProduct
  rw [hfirst, hlast]
  simpa only [mul_comm] using h

/-- Both ordinary affine planes are actual closure responses. The complete
vertical profile and its selected join occurrences are produced from the source,
not carried as an assumed representation of the unit-corrected function. -/
theorem originalClosure_plane_actual_response {n s : ℕ}
    (P : Profile n) (H : Profile s) (w : ℤ × ℤ)
    (hH : originalHorizontalClosure P = translate w H.cells)
    (hB : 0 < originalSelectedCount (hD := hD) P) (vertical : Bool) :
    let first : Fin (originalSelectedCount (hD := hD) P) := ⟨0, hB⟩
    let last : Fin (originalSelectedCount (hD := hD) P) :=
      ⟨originalSelectedCount (hD := hD) P - 1, by omega⟩
    let middle : Fin (originalSelectedCount (hD := hD) H + 1) :=
      ⟨originalSelectedCount (hD := hD) P, by
        rw [originalHorizontalClosure_profile_selected_count P H w hH]
        omega⟩
    ∃ m : ℕ, ∃ V : Profile m, ∃ v : ℤ × ℤ,
      ∃ hV : originalVerticalClosure P = translate v V.cells,
        c.regularResidue (c.originalHessenbergResponse H middle middle) -
            (if vertical then 1 else 0) * c.originalTrueCapProduct P =
          if vertical then
            c.regularResidue (c.originalLocalResponse V
              (some (originalVerticalClosureSelectedCopy P V v hV true
                (originalSelectedEnumeration (hD := hD) P last)))
              (some (originalVerticalClosureSelectedCopy P V v hV false
                (originalSelectedEnumeration (hD := hD) P first))))
          else c.regularResidue (c.originalHessenbergResponse H middle middle) := by
  intro first last middle
  obtain ⟨m, V, v, hV⟩ := (originalVerticalClosure_connected P).exists_profile_cells
  refine ⟨m, V, v, hV, ?_⟩
  cases vertical
  · simp only [Bool.false_eq_true, ↓reduceIte, zero_mul, sub_zero]
  · simp only [↓reduceIte, one_mul]
    exact (c.originalVerticalClosure_central_response P V H v w hV hH hB).symm

end SkewCornerDescent.Matrix.SelectedCoordinate
