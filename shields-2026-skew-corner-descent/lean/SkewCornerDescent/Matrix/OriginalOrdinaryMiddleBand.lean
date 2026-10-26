/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/


import SkewCornerDescent.Matrix.OriginalSelectedContentCover
import SkewCornerDescent.Matrix.OriginalOrdinaryBetaSpan

/-!
# Exact ordinary middle content band from the true source caps

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
Literal upper and lower selected-component copies identify the genuine
extreme beta coordinates of the doubled ordinary closure. Its middle
content band is bounded by the original right cap and the doubled source
span minus the original left cap, in both ordinary directions. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate
open SkewGluing
variable {D : Diagram} {hD : IsConnectedSkew D}

/-- Both actual ordinary closure directions have the exact source-cap
thresholds for their complete middle content band. -/
theorem originalOrdinaryClosure_middle_betas {pn qn : ℕ}
    (P : Profile pn) (Q : Profile qn) (z : ℤ × ℤ)
    (hQ : originalHorizontalClosure P = translate z Q.cells ∨
      originalVerticalClosure P = translate z Q.cells)
    [NeZero (originalSelectedCount (hD := hD) P)]
    [NeZero (originalSelectedCount (hD := hD) Q)] :
    (originalSelectedMiddleLowerBeta (hD := hD) Q =
      originalHessenbergDistance (hD := hD) P (Fin.last _) (Fin.last _)) ∧
    (originalSelectedMiddleUpperBeta (hD := hD) Q =
      2 * P.xi 0 - originalHessenbergDistance (hD := hD) P 0 0) := by
  obtain ⟨coord⟩ := exists_selectedCoordinate hD
  have hP := NeZero.pos (originalSelectedCount (hD := hD) P)
  have hQQ := NeZero.pos (originalSelectedCount (hD := hD) Q)
  have hCQ := originalOrdinaryClosure_selected_count (hD := hD) P Q z hQ
  let pf := originalSelectedEnumeration (hD := hD) P ⟨0,hP⟩
  let pl := originalSelectedEnumeration (hD := hD) P
    ⟨originalSelectedCount (hD := hD) P-1, by omega⟩
  let qf := originalSelectedEnumeration (hD := hD) Q ⟨0,hQQ⟩
  let qidx : Fin (originalSelectedCount (hD := hD) Q) :=
    ⟨originalSelectedCount (hD := hD) P + (originalSelectedCount (hD := hD) P-1), by omega⟩
  let ql := originalSelectedEnumeration (hD := hD) Q qidx
  have hcanonical : qidx = ⟨originalSelectedCount (hD := hD) Q-1, by omega⟩ :=
    Fin.ext (by dsimp only [qidx]; omega)
  obtain ⟨w, hw, hz, hu, hl⟩ : ∃ w : ℤ × ℤ, content w = P.xi 0 ∧ content z = 0 ∧
      translate z (interiorBlockCells Q qf.val.val) =
        translate w (interiorBlockCells P pf.val.val) ∧
      translate z (interiorBlockCells Q ql.val.val) = interiorBlockCells P pl.val.val := by
    rcases hQ with hH | hV
    · refine ⟨vH P.cells, ?_, (originalHorizontalClosure_profile_endpoints P Q z hH).1, ?_, ?_⟩
      · simpa only [P.zeta_last, sub_zero] using originalHorizontalDisplacement_content P
      · exact originalHorizontalClosure_enumeration_upper_cells P Q z hH ⟨0,hP⟩
      · exact originalHorizontalClosure_enumeration_lower_cells P Q z hH
          ⟨originalSelectedCount (hD := hD) P-1, by omega⟩
    · refine ⟨vH P.cells-eCell, originalVerticalDisplacement_content P,
        originalVerticalClosure_profile_content P Q z hV, ?_, ?_⟩
      · exact originalVerticalClosure_enumeration_upper_cells P Q z hV ⟨0,hP⟩
      · exact originalVerticalClosure_enumeration_lower_cells P Q z hV
          ⟨originalSelectedCount (hD := hD) P-1, by omega⟩
  have hlower := (coord.originalSelected_translated_endpoints Q P ql pl z hl).1
  rw [hz, add_zero] at hlower
  have hrel : translate (w-z) (interiorBlockCells P pf.val.val) =
      interiorBlockCells Q qf.val.val := by
    apply translate_injective z
    rw [translate_translate, show z+(w-z) = w by abel]
    exact hu.symm
  have hupper := (coord.originalSelected_translated_endpoints P Q pf qf (w-z) hrel).2
  rw [MarkedInner.content_sub, hw, hz, sub_zero] at hupper
  constructor
  · unfold originalSelectedMiddleLowerBeta originalSelectedSourceBeta
    rw [← hcanonical, originalHessenbergDistance_last P hP]
    change Q.xi ql.val.val.succ = P.xi pl.val.val.succ - P.zeta (Fin.last pn)
    rw [P.zeta_last, sub_zero]
    exact hlower.symm
  · unfold originalSelectedMiddleUpperBeta
    rw [originalHessenbergDistance_first P hP]
    change Q.zeta (interiorBlockLast Q qf.val.val).castSucc =
      2 * P.xi 0 - (P.xi 0 - P.zeta (interiorBlockLast P pf.val.val).castSucc)
    rw [hupper]
    ring

end SkewCornerDescent.Matrix.SelectedCoordinate
