/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/


import SkewCornerDescent.Matrix.OriginalOrdinaryClosureScalars
import SkewCornerDescent.Matrix.OriginalLiteralPeriodTranslation
import SkewCornerDescent.Matrix.OriginalClosureEnumeration
import SkewCornerDescent.Matrix.OriginalVerticalClosureEnumeration

/-!
# Exact original beta span between ordinary source copies

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
Both actual ordinary closure directions contain the two whole selected
component inventories. Their literal cell translations identify the
retained starting beta coordinates across the entire source span, with
the vertical unit join retained. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate
open SkewGluing
variable {D : Diagram} {hD : IsConnectedSkew D}

/-- The genuine ordinary source copies differ by exactly the full parent beta span. -/
theorem originalOrdinaryClosure_selected_beta_copy_span {pn qn : ℕ}
    (P : Profile pn) (Q : Profile qn) (z : ℤ × ℤ)
    (hQ : originalHorizontalClosure P = translate z Q.cells ∨
      originalVerticalClosure P = translate z Q.cells) :
    ∃ hCQ : originalSelectedCount (hD := hD) Q = 2 * originalSelectedCount (hD := hD) P,
    ∀ i : Fin (originalSelectedCount (hD := hD) P),
      originalSelectedSourceBeta Q ⟨originalSelectedCount (hD := hD) P + i.val, by
        have := i.isLt
        omega⟩ = originalSelectedSourceBeta Q ⟨i.val, by have := i.isLt; omega⟩ - P.xi 0 := by
  obtain ⟨coord⟩ := exists_selectedCoordinate hD
  have hCQ := originalOrdinaryClosure_selected_count (hD := hD) P Q z hQ
  refine ⟨hCQ, ?_⟩
  intro i
  let up := originalSelectedEnumeration (hD := hD) Q ⟨i.val, by have := i.isLt; omega⟩
  let down := originalSelectedEnumeration (hD := hD) Q
    ⟨originalSelectedCount (hD := hD) P+i.val, by have := i.isLt; omega⟩
  let A := interiorBlockCells P (originalSelectedEnumeration (hD := hD) P i).val.val
  obtain ⟨w, hw, hu, hl⟩ : ∃ w : ℤ × ℤ, content w = P.xi 0 ∧
      translate z (interiorBlockCells Q up.val.val) = translate w A ∧
      translate z (interiorBlockCells Q down.val.val) = A := by
    rcases hQ with hH | hV
    · refine ⟨vH P.cells, ?_, ?_, ?_⟩
      · simpa only [P.zeta_last, sub_zero] using originalHorizontalDisplacement_content P
      · exact originalHorizontalClosure_enumeration_upper_cells P Q z hH i
      · exact originalHorizontalClosure_enumeration_lower_cells P Q z hH i
    · refine ⟨vH P.cells-eCell, originalVerticalDisplacement_content P, ?_, ?_⟩
      · exact originalVerticalClosure_enumeration_upper_cells P Q z hV i
      · exact originalVerticalClosure_enumeration_lower_cells P Q z hV i
  have hrel : translate w (interiorBlockCells Q down.val.val) =
      interiorBlockCells Q up.val.val := by
    apply translate_injective z
    calc
      translate z (translate w (interiorBlockCells Q down.val.val)) =
          translate w (translate z (interiorBlockCells Q down.val.val)) := by
        rw [translate_translate, translate_translate, add_comm z w]
      _ = translate w A := by rw [hl]
      _ = translate z (interiorBlockCells Q up.val.val) := hu.symm
  have hb := (coord.originalSelected_translated_endpoints Q Q down up w hrel).1
  rw [hw] at hb
  change Q.xi down.val.val.succ = Q.xi up.val.val.succ - P.xi 0
  omega

end SkewCornerDescent.Matrix.SelectedCoordinate
