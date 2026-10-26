/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.SquareWordMark
import SkewCornerDescent.SquareWordDetector
import SkewCornerDescent.SquareWordNormalCoefficient

/-!
# The actual square-word counterexample

Formalizes `shields-2026-skew-corner-descent.tex` (`rem:square-word`).
A genuine legal ordinary chart has the stated nonzero second detector, original
defect order exactly one, and no actual five-copy empty line root. All geometric,
response, counting, residue, normal-jet, and root-shape inputs are produced.
Sorry-free.
-/

namespace SkewCornerDescent.SquareWordProfiles

open SkewGluing

/-- The complete square-word example, without supplied geometric or analytic compatibility. -/
theorem square_word_counterexample :
    marked.IsLegal ∧ marked.LowerV ∧ marked.UpperV ∧
      actualSecondDetector ≠ 0 ∧ PowerSeries.order defect = 1 ∧
      (∀ E : Diagram, IsConnectedSkew E → ∀ v : ℤ × ℤ,
        source.cells ≠ translate v ((emptyMarkH E).compose (horizontalRow 5)) ∧
          source.cells ≠ translate v ((emptyMarkH E).compose (verticalColumn 5))) := by
  exact ⟨marked_isLegal, marked_vertical_edges.1, marked_vertical_edges.2,
    actualSecondDetector_ne_zero, defect_order_one, source_no_actual_five_copy_line_root⟩

end SkewCornerDescent.SquareWordProfiles
