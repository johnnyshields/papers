/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.NonVLegality
import SkewCornerDescent.EmptyClosureComplement

/-!
# The concrete ordinary gauge pair on the non-V eight-cell example

Supports `shields-2026-skew-corner-descent.tex` (`rem:ordinary-gauge`).
The same literal inner admits the horizontal column mark and a vertical row
mark. The two actual compositions agree after antitransposing a nonempty outer.
The two-cell outer functions remain distinct. Sorry-free.
-/

namespace SkewCornerDescent

open SkewGluing MvPolynomial

/-- The actual vertical ordinary reading on the same eight-cell inner. -/
def nonVVerticalMarkFour : MarkedInner where
  E := nonVDiagram 4
  W := {(0, 0), (0, 1)}
  v := (-2, 2)
  case := .b

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
-- The kernel checks the finite-window legality predicate and all marked subsets of eight cells.
/-- The complete concrete vertical ordinary mark is legal. -/
theorem nonVVerticalMarkFour_isLegal : nonVVerticalMarkFour.IsLegal := by
  apply MarkedInner.isLegal_iff_window.mpr
  decide

/-- The displacement difference is the actual southeast diagonal step. -/
theorem nonVFour_displacement_gauge :
    (nonVMark 4).v = nonVVerticalMarkFour.v + eCell := by
  decide

/-- Every nonempty actual outer transforms by the stated ordinary gauge,
with the inner held literally fixed and no function-equivalent replacement. -/
theorem nonVFour_compose_gauge (D : Diagram) (hD : D.Nonempty) :
    (nonVMark 4).compose D = nonVVerticalMarkFour.compose (antitranspose D) := by
  exact MarkedInner.compose_antitranspose_gauge hD
    (ωa := nonVMark 4) (ωb := nonVVerticalMarkFour) rfl rfl rfl
    nonVFour_displacement_gauge

/-- The row and column two-cell outers really have different functions. -/
theorem two_cell_outer_functions_ne :
    cellSchur (horizontalRow 2) (isConnectedSkew_horizontalRow (by decide)).1 ≠
      cellSchur (antitranspose (horizontalRow 2))
        (isConnectedSkew_antitranspose (isConnectedSkew_horizontalRow (by decide))).1 := by
  have hr := cellSchur_horizontal_row (2 : ℕ+)
  have hc := cellSchur_antitranspose_two_row
  intro he
  have hx : (X (2 : ℕ+) : Lambda) = X 1 ^ 2 - X 2 := hr.symm.trans (he.trans hc)
  let φ : Lambda →+* ℚ := eval₂Hom (RingHom.id ℚ) (fun j : ℕ+ => if j = 2 then 1 else 0)
  have h := congrArg φ hx
  norm_num [φ] at h

end SkewCornerDescent
