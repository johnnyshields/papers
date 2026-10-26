/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewJacobiNegative.NegativeBudgetInventory

/-!
# Saturated first-column reduction

The actual negative-budget reduction in `thm:saturated-column` of
`shields-2026-skew-jacobi-negative.tex`.  The child is the genuine suffix
of the maximal cofactor; the cross rectangle is counted, not assumed.
-/

namespace SkewJacobiNegative.BetaDiagram

variable {n : ℕ}

/-- The block after the first singleton in the actual maximal cofactor. -/
def saturatedColumnCore (D : BetaDiagram (n + 3)) (hP : D.PositiveCorner) :
    BetaDiagram (n + 1) :=
  ((D.cornerDiagram hP).reindexOrder
    (by omega : 1 + (n + 1) = n + 2)).suffix

/-- Saturation places a genuine component cut immediately after the first row. -/
theorem saturated_column_core_budget (D : BetaDiagram (n + 3))
    (hD : D.Connected) (hZ : D.ZeroFree)
    (hSat : D.row 2 < D.col 0) :
    let hP := D.positiveCorner_of_connected_zeroFree hD hZ
    negativeCount D = negativeCount (D.saturatedColumnCore hP) + (n + 1) := by
  let hP := D.positiveCorner_of_connected_zeroFree hD hZ
  let R := (D.cornerDiagram hP).reindexOrder
    (by omega : 1 + (n + 1) = n + 2)
  have hc : negativeCount R = negativeCount D := by
    rw [reindexOrder_negativeCount]
    exact D.corner_negativeCount hP
  have hcut : R.row ⟨1, by omega⟩ < R.col ⟨0, by omega⟩ := hSat
  have hb := negativeCount_at_cut (a := 1) (b := n + 1)
    R (by omega) (by omega) hcut
  have hzero : negativeCount (R.betaPrefix (a := 1) (b := n + 1)) = 0 := by
    classical
    rw [negativeCount_eq_cell_sum]
    simp only [Fin.sum_univ_one]
    have hp := (R.betaPrefix (a := 1) (b := n + 1)).row_nonempty 0
    simp only [ite_eq_right (not_lt_of_ge hp.le)]
  dsimp only
  change negativeCount D = negativeCount (R.suffix (a := 1) (b := n + 1)) + (n + 1)
  omega

/-- At most two negatives outside the saturated column remain in the actual core. -/
theorem saturated_column_core_small (D : BetaDiagram (n + 3))
    (hD : D.Connected) (hZ : D.ZeroFree)
    (hSat : D.row 2 < D.col 0) (hBudget : negativeCount D ≤ n + 3) :
    negativeCount (D.saturatedColumnCore
      (D.positiveCorner_of_connected_zeroFree hD hZ)) ≤ 2 := by
  have hb := D.saturated_column_core_budget hD hZ hSat
  dsimp only at hb
  omega

/-- A disconnected board pays at least its order minus one in cross negatives. -/
theorem connected_of_negativeCount_small {m : ℕ} (D : BetaDiagram m)
    (hm : 0 < m) (hCount : negativeCount D + 1 < m) : D.Connected := by
  by_contra hd
  have h := D.componentDecomposition.negative_budget_row_bound hm hd
    (negativeCount D) le_rfl
  omega

/-- In at least six parent rows the remaining block is necessarily connected. -/
theorem saturated_column_core_connected (D : BetaDiagram (n + 3))
    (hn : 3 ≤ n) (hD : D.Connected) (hZ : D.ZeroFree)
    (hSat : D.row 2 < D.col 0) (hBudget : negativeCount D ≤ n + 3) :
    (D.saturatedColumnCore (D.positiveCorner_of_connected_zeroFree hD hZ)).Connected := by
  have hb := D.saturated_column_core_small hD hZ hSat hBudget
  apply connected_of_negativeCount_small _ (by omega)
  omega

end SkewJacobiNegative.BetaDiagram
