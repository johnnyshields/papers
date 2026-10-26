/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalEndpointProfiles

/-!
# Complete original endpoint coordinates are injective

Supports `shields-2026-skew-corner-descent.tex` (`lem:early-recovery`, `cor:row-pencil`).
The actual source partition and the original strict beta order supply coordinate
injection on the complete remaining family and every retained interval. Thus
an interval has at most one literal unit vertex at any position. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D}

/-- Every complete original remaining occurrence has its own column coordinate. -/
theorem originalResponseCols_injective {n : ℕ} (P : Profile n) :
    Function.Injective (originalResponseCols (hD := hD) P) := by
  intro i j he
  have hz : P.zeta (originalColSplitEquiv (hD := hD) P (.inr i)) =
      P.zeta (originalColSplitEquiv (hD := hD) P (.inr j)) := by
    rw [originalColSplitEquiv_removed, originalColSplitEquiv_removed]
    exact he
  exact Sum.inr_injective ((originalColSplitEquiv (hD := hD) P).injective
    (P.zeta_strictAnti.injective hz))

/-- Original interval pruning retains the actual source column injection. -/
theorem original_interval_cols_injective {n : ℕ} (P : Profile n)
    (b d : Option (OriginalSelectedBlocks (hD := hD) P)) :
    Function.Injective (fun i : OriginalResponseInterval (hD := hD) P b d =>
      originalResponseCols P i.1.1) := by
  intro i j he
  apply Subtype.ext
  apply Subtype.ext
  exact originalResponseCols_injective P he

/-- A complete original interval has at most one literal unit vertex at any
specified physical position, including an invisible midpoint. -/
theorem original_interval_unit_vertex_count_le_one {n : ℕ} (P : Profile n)
    (b d : Option (OriginalSelectedBlocks (hD := hD) P)) (z : ℤ) :
    (Finset.univ.filter (fun i : OriginalResponseInterval (hD := hD) P b d =>
      originalResponseRows P i.1.1 = z ∧ originalResponseCols P i.1.1 = z)).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro i hi j hj
  apply original_interval_cols_injective P b d
  exact (Finset.mem_filter.mp hi).2.2.trans (Finset.mem_filter.mp hj).2.2.symm

end SkewCornerDescent.Matrix.SelectedCoordinate
