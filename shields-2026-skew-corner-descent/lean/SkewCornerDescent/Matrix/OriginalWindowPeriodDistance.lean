/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalWindowGapAssembly
import SkewCornerDescent.Matrix.OriginalBoundedSchurFrontier

/-!
# Fixed-span internal windows from literal endpoint translations

Supports `shields-2026-skew-corner-descent.tex` (`lem:maximal-bin`). Equal
complete end windows translate the actual selected endpoint ranks. Their exact
content shift determines every full internal-period distance; no completed cyclic
period is assumed. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing CyclicWindows

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- A full internal period spans precisely the literal content displacement.
Repeated selected components retain their original ranks. -/
theorem originalWindow_selected_period_distance {n m : ℕ} (P : Profile n) (W : Profile m)
    (q : ℤ) (u v : ℤ × ℤ) (hv : content v = q)
    (hW : P.cells.filter (fun x => 0 ≤ content x ∧ content x < P.xi 0 - q) =
      translate u W.cells)
    (hwindow : P.cells.filter (fun x => q ≤ content x ∧ content x < P.xi 0) =
      translate v (P.cells.filter fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hq : ∀ x ∈ diagramInterior P.cells, content x ≠ q)
    (hLq : ∀ x ∈ diagramInterior P.cells, content x ≠ P.xi 0 - q)
    (i j : Fin (originalSelectedCount (hD := hD) P))
    (hji : j.val = i.val + (originalSelectedCount (hD := hD) P -
      originalSelectedCount (hD := hD) W)) :
    originalHessenbergDistance (hD := hD) P i.succ j.castSucc = (c.top : ℤ) + q := by
  have hprefix : IsSkew (P.cells.filter fun x => 0 ≤ content x ∧ content x < P.xi 0 - q) := by
    rw [hW]
    exact isSkew_translate u W.isConnectedSkew_cells.1
  have h0 := (originalProfile_interior_boundary_gaps P).1
  have hL := (originalProfile_interior_boundary_gaps P).2
  have hcount := originalWindow_selected_count (hD := hD) P W 0 (P.xi 0 - q) u hW h0 hLq
  have hmatch := originalWindow_selected_index_translation (hD := hD) P q v hv hprefix
    hwindow h0 hq hLq hL i j (by rw [hcount]; exact hji)
  let E := originalSelectedEnumeration (hD := hD) P
  have hmin (k : Fin (originalSelectedCount (hD := hD) P)) :=
    interiorBlockCells_minContent P (E k).val.val
      (originalBlockSelected_nonempty P (E k).val (E k).property)
  have hne := (interiorBlockCells_connected P (E j).val.val
    (originalBlockSelected_nonempty P (E j).val (E j).property)).2.1
  have hc := congrArg minContent hmatch
  rw [minContent_translate hne, hmin i, hmin j, hv] at hc
  have hend := c.originalSelected_endpoint_distance P (E i)
  unfold originalHessenbergDistance
  rw [originalHessenbergRows_succ, originalHessenbergCols_castSucc,
    originalRowSplitEquiv_selected, originalColSplitEquiv_selected]
  dsimp only [E] at hend hc
  omega

end SkewCornerDescent.Matrix.SelectedCoordinate
