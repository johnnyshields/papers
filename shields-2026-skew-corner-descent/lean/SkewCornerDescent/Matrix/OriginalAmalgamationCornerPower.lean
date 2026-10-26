/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.LiteralOverlapInventory
import SkewCornerDescent.Matrix.OriginalMultiplicity

/-!
# Actual whole amalgamation corner powers from literal windows

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
Complete original source and overlap inventories determine the actual union's
whole complementary determinant before selecting any component or normal chart.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix

open SkewGluing

/-- Original corner powers and complete literal overlap windows produce the
whole actual amalgamation cofactor power, without a supplied union inventory. -/
theorem originalAmalgamation_corner_power {n m k : ℕ}
    (P : Profile n) (W : Profile m) (A : Profile k)
    (q : ℤ) (v u z : ℤ × ℤ) (hv : content v = q)
    (hwindow : P.cells.filter (fun x => q ≤ content x ∧ content x < P.xi 0) =
      translate v (P.cells.filter fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hW : translate z W.cells = P.cells.filter
      (fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hA : P.cells ∪ translate v P.cells = translate u A.cells)
    (Λ : Lambda) (b a : ℕ) (hab : a ≤ b)
    (hKP : (jtMatrix (fun j : Fin n => P.xi j.succ)
      (fun j => P.zeta j.castSucc)).det = Λ ^ b)
    (hKW : (jtMatrix (fun j : Fin m => W.xi j.succ)
      (fun j => W.zeta j.castSucc)).det = Λ ^ a) :
    (jtMatrix (fun j : Fin k => A.xi j.succ)
      (fun j => A.zeta j.castSucc)).det = Λ ^ (2 * b - a) := by
  have hUs : IsSkew (P.cells ∪ translate v P.cells) := by
    rw [hA]
    exact isSkew_translate u A.isConnectedSkew_cells.1
  have hKP' : cellSchur (diagramInterior P.cells) P.isConnectedSkew_cells.1.interior = Λ ^ b := by
    simpa only [← Profile.minorDet_eq_interiorSchur, betaDet, jtMatrix] using hKP
  have hKW' : cellSchur (diagramInterior (translate z W.cells))
      (isSkew_translate z W.isConnectedSkew_cells.1).interior = Λ ^ a := by
    calc
      _ = cellSchur (translate z (diagramInterior W.cells))
          (isSkew_translate z W.isConnectedSkew_cells.1.interior) :=
        cellSchur_congr (interior_translate W.cells z) _ _
      _ = cellSchur (diagramInterior W.cells) W.isConnectedSkew_cells.1.interior :=
        SkewGluing.cellSchur_translate (diagramInterior W.cells)
          W.isConnectedSkew_cells.1.interior z
      _ = _ := by
        simpa only [← Profile.minorDet_eq_interiorSchur, betaDet, jtMatrix] using hKW
  have hp := literalOverlap_corner_power P.cells (translate z W.cells) P.isConnectedSkew_cells
    (isSkew_translate z W.isConnectedSkew_cells.1) (P.xi 0) (P.xi 0 - q) v
    P.minContent_cells (by simpa only [sub_sub_cancel] using hv)
    (fun x hx => P.content_bounds_cells hx)
    (by simpa only [sub_sub_cancel] using hwindow) hW hUs Λ b a hab hKP' hKW'
  have he : diagramInterior (P.cells ∪ translate v P.cells) =
      translate u (diagramInterior A.cells) := by rw [hA, interior_translate]
  have ht := cellSchur_congr he hUs.interior (isSkew_translate u A.isConnectedSkew_cells.1.interior)
  rw [SkewGluing.cellSchur_translate (diagramInterior A.cells) A.isConnectedSkew_cells.1.interior u]
    at ht
  simpa only [← Profile.minorDet_eq_interiorSchur, betaDet, jtMatrix] using ht.symm.trans hp

end SkewCornerDescent.Matrix
