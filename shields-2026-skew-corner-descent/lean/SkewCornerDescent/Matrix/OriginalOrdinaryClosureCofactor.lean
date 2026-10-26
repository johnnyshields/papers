/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalClosureInventory
import SkewCornerDescent.Matrix.OriginalVerticalInterior
import SkewGluing.DisconnectedTableau

/-!
# Complete ordinary closure cofactor squares in both directions

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
The actual vertical interior has two separated complete source copies, just as
the actual horizontal interior does. Both complete component products and
canonical profile presentations give the exact cofactor square.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix

open SkewGluing

/-- The actual vertical closure retains both full interior component products.
Its extra join vertex is not an interior cell and changes no cofactor factor. -/
theorem originalVerticalClosure_corner_inventory {n : ℕ} (P : Profile n) :
    cellSchur (diagramInterior (originalVerticalClosure P))
        (originalVerticalClosure_connected P).1.interior =
      cellSchur (diagramInterior P.cells) P.isConnectedSkew_cells.1.interior ^ 2 := by
  classical
  let v := vH P.cells - eCell
  have hdisj : Disjoint (diagramInterior P.cells) (translate v (diagramInterior P.cells)) := by
    rw [Finset.disjoint_left]
    intro x hx hy
    have hx0 := interior_content_strict P.isConnectedSkew_cells hx
    have hy0 := interior_content_strict P.isConnectedSkew_cells (mem_translate.mp hy)
    rw [P.minContent_cells, P.maxContent_cells] at hx0 hy0
    have hw : content v = P.xi 0 := originalVerticalDisplacement_content P
    simp only [content, Prod.fst_sub, Prod.snd_sub] at hx0 hy0 hw
    omega
  have hu := (originalVerticalClosure_connected P).1.interior
  rw [originalVerticalClosure_interior] at hu
  have hs := cellSchur_union P.isConnectedSkew_cells.1.interior
    (isSkew_translate v P.isConnectedSkew_cells.1.interior) hu hdisj
    (fun x hx y hy => originalVerticalClosure_not_adjacent P hx hy)
  rw [cellSchur_translate _ P.isConnectedSkew_cells.1.interior v] at hs
  have he := cellSchur_congr (originalVerticalClosure_interior P)
    (originalVerticalClosure_connected P).1.interior hu
  simpa only [pow_two] using he.trans hs

/-- Either actual ordinary closure has the source's whole complementary
Jacobi--Trudi determinant squared, for every canonical translated presentation. -/
theorem originalOrdinaryClosure_complementary_square {n m : ℕ}
    (P : Profile n) (Q : Profile m) (z : ℤ × ℤ)
    (hQ : originalHorizontalClosure P = translate z Q.cells ∨
      originalVerticalClosure P = translate z Q.cells) :
    (jtMatrix (fun j : Fin m => Q.xi j.succ) (fun j => Q.zeta j.castSucc)).det =
      (jtMatrix (fun j : Fin n => P.xi j.succ) (fun j => P.zeta j.castSucc)).det ^ 2 := by
  have hcopy (C : Diagram) (hc : IsConnectedSkew C) (he : C = translate z Q.cells)
      (hinv : cellSchur (diagramInterior C) hc.1.interior =
        cellSchur (diagramInterior P.cells) P.isConnectedSkew_cells.1.interior ^ 2) :
      cellSchur (diagramInterior Q.cells) Q.isConnectedSkew_cells.1.interior =
        cellSchur (diagramInterior P.cells) P.isConnectedSkew_cells.1.interior ^ 2 := by
    have heI : diagramInterior C = translate z (diagramInterior Q.cells) := by
      rw [he, interior_translate]
    have ht := cellSchur_congr heI
      hc.1.interior (isSkew_translate z Q.isConnectedSkew_cells.1.interior)
    rw [cellSchur_translate _ Q.isConnectedSkew_cells.1.interior z] at ht
    exact ht.symm.trans hinv
  have h : cellSchur (diagramInterior Q.cells) Q.isConnectedSkew_cells.1.interior =
      cellSchur (diagramInterior P.cells) P.isConnectedSkew_cells.1.interior ^ 2 := by
    rcases hQ with hQ | hQ
    · exact hcopy _ (originalHorizontalClosure_connected P) hQ
        (originalHorizontalClosure_corner_inventory P)
    · exact hcopy _ (originalVerticalClosure_connected P) hQ
        (originalVerticalClosure_corner_inventory P)
  simpa only [← Profile.minorDet_eq_interiorSchur, betaDet, jtMatrix] using h

end SkewCornerDescent.Matrix
