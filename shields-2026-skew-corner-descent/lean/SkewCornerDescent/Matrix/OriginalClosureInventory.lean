/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.OriginalClosureComponents
import SkewCornerDescent.Matrix.OriginalRemovedCancellation
import SkewGluing.EmptyRowSchur
import SkewGluing.InteriorCofactor

/-!
# Actual horizontal-closure corner inventory

Formalizes `shields-2026-skew-corner-descent.tex`, «Actual responses and residue classes»
(`sec:normal-chart`, `lem:actual-words`). The corner inventory of the actual empty horizontal
closure is the square of the original inventory. Every translated profile of the closure has
this same complementary determinant. Sorry-free.
-/

namespace SkewCornerDescent.Matrix

open SkewGluing

/-- Every positive-length actual empty horizontal row retains the complete corner inventory. -/
theorem originalEmptyHorizontal_corner_inventory {n : ℕ} (P : Profile n)
    (copies : ℕ) (hcopies : 1 ≤ copies) :
    cellSchur (diagramInterior ((emptyMarkH P.cells).compose (horizontalRow copies)))
        (MarkedInner.IsLegal.isConnectedSkew_compose_horizontalRow_all
          (emptyMarkH_isLegal P.isConnectedSkew_cells) hcopies).1.interior =
      cellSchur (diagramInterior P.cells) P.isConnectedSkew_cells.1.interior ^ copies := by
  let h := emptyMarkH_isLegal P.isConnectedSkew_cells
  have hc := (emptyMarkH P.cells).compose_horizontalRow hcopies
  calc
    _ = cellSchur (diagramInterior ((emptyMarkH P.cells).rowCopies copies))
        (h.isConnectedSkew_rowCopies_all hcopies).1.interior :=
      cellSchur_congr (congrArg diagramInterior hc) _ _
    _ = _ := h.interiorSchur_rowCopies_empty rfl hcopies

/-- Every profile of the literal positive-length empty row has the exact original corner power. -/
theorem originalEmptyHorizontal_profile_inventory {n m : ℕ} (P : Profile n) (Q : Profile m)
    (copies : ℕ) (hcopies : 1 ≤ copies) (v : ℤ × ℤ)
    (hv : (emptyMarkH P.cells).compose (horizontalRow copies) = translate v Q.cells) :
    (jtMatrix (fun j : Fin m => Q.xi j.succ) (fun j => Q.zeta j.castSucc)).det =
      (jtMatrix (fun j : Fin n => P.xi j.succ) (fun j => P.zeta j.castSucc)).det ^ copies := by
  have hc := originalEmptyHorizontal_corner_inventory P copies hcopies
  have he : diagramInterior ((emptyMarkH P.cells).compose (horizontalRow copies)) =
      translate v (diagramInterior Q.cells) := by rw [hv, interior_translate]
  have ht := cellSchur_congr he
    (MarkedInner.IsLegal.isConnectedSkew_compose_horizontalRow_all
      (emptyMarkH_isLegal P.isConnectedSkew_cells) hcopies).1.interior
    (isSkew_translate v Q.isConnectedSkew_cells.1.interior)
  rw [SkewGluing.cellSchur_translate (diagramInterior Q.cells)
    Q.isConnectedSkew_cells.1.interior v] at ht
  have h := ht.symm.trans hc
  simpa only [← Profile.minorDet_eq_interiorSchur, betaDet, jtMatrix] using h

/-- Both complete actual copies, including all repeated component functions, contribute once. -/
theorem originalHorizontalClosure_corner_inventory {n : ℕ} (P : Profile n) :
    cellSchur (diagramInterior (originalHorizontalClosure P))
        (originalHorizontalClosure_connected P).1.interior =
      cellSchur (diagramInterior P.cells) P.isConnectedSkew_cells.1.interior ^ 2 := by
  let h := emptyMarkH_isLegal P.isConnectedSkew_cells
  have hc : originalHorizontalClosure P = (emptyMarkH P.cells).rowCopies 2 :=
    (emptyMarkH P.cells).compose_horizontalRow (by decide)
  calc
    _ = cellSchur (diagramInterior ((emptyMarkH P.cells).rowCopies 2))
        (h.isConnectedSkew_rowCopies_all (by decide)).1.interior :=
      cellSchur_congr (congrArg diagramInterior hc) _ _
    _ = _ := h.interiorSchur_rowCopies_empty rfl (by decide)

/-- A profile of the literal translated closure realizes the original square inventory exactly. -/
theorem originalHorizontalClosure_profile_inventory {n m : ℕ} (P : Profile n) (Q : Profile m)
    (v : ℤ × ℤ) (hv : originalHorizontalClosure P = translate v Q.cells) :
    (jtMatrix (fun j : Fin m => Q.xi j.succ) (fun j => Q.zeta j.castSucc)).det =
      (jtMatrix (fun j : Fin n => P.xi j.succ) (fun j => P.zeta j.castSucc)).det ^ 2 := by
  have hc := originalHorizontalClosure_corner_inventory P
  have he : diagramInterior (originalHorizontalClosure P) =
      translate v (diagramInterior Q.cells) := by rw [hv, interior_translate]
  have ht := cellSchur_congr he
    (originalHorizontalClosure_connected P).1.interior
    (isSkew_translate v Q.isConnectedSkew_cells.1.interior)
  rw [SkewGluing.cellSchur_translate (diagramInterior Q.cells)
    Q.isConnectedSkew_cells.1.interior v] at ht
  have h := ht.symm.trans hc
  simpa only [← Profile.minorDet_eq_interiorSchur, betaDet, jtMatrix] using h

namespace SelectedCoordinate

variable {D : Diagram} {hD : IsConnectedSkew D}

/-- The complete removed determinant of the literal closure is the original square.
No component count, removed-factor inventory or normal-order cancellation is assumed. -/
theorem originalHorizontalClosure_removed_square {n m : ℕ} (P : Profile n) (Q : Profile m)
    (v : ℤ × ℤ) (hv : originalHorizontalClosure P = translate v Q.cells) :
    (originalRemovedMatrix (hD := hD) Q).det =
      (originalRemovedMatrix (hD := hD) P).det ^ 2 := by
  have hc := originalHorizontalClosure_profile_inventory P Q v hv
  simpa only [pow_one] using
    (originalRemovedMatrix_pair_power (hD := hD) Q P 2 1 (by simpa only [pow_one] using hc))

end SelectedCoordinate

end SkewCornerDescent.Matrix
