/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.LiteralOverlapInventory
import SkewCornerDescent.Matrix.OriginalDefectFactors

/-!
# Full removed-factor cancellation on literal window profiles

Formalizes `shields-2026-skew-corner-descent.tex`, «Actual responses and residue classes»
(`sec:normal-chart`, `lem:actual-words`). The overlap and horizontal closure inventories are
produced from their complete actual cells. Original corner powers are standing assumptions;
no selected multiplicity, removed-factor law or cancellation premise is carried. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D}

/-- Complete actual end windows close the full removed-factor part of the determinant defect.
Both profile realization equalities name literal diagrams, not Schur-equivalent substitutes. -/
theorem originalFullWindow_removed_cancel {n m k l : ℕ}
    (U : Profile n) (W : Profile m) (A : Profile k) (H : Profile l)
    (q w : ℤ) (v a z h : ℤ × ℤ)
    (hmin : minContent U.cells = 0) (hv : content v = q - w)
    (hbound : ∀ x ∈ U.cells, 0 ≤ content x ∧ content x < q)
    (hwindow : U.cells.filter (fun x => q - w ≤ content x ∧ content x < q) =
      translate v (U.cells.filter fun x => 0 ≤ content x ∧ content x < w))
    (hWcells : translate z W.cells = U.cells.filter fun x => 0 ≤ content x ∧ content x < w)
    (hAcells : U.cells ∪ translate v U.cells = translate a A.cells)
    (hHcells : originalHorizontalClosure U = translate h H.cells)
    (Λ : Lambda) (b c d : ℕ) (hc : c ≤ b) (hd : d + c = b)
    (hKU : (jtMatrix (fun j : Fin n => U.xi j.succ)
      (fun j => U.zeta j.castSucc)).det = Λ ^ b)
    (hKW : (jtMatrix (fun j : Fin m => W.xi j.succ)
      (fun j => W.zeta j.castSucc)).det = Λ ^ c) :
    (originalRemovedMatrix (hD := hD) A).det ^ b =
      (originalRemovedMatrix (hD := hD) W).det ^ b *
        (originalRemovedMatrix (hD := hD) H).det ^ d := by
  have hUs : IsSkew (U.cells ∪ translate v U.cells) := by
    rw [hAcells]
    exact isSkew_translate a A.isConnectedSkew_cells.1
  have hKU' : cellSchur (diagramInterior U.cells) U.isConnectedSkew_cells.1.interior = Λ ^ b := by
    simpa only [← Profile.minorDet_eq_interiorSchur, betaDet, jtMatrix] using hKU
  have hKW' : cellSchur (diagramInterior (translate z W.cells))
      (isSkew_translate z W.isConnectedSkew_cells.1).interior = Λ ^ c := by
    calc
      _ = cellSchur (translate z (diagramInterior W.cells))
          (isSkew_translate z W.isConnectedSkew_cells.1.interior) :=
        cellSchur_congr (interior_translate W.cells z) _ _
      _ = cellSchur (diagramInterior W.cells) W.isConnectedSkew_cells.1.interior :=
        SkewGluing.cellSchur_translate (diagramInterior W.cells)
          W.isConnectedSkew_cells.1.interior z
      _ = _ := by
        simpa only [← Profile.minorDet_eq_interiorSchur, betaDet, jtMatrix] using hKW
  have hp := literalOverlap_corner_power U.cells (translate z W.cells) U.isConnectedSkew_cells
    (isSkew_translate z W.isConnectedSkew_cells.1) q w v hmin hv hbound hwindow hWcells hUs
    Λ b c hc hKU' hKW'
  have he : diagramInterior (U.cells ∪ translate v U.cells) =
      translate a (diagramInterior A.cells) := by rw [hAcells, interior_translate]
  have ht := cellSchur_congr he hUs.interior (isSkew_translate a A.isConnectedSkew_cells.1.interior)
  rw [SkewGluing.cellSchur_translate (diagramInterior A.cells) A.isConnectedSkew_cells.1.interior a]
    at ht
  have hKA : (jtMatrix (fun j : Fin k => A.xi j.succ)
      (fun j => A.zeta j.castSucc)).det = Λ ^ (2 * b - c) := by
    simpa only [← Profile.minorDet_eq_interiorSchur, betaDet, jtMatrix] using ht.symm.trans hp
  exact originalRemovedMatrix_actual_defect_cancel U W A H h hHcells Λ b c d hc hd hKU hKW hKA

end SkewCornerDescent.Matrix.SelectedCoordinate
