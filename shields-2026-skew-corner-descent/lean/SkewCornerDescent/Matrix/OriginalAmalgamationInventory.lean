/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalAmalgamationWindows
import SkewCornerDescent.Matrix.OriginalMultiplicity

/-!
# Actual selected inventory of the amalgamation

Supports `shields-2026-skew-corner-descent.tex` (`lem:actual-words`). The complete
literal overlap supplies its shared corner factors. Prime order then counts every
selected occurrence in the actual union, including repeated factors. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D}

/-- The complete literal overlap gives the full interior Schur product, before any
selected-prime valuation is taken. -/
theorem originalAmalgamation_interiorSchur_product {n m k : ℕ}
    (P : Profile n) (W : Profile k) (A : Profile m) (q : ℤ) (v u z : ℤ × ℤ)
    (hv : content v = q)
    (hwindow : P.cells.filter (fun x => q ≤ content x ∧ content x < P.xi 0) =
      translate v (P.cells.filter fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hW : translate z W.cells = P.cells.filter
      (fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hA : P.cells ∪ translate v P.cells = translate u A.cells) :
    cellSchur (diagramInterior A.cells) A.isConnectedSkew_cells.1.interior *
      cellSchur (diagramInterior W.cells) W.isConnectedSkew_cells.1.interior =
        cellSchur (diagramInterior P.cells) P.isConnectedSkew_cells.1.interior ^ 2 := by
  have hbound : ∀ x ∈ P.cells, 0 ≤ content x ∧ content x < P.xi 0 := by
    intro x hx
    have hlo := minContent_le (content_mem_contents hx)
    have hhi := le_maxContent (content_mem_contents hx)
    rw [P.minContent_cells] at hlo
    rw [P.maxContent_cells] at hhi
    exact ⟨hlo, by omega⟩
  have hU : IsSkew (P.cells ∪ translate v P.cells) := by
    rw [hA]
    exact isSkew_translate u A.isConnectedSkew_cells.1
  have hp := literalOverlap_corner_product P.cells (translate z W.cells)
    P.isConnectedSkew_cells (isSkew_translate z W.isConnectedSkew_cells.1)
    (P.xi 0) (P.xi 0 - q) v P.minContent_cells (by omega) hbound
    (by simpa only [sub_sub_cancel] using hwindow) hW hU
  have heA : diagramInterior (P.cells ∪ translate v P.cells) =
      translate u (diagramInterior A.cells) := by rw [hA, interior_translate]
  have htA := cellSchur_congr heA hU.interior
    (isSkew_translate u A.isConnectedSkew_cells.1.interior)
  rw [cellSchur_translate _ A.isConnectedSkew_cells.1.interior u] at htA
  have htW : cellSchur (diagramInterior (translate z W.cells))
      (isSkew_translate z W.isConnectedSkew_cells.1).interior =
      cellSchur (diagramInterior W.cells) W.isConnectedSkew_cells.1.interior := by
    exact (cellSchur_congr (interior_translate W.cells z)
      (isSkew_translate z W.isConnectedSkew_cells.1).interior
      (isSkew_translate z W.isConnectedSkew_cells.1.interior)).trans
      (cellSchur_translate _ W.isConnectedSkew_cells.1.interior z)
  rw [htA, htW] at hp
  exact hp

/-- The literal shared window determines the union count without a count correspondence input. -/
theorem originalAmalgamation_selected_inventory {n m k : ℕ}
    (P : Profile n) (W : Profile k) (A : Profile m) (q : ℤ) (v u z : ℤ × ℤ)
    (hv : content v = q)
    (hwindow : P.cells.filter (fun x => q ≤ content x ∧ content x < P.xi 0) =
      translate v (P.cells.filter fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hW : translate z W.cells = P.cells.filter
      (fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hA : P.cells ∪ translate v P.cells = translate u A.cells) :
    originalSelectedCount (hD := hD) A + originalSelectedCount (hD := hD) W =
      2 * originalSelectedCount (hD := hD) P := by
  have hp := originalAmalgamation_interiorSchur_product P W A q v u z hv hwindow hW hA
  have hval := congrArg (primeOrder (cellSchur D hD.1)) hp
  rw [primeOrder_mul (irreducible_cellSchur hD).prime (cellSchur_ne_zero _ _)
      (cellSchur_ne_zero _ _), primeOrder_pow (irreducible_cellSchur hD).prime
      2] at hval
  have hcount {s : ℕ} (Q : Profile s) : originalSelectedCount (hD := hD) Q =
      primeOrder (cellSchur D hD.1)
        (cellSchur (diagramInterior Q.cells) Q.isConnectedSkew_cells.1.interior) := by
    rw [originalSelectedCount_eq_primeOrder, ← Profile.minorDet_eq_interiorSchur]
    rfl
  rw [← hcount A, ← hcount W, ← hcount P] at hval
  exact hval

end SkewCornerDescent.Matrix.SelectedCoordinate
