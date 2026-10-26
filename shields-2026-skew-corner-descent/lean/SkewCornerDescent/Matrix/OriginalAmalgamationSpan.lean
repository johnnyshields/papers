/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.OriginalAmalgamationInventory
import SkewGluing.ComponentOrders

/-!
# Component span bounds for the actual amalgamation

Supports `shields-2026-skew-corner-descent.tex` (`lem:actual-words`, `lem:original-transfer`).
The complete literal corner product makes each union component divide the square of the
source interior Schur polynomial. Its generator span is therefore bounded by the source
component span. No union component bound is assumed. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

private theorem component_span_of_interior_dvd {n m : ℕ} (P : Profile n) (Q : Profile m)
    (N : ℕ) (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ N)
    (hdiv : cellSchur (diagramInterior Q.cells) Q.isConnectedSkew_cells.1.interior ∣
      cellSchur (diagramInterior P.cells) P.isConnectedSkew_cells.1.interior ^ 2) :
    ∀ C ∈ edgeComponents (diagramInterior Q.cells), span C ≤ N := by
  classical
  have hs : polynomialSpan
      (cellSchur (diagramInterior P.cells) P.isConnectedSkew_cells.1.interior) ≤ N := by
    apply polynomialSpan_prod_le
    intro C _
    rw [← cellSchur_eq_connected (isConnectedSkew_component
      P.isConnectedSkew_cells.1.interior C.property),
      polynomialSpan_cellSchur (isConnectedSkew_component
        P.isConnectedSkew_cells.1.interior C.property)]
    exact hmax C.val C.property
  intro C hC
  have hd := component_cellSchur_dvd Q.isConnectedSkew_cells.1.interior hC
  have hb := polynomialSpan_le_of_dvd
    (pow_ne_zero 2 (cellSchur_ne_zero _ P.isConnectedSkew_cells.1.interior)) (hd.trans hdiv)
  rw [polynomialSpan_cellSchur
    (isConnectedSkew_component Q.isConnectedSkew_cells.1.interior hC)] at hb
  exact hb.trans ((polynomialSpan_pow_le _ 2).trans hs)

/-- Literal overlap preserves the upper span bound for every actual interior component. -/
theorem originalAmalgamation_component_span {n m k : ℕ}
    (P : Profile n) (W : Profile k) (A : Profile m) (q : ℤ) (v u z : ℤ × ℤ)
    (hv : content v = q)
    (hwindow : P.cells.filter (fun x => q ≤ content x ∧ content x < P.xi 0) =
      translate v (P.cells.filter fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hW : translate z W.cells = P.cells.filter
      (fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hA : P.cells ∪ translate v P.cells = translate u A.cells)
    (N : ℕ) (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ N) :
    ∀ C ∈ edgeComponents (diagramInterior A.cells), span C ≤ N := by
  have hp := originalAmalgamation_interiorSchur_product P W A q v u z hv hwindow hW hA
  exact component_span_of_interior_dvd P A N hmax
    ⟨cellSchur (diagramInterior W.cells) W.isConnectedSkew_cells.1.interior, hp.symm⟩

/-- The same literal corner product supplies the source span bound for every
actual common-window component. No window component bound is assumed. -/
theorem originalWindow_component_span {n m k : ℕ}
    (P : Profile n) (W : Profile k) (A : Profile m) (q : ℤ) (v u z : ℤ × ℤ)
    (hv : content v = q)
    (hwindow : P.cells.filter (fun x => q ≤ content x ∧ content x < P.xi 0) =
      translate v (P.cells.filter fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hW : translate z W.cells = P.cells.filter
      (fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hA : P.cells ∪ translate v P.cells = translate u A.cells)
    (N : ℕ) (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ N) :
    ∀ C ∈ edgeComponents (diagramInterior W.cells), span C ≤ N := by
  have hp := originalAmalgamation_interiorSchur_product P W A q v u z hv hwindow hW hA
  apply component_span_of_interior_dvd P W N hmax
  refine ⟨cellSchur (diagramInterior A.cells) A.isConnectedSkew_cells.1.interior, ?_⟩
  rw [mul_comm]
  exact hp.symm

end SkewCornerDescent.Matrix.SelectedCoordinate
