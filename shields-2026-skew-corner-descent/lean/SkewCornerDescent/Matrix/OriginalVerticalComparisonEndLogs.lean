/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalAmalgamationEndLogLocality
import SkewCornerDescent.Matrix.OriginalVerticalEndLogLocality

/-!
# Complete weighted endpoint logarithmic cancellation with the actual vertical closure

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
The complete overlap union, source and actual vertical closure produce every cap
jet. Their outer-count balance cancels both full ends without freezing a unit.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Complete left and right cap logarithms cancel with the actual three-word weights
on the vertical-closure branch. Literal geometry supplies all four jet matches;
the outer-count balance is the only scalar assumption. -/
theorem originalVerticalComparison_end_log_balance {n m w h : ℕ}
    (P : Profile n) (W : Profile w) (A : Profile m) (V : Profile h)
    (q : ℤ) (shift u z l : ℤ × ℤ) (hq : 0 ≤ q) (hv : content shift = q)
    (hwindow : P.cells.filter (fun x => q ≤ content x ∧ content x < P.xi 0) =
      translate shift (P.cells.filter fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hW : translate z W.cells = P.cells.filter
      (fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hA : P.cells ∪ translate shift P.cells = translate u A.cells)
    (hV : originalVerticalClosure P = translate l V.cells)
    (hcutq : ∀ x ∈ diagramInterior P.cells, content x ≠ q)
    (hcutLq : ∀ x ∈ diagramInterior P.cells, content x ≠ P.xi 0 - q)
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ))
    (b a d : ℕ) (hd : d + a = b) (k : ℕ)
    (hk : k < originalSelectedCount (hD := hD) P) :
    let left := fun {s : ℕ} (X : Profile s) =>
      PowerSeries.coeff k (leftCap (c.originalNormalExtension X)
        (originalSelectedCount (hD := hD) X))
    let right := fun {s : ℕ} (X : Profile s) =>
      PowerSeries.coeff k (rightCap (c.originalNormalExtension X) 0
        (originalSelectedCount (hD := hD) X))
    (b : OtherField c.top) * left A - (a : OtherField c.top) * left P -
        (d : OtherField c.top) * left V = 0 ∧
      (b : OtherField c.top) * right A - (a : OtherField c.top) * right P -
        (d : OtherField c.top) * right V = 0 := by
  dsimp only
  rw [c.originalAmalgamation_left_log_coeff P W A q shift u z hq hv
      hwindow hW hA hcutq hcutLq hmax k hk,
    c.originalVerticalClosure_left_log_coeff P V l hV hmax k hk,
    c.originalAmalgamation_right_log_coeff P W A q shift u z hq hv
      hwindow hW hA hcutq hcutLq hmax k hk,
    c.originalVerticalClosure_right_log_coeff P V l hV hmax k hk]
  have hc : (d : OtherField c.top) + (a : OtherField c.top) = (b : OtherField c.top) := by
    exact_mod_cast hd
  constructor
  · linear_combination
      -(PowerSeries.coeff k (leftCap (c.originalNormalExtension P)
        (originalSelectedCount (hD := hD) P))) * hc
  · linear_combination
      -(PowerSeries.coeff k (rightCap (c.originalNormalExtension P) 0
        (originalSelectedCount (hD := hD) P))) * hc


end SkewCornerDescent.Matrix.SelectedCoordinate
