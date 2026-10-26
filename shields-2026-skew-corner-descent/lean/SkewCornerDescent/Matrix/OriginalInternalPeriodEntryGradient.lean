/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalNormalPeriodGradient
import SkewCornerDescent.Matrix.OriginalInternalMarkedDerivative

/-!
# Complete period-entry gradients at the actual internal matrix interface

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
Internal row and column positions are the exact selected endpoint occurrences.
The full period-length response gradient is supplied by the original source.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing CyclicWindows

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- An actual internal matrix entry is precisely its two original selected endpoints. -/
theorem originalInternalResponseMatrix_selected_entry {n : ℕ} (P : Profile n)
    (i j : Fin (originalSelectedCount (hD := hD) P - 1)) :
    c.originalInternalResponseMatrix P i j = c.originalLocalResponse P
      (some (originalSelectedEnumeration P ⟨i.val, by have := i.isLt; omega⟩))
      (some (originalSelectedEnumeration P ⟨j.val + 1, by have := j.isLt; omega⟩)) := by
  let a : Fin (originalSelectedCount (hD := hD) P) := ⟨i.val, by have := i.isLt; omega⟩
  let b : Fin (originalSelectedCount (hD := hD) P) := ⟨j.val + 1, by have := j.isLt; omega⟩
  change c.originalLocalResponse P (originalHessenbergRows P a.succ)
    (originalHessenbergCols P b.castSucc) = _
  rw [originalHessenbergRows_succ, originalHessenbergCols_castSucc]

/-- Every complete period-length entry of the unchanged internal normal matrix has
the actual raw selected-function gradient as a constant series, at every normal order. -/
theorem originalInternal_period_entry_gradient {n m : ℕ} (P : Profile n) (W : Profile m)
    [NeZero (originalSelectedCount (hD := hD) P)]
    (q : ℤ) (u v : ℤ × ℤ) (hv : content v = q)
    (hW : P.cells.filter (fun x => 0 ≤ content x ∧ content x < P.xi 0 - q) =
      translate u W.cells)
    (hwindow : P.cells.filter (fun x => q ≤ content x ∧ content x < P.xi 0) =
      translate v (P.cells.filter fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hq : diagLo P.cells q = diagHi P.cells q)
    (hLq : diagLo P.cells (P.xi 0 - q) = diagHi P.cells (P.xi 0 - q))
    (hC : 0 < originalSelectedCount (hD := hD) W)
    (r d : ℕ) (hn : 2 ≤ d * r)
    (hdiff : originalSelectedCount (hD := hD) P -
      originalSelectedCount (hD := hD) W = r * d)
    (hresponse : ∀ i j : Fin (originalSelectedCount (hD := hD) P - 1),
      j.val = i.val + r → c.originalInternalResidue P i = c.originalInternalResidue P j)
    (hp : Function.Periodic
      (fun x => c.originalCompletedGap P ((ZMod.finEquiv _).symm x))
      (r : ZMod (originalSelectedCount (hD := hD) P)))
    (i j : Fin (originalSelectedCount (hD := hD) P - 1))
    (hlen : j.val + 1 = i.val + d * r) (J H : ℕ+)
    (hH : (H : ℤ) = d • windowSum
      (fun x => c.originalCompletedGap P ((ZMod.finEquiv _).symm x)) 1 r 0 + (J : ℤ)) :
    let K := c.originalInternalPeriodHigherIndex P r d hn hp J H hH
    residueSeriesGeneratorDeriv c.top ⟨K.val, ne_of_gt K.property⟩
      (c.normalSeries (c.originalInternalResponseMatrix P i j)) =
    PowerSeries.C (c.normalCoefficient⁻¹ *
      c.residueMap (MvPolynomial.pderiv J (cellSchur D hD.1))) := by
  have hpos : 0 < d * r := by omega
  have hd : 0 < d := by
    by_contra h
    have hz : d = 0 := by omega
    rw [hz, zero_mul] at hpos
    exact (lt_irrefl 0) hpos
  have hr : 0 < r := by
    by_contra h
    have hz : r = 0 := by omega
    rw [hz, mul_zero] at hpos
    exact (lt_irrefl 0) hpos
  rw [c.originalInternalResponseMatrix_selected_entry P i j]
  exact c.original_period_response_normal_gradient P W q u v hv hW hwindow hq hLq hC
    r d hr hd hdiff hresponse hp _ _ hlen J H hH

end SkewCornerDescent.Matrix.SelectedCoordinate
