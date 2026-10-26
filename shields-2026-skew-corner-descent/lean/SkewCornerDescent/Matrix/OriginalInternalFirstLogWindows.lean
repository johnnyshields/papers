/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalInternalFirstLogIntervals
import SkewCornerDescent.Matrix.MatrixIntervalCharges

/-!
# Complete first normal logarithm as full local matrix windows

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
The full onsite and adjacent-pair sums are genuine one-state and two-state
matrix-window functionals, retaining every original first normal jet.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The complete first normalized internal logarithm is the difference of the
full onsite window sum and the complete pair-window sum. -/
theorem originalInternal_first_log_windows {n : ℕ} (P : Profile n)
    (hB : 2 ≤ originalSelectedCount (hD := hD) P)
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ)) :
    let M := (c.originalInternalResponseMatrix P).map c.normalSeries
    let onsite := fun V : Matrix (Fin 1) (Fin 1) (PowerSeries (OtherField c.top)) =>
      PowerSeries.coeff 1 (V 0 0) * (PowerSeries.constantCoeff (V 0 0))⁻¹
    let pair := fun V : Matrix (Fin 2) (Fin 2) (PowerSeries (OtherField c.top)) =>
      PowerSeries.constantCoeff (V 0 (Fin.last 1)) *
        ∏ k, (PowerSeries.constantCoeff (V k k))⁻¹
    PowerSeries.coeff 1 (PowerSeries.logOf
      (PowerSeries.C (PowerSeries.constantCoeff M.det)⁻¹ * M.det)) =
      (∑ s, onsite (contiguousMatrixWindow M 1 s)) -
        c.normalCoefficient⁻¹ * (∑ s, pair (contiguousMatrixWindow M 2 s)) := by
  let M := (c.originalInternalResponseMatrix P).map c.normalSeries
  let ν := fun p : PowerSeries (OtherField c.top) =>
    PowerSeries.coeff 1 p * (PowerSeries.constantCoeff p)⁻¹
  let pair := fun V : Matrix (Fin 2) (Fin 2) (PowerSeries (OtherField c.top)) =>
    PowerSeries.constantCoeff (V 0 (Fin.last 1)) *
      ∏ k, (PowerSeries.constantCoeff (V k k))⁻¹
  have hons : (∑ i, ν (M i i)) =
      ∑ s, ν (contiguousMatrixWindow M 1 s 0 0) := by
    apply Fintype.sum_equiv (finCongr (show originalSelectedCount (hD := hD) P - 1 =
      (originalSelectedCount (hD := hD) P - 1) + 1 - 1 by omega))
    intro i
    simp only [contiguousMatrixWindow, Matrix.submatrix_apply, Fin.val_zero, Nat.add_zero]
    rfl
  have hp := matrix_interval_charge_windows 1 M
    (fun p => PowerSeries.constantCoeff p) (fun p => (PowerSeries.constantCoeff p)⁻¹)
  have hpred (i j : Fin (originalSelectedCount (hD := hD) P - 1)) :
      i.val ≤ j.val ∧ j.val - i.val = 1 ↔ j.val = i.val + 1 := by omega
  simp only [hpred] at hp
  have hpair : (∑ i : Fin (originalSelectedCount (hD := hD) P - 1), ∑ j,
      if j.val = i.val + 1 then PowerSeries.constantCoeff (M i j) *
        ∏ k ∈ Finset.Icc i j, (PowerSeries.constantCoeff (M k k))⁻¹ else 0) =
      ∑ s, pair (contiguousMatrixWindow M 2 s) :=
    hp.trans (contiguousMatrixWindow_sum_starts M 1 pair)
  have h := c.originalInternal_first_log_intervals P hB hmax
  change PowerSeries.coeff 1 (PowerSeries.logOf
    (PowerSeries.C (PowerSeries.constantCoeff M.det)⁻¹ * M.det)) =
      (∑ i, ν (M i i)) - _ at h
  dsimp only
  exact h.trans (by rw [hons, hpair])

end SkewCornerDescent.Matrix.SelectedCoordinate
