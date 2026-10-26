/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalInternalPartitionLog
import SkewCornerDescent.Matrix.OriginalInternalMarkedFirstCoefficient

/-!
# Complete original logarithmic coefficient from marked interval activities

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
The exact logarithmic subtraction retains the full first partition coefficient
and both normal determinant frontiers, including every cost-two mark.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing CyclicWindows

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The complete original normalized logarithm consists of the full long-interval
residue, the full disjoint-pair residue, and the entire lower-cost normal jet
minus its exact first-partition-coefficient correction. -/
theorem originalInternal_marked_log_interval_coefficient {n : ℕ} (P : Profile n)
    [NeZero (originalSelectedCount (hD := hD) P)]
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ))
    (r d : ℕ) (hn : 2 ≤ d * r)
    (hp : Function.Periodic
      (fun x => c.originalCompletedGap P ((ZMod.finEquiv _).symm x))
      (r : ZMod (originalSelectedCount (hD := hD) P)))
    (J H : ℕ+)
    (hH : (H : ℤ) = d • windowSum
      (fun x => c.originalCompletedGap P ((ZMod.finEquiv _).symm x)) 1 r 0 + (J : ℤ)) :
    let K := c.originalInternalPeriodHigherIndex P r d hn hp J H hH
    let δ := residueSeriesGeneratorDeriv c.top ⟨K.val, ne_of_gt K.property⟩
    let A := (c.originalInternalResponseMatrix P).map c.normalSeries
    let w := fun j => (A j j)⁻¹
    let m := d * r
    let interval := fun L =>
      ∑ i : Fin (originalSelectedCount (hD := hD) P - 1), ∑ j,
        if i.val ≤ j.val ∧ j.val - i.val = L then
          δ (A i j) * ∏ k ∈ Finset.Icc i j, w k else 0
    let pair := ∑ p : OneShyIntervalPair (originalSelectedCount (hD := hD) P - 1) m,
      (δ (A p.longStart p.longEnd) * ∏ k ∈ Finset.Icc p.longStart p.longEnd, w k) *
        (A p.pairStart p.pairEnd * ∏ k ∈ Finset.Icc p.pairStart p.pairEnd, w k)
    residueGeneratorDeriv c.top ⟨K.val, ne_of_gt K.property⟩
      (PowerSeries.coeff m (PowerSeries.logOf
        (PowerSeries.C (PowerSeries.constantCoeff A.det)⁻¹ * A.det))) =
      (-1 : OtherField c.top) ^ m * c.normalCoefficient⁻¹ ^ m *
        PowerSeries.constantCoeff (interval m + pair) +
      (-1 : OtherField c.top) ^ (m - 1) * c.normalCoefficient⁻¹ ^ (m - 1) *
        (PowerSeries.coeff 1 (interval (m - 1)) -
          PowerSeries.coeff 1 (A.det * ∏ j, w j) *
            PowerSeries.constantCoeff (interval (m - 1))) := by
  have hlog := c.originalInternal_partition_log_next P hmax r d hn hp J H hH
  have hm := c.originalInternal_marked_interval_coefficient P hmax r d hn hp J H hH
  have hf := c.originalInternal_marked_first_interval_coefficient P hmax r d hn hp J H hH
  dsimp only at hlog hm hf ⊢
  rw [hlog, hm, hf]
  ring

end SkewCornerDescent.Matrix.SelectedCoordinate
