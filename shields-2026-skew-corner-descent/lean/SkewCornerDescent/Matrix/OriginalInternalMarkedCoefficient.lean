/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalInternalMarkedIntervals
import SkewCornerDescent.Matrix.TwoAdjacentFrontiers

/-!
# Complete original normalized coefficient from interval frontiers

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
Both full-cost activities and the entire lower-cost first jet are produced
from the actual internal determinant, with every disjoint pair mark retained.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing CyclicWindows

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The complete normalized determinant derivative has a full long-interval residue,
a full disjoint-pair residue, and a full first jet at the adjacent lower cost. -/
theorem originalInternal_marked_interval_coefficient {n : ℕ} (P : Profile n)
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
      (PowerSeries.coeff m (A.det * ∏ j, w j)) =
      (-1 : OtherField c.top) ^ m * c.normalCoefficient⁻¹ ^ m *
        PowerSeries.constantCoeff (interval m + pair) +
      (-1 : OtherField c.top) ^ (m - 1) * c.normalCoefficient⁻¹ ^ (m - 1) *
        PowerSeries.coeff 1 (interval (m - 1)) := by
  let K := c.originalInternalPeriodHigherIndex P r d hn hp J H hH
  let δ := residueSeriesGeneratorDeriv c.top ⟨K.val, ne_of_gt K.property⟩
  let A := (c.originalInternalResponseMatrix P).map c.normalSeries
  let w := fun j => (A j j)⁻¹
  let marked := fun σ : Equiv.Perm (Fin (originalSelectedCount (hD := hD) P - 1)) =>
    let upper := Finset.univ.filter (fun j => j.val ≤ (σ j).val)
    ∑ i ∈ upper, (δ (A i (σ i)) * ∏ k ∈ Finset.Icc i (σ i), w k) *
      ∏ j ∈ upper.erase i, A j (σ j) * ∏ k ∈ Finset.Icc j (σ j), w k
  have h := c.originalInternal_marked_two_costs P hmax r d hn hp J H hH
  have hparts := c.originalInternal_marked_frontier_intervals P hmax r d hn hp J H hH
  have hsum := sum_two_adjacent_frontiers
    (fun σ : Equiv.Perm (Fin (originalSelectedCount (hD := hD) P - 1)) =>
      ∀ j, j.val ≤ (σ j).val + 1)
    (fun σ => (Finset.univ.filter (fun j => (σ j).val < j.val)).card) marked
    (PowerSeries.constantCoeff (R := OtherField c.top)).toAddMonoidHom
    (PowerSeries.coeff (R := OtherField c.top) 1).toAddMonoidHom
    ((-1 : OtherField c.top) ^ (d * r) * c.normalCoefficient⁻¹ ^ (d * r))
    ((-1 : OtherField c.top) ^ (d * r - 1) * c.normalCoefficient⁻¹ ^ (d * r - 1))
    (d * r) (by omega)
  dsimp only at h hparts ⊢
  refine h.trans (hsum.trans ?_)
  rw [hparts.1, hparts.2]
  rfl

end SkewCornerDescent.Matrix.SelectedCoordinate
