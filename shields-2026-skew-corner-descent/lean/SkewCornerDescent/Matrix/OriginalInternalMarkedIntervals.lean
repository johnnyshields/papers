/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalInternalMarkedDerivative
import SkewCornerDescent.Matrix.HessenbergMarkedFrontierReduction

/-!
# Exact actual marked frontiers as full intervals and disjoint pairs

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
Original generator support supplies every shorter-entry exclusion. Complete
normal inverse weights remain in both selected cost frontiers.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing CyclicWindows

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The actual marked sums at the two surviving costs reduce to literal full
intervals and disjoint pair intervals, with all normal orders retained. -/
theorem originalInternal_marked_frontier_intervals {n : ℕ} (P : Profile n)
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
    let marked := fun σ : Equiv.Perm (Fin (originalSelectedCount (hD := hD) P - 1)) =>
      let upper := Finset.univ.filter (fun j => j.val ≤ (σ j).val)
      ∑ i ∈ upper, (δ (A i (σ i)) * ∏ k ∈ Finset.Icc i (σ i), w k) *
        ∏ j ∈ upper.erase i, A j (σ j) * ∏ k ∈ Finset.Icc j (σ j), w k
    let frontier := fun m =>
      ∑ σ : Equiv.Perm (Fin (originalSelectedCount (hD := hD) P - 1)),
        if (∀ j, j.val ≤ (σ j).val + 1) ∧
          (Finset.univ.filter (fun j => (σ j).val < j.val)).card = m then marked σ else 0
    frontier (d * r - 1) =
      (∑ i : Fin (originalSelectedCount (hD := hD) P - 1), ∑ j,
        if i.val ≤ j.val ∧ j.val - i.val = d * r - 1 then
          δ (A i j) * ∏ k ∈ Finset.Icc i j, w k else 0) ∧
    frontier (d * r) =
      (∑ i : Fin (originalSelectedCount (hD := hD) P - 1), ∑ j,
        if i.val ≤ j.val ∧ j.val - i.val = d * r then
          δ (A i j) * ∏ k ∈ Finset.Icc i j, w k else 0) +
      ∑ p : OneShyIntervalPair (originalSelectedCount (hD := hD) P - 1) (d * r),
        (δ (A p.longStart p.longEnd) * ∏ k ∈ Finset.Icc p.longStart p.longEnd, w k) *
          (A p.pairStart p.pairEnd * ∏ k ∈ Finset.Icc p.pairStart p.pairEnd, w k) := by
  classical
  let K := c.originalInternalPeriodHigherIndex P r d hn hp J H hH
  let δ := residueSeriesGeneratorDeriv c.top ⟨K.val, ne_of_gt K.property⟩
  let A := (c.originalInternalResponseMatrix P).map c.normalSeries
  let w := fun j => (A j j)⁻¹
  have hdiag (j) : A j j * w j = 1 :=
    PowerSeries.mul_inv_cancel _
      (c.originalInternal_normal_diagonal_ne_zero P (NeZero.pos _) hmax j)
  have hheight : d • windowSum
      (fun x => c.originalCompletedGap P ((ZMod.finEquiv _).symm x)) 1 r 0 < (K.val : ℤ) := by
    change d • windowSum
      (fun x => c.originalCompletedGap P ((ZMod.finEquiv _).symm x)) 1 r 0 < (H : ℤ)
    have hJ := J.pos
    omega
  have hshort (i j : Fin (originalSelectedCount (hD := hD) P - 1))
      (hij : i.val ≤ j.val) (hlen : j.val - i.val + 1 < d * r) : δ (A i j) = 0 :=
    c.originalInternal_normal_entry_short P hmax r d hp K.val K.property hheight i j hij hlen
  dsimp only
  constructor
  · exact hessenberg_marked_one_length_sum A (fun i j => δ (A i j)) w hdiag
      (fun i j hij hlen => hshort i j hij (by omega))
  · exact hessenberg_marked_two_length_sum hn A (fun i j => δ (A i j)) w hdiag hshort

end SkewCornerDescent.Matrix.SelectedCoordinate
