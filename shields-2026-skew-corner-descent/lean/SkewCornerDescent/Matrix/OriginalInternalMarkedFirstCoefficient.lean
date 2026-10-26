/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalInternalMarkedIntervals
import SkewCornerDescent.Matrix.NormalMarkedFirstCoefficient

/-!
# First actual marked interval coefficient below the next normal cost

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
Whole short-entry independence and exact marked interval indexing produce
the first fresh normalized coefficient from the original source.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing CyclicWindows

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The lower marked frontier is exactly the residue of its complete interval
activity sum, including every original inverse-diagonal occurrence. -/
theorem originalInternal_marked_first_interval_coefficient {n : ℕ} (P : Profile n)
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
    residueGeneratorDeriv c.top ⟨K.val, ne_of_gt K.property⟩
      (PowerSeries.coeff (d * r - 1) (A.det * ∏ j, w j)) =
      (-1 : OtherField c.top) ^ (d * r - 1) * c.normalCoefficient⁻¹ ^ (d * r - 1) *
        PowerSeries.constantCoeff
          (∑ i : Fin (originalSelectedCount (hD := hD) P - 1), ∑ j,
            if i.val ≤ j.val ∧ j.val - i.val = d * r - 1 then
              δ (A i j) * ∏ k ∈ Finset.Icc i j, w k else 0) := by
  let K := c.originalInternalPeriodHigherIndex P r d hn hp J H hH
  let δ := residueSeriesGeneratorDeriv c.top ⟨K.val, ne_of_gt K.property⟩
  let A := (c.originalInternalResponseMatrix P).map c.normalSeries
  let w := fun j => (A j j)⁻¹
  let marked := fun σ : Equiv.Perm (Fin (originalSelectedCount (hD := hD) P - 1)) =>
    let upper := Finset.univ.filter (fun j => j.val ≤ (σ j).val)
    ∑ i ∈ upper, (δ (A i (σ i)) * ∏ k ∈ Finset.Icc i (σ i), w k) *
      ∏ j ∈ upper.erase i, A j (σ j) * ∏ k ∈ Finset.Icc j (σ j), w k
  have hheight : d • windowSum
      (fun x => c.originalCompletedGap P ((ZMod.finEquiv _).symm x)) 1 r 0 < (K.val : ℤ) := by
    change d • windowSum
      (fun x => c.originalCompletedGap P ((ZMod.finEquiv _).symm x)) 1 r 0 < (H : ℤ)
    have hJ := J.pos
    omega
  have hprev (σ : Equiv.Perm (Fin (originalSelectedCount (hD := hD) P - 1)))
      (hσ : ∀ j, j.val ≤ (σ j).val + 1)
      (hcost : (Finset.univ.filter (fun j => (σ j).val < j.val)).card < d * r - 1) :
      marked σ = 0 := by
    dsimp only [marked]
    apply Finset.sum_eq_zero
    intro i hi
    have hiup := (Finset.mem_filter.mp hi).2
    have hb := hessenberg_permutation_interval_cost σ hσ i hiup
    have hz : δ (A i (σ i)) = 0 :=
      c.originalInternal_normal_entry_short P hmax r d hp K.val K.property hheight
        i (σ i) hiup (by omega)
    rw [hz, zero_mul, zero_mul]
  have hexp := c.originalInternal_det_marked_derivative P hmax r d hn hp J H hH
  have hparts := (c.originalInternal_marked_frontier_intervals P hmax r d hn hp J H hH).1
  have hg := normal_marked_first_coeff
    (fun σ : Equiv.Perm (Fin (originalSelectedCount (hD := hD) P - 1)) =>
      ∀ j, j.val ≤ (σ j).val + 1)
    (fun σ => (Finset.univ.filter (fun j => (σ j).val < j.val)).card)
    marked c.normalCoefficient⁻¹ (d * r - 1) hprev
  dsimp only
  rw [← residueSeriesGeneratorDeriv_coeff]
  change PowerSeries.coeff (d * r - 1) (δ (A.det * ∏ j, w j)) = _
  rw [hexp]
  refine hg.trans ?_
  dsimp only at hparts
  rw [hparts]

end SkewCornerDescent.Matrix.SelectedCoordinate
