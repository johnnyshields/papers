/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalInternalFirstJet
import SkewCornerDescent.Matrix.FirstLogCoefficient
import SkewCornerDescent.Matrix.AdjacentPairIndexing

/-!
# Complete first normalized logarithm in actual interval indices

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
The original onsite and adjacent-pair balance is reindexed without a residual
matrix equivalence in its statement. Original unit residues justify logarithmic
normalization. Every diagonal first jet and pair entry remains present.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The actual complete first normalized internal logarithm is its full onsite
sum minus the original closed-interval pair sum. No partition coefficient is
substituted for the whole first normal coefficient. -/
theorem originalInternal_first_log_intervals {n : ℕ} (P : Profile n)
    (hB : 2 ≤ originalSelectedCount (hD := hD) P)
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ)) :
    let M := (c.originalInternalResponseMatrix P).map c.normalSeries
    PowerSeries.coeff 1 (PowerSeries.logOf
      (PowerSeries.C (PowerSeries.constantCoeff M.det)⁻¹ * M.det)) =
      (∑ i, PowerSeries.coeff 1 (M i i) * (PowerSeries.constantCoeff (M i i))⁻¹) -
      c.normalCoefficient⁻¹ *
        (∑ i : Fin (originalSelectedCount (hD := hD) P - 1), ∑ j,
          if j.val = i.val + 1 then PowerSeries.constantCoeff (M i j) *
            ∏ k ∈ Finset.Icc i j, (PowerSeries.constantCoeff (M k k))⁻¹ else 0) := by
  let M := (c.originalInternalResponseMatrix P).map c.normalSeries
  let e : Fin (originalSelectedCount (hD := hD) P - 2 + 1) ≃
      Fin (originalSelectedCount (hD := hD) P - 1) := finCongr (by omega)
  let g := fun i : Fin (originalSelectedCount (hD := hD) P - 1) =>
    PowerSeries.coeff 1 (M i i) * (PowerSeries.constantCoeff (M i i))⁻¹
  let f := fun (i j : Fin (originalSelectedCount (hD := hD) P - 1)) =>
    c.normalCoefficient⁻¹ * PowerSeries.constantCoeff (M i j) *
      (PowerSeries.constantCoeff (M i i))⁻¹ * (PowerSeries.constantCoeff (M j j))⁻¹
  have hons : (∑ i, g (e i)) = ∑ i, g i := by
    apply Fintype.sum_equiv e
    intro i
    rfl
  have he : (∑ i, ∑ j, if j.val = i.val + 1 then f i j else 0) =
      ∑ i, ∑ j, if j.val = i.val + 1 then f (e i) (e j) else 0 := by
    symm
    apply Fintype.sum_equiv e
    intro i
    apply Fintype.sum_equiv e
    intro j
    rfl
  have hs : (∑ i : Fin (originalSelectedCount (hD := hD) P - 2 + 1), ∑ j,
      if j.val = i.val + 1 then f (e i) (e j) else 0) =
      ∑ i : Fin (originalSelectedCount (hD := hD) P - 2),
        f (e i.castSucc) (e i.succ) :=
    adjacent_pair_sum (fun i j => f (e i) (e j))
  have hmap : c.normalSeries (c.originalInternalResponseMatrix P).det = M.det := by
    rw [RingHom.map_det]
    congr 1
  have h0 := c.originalInternal_normal_constant_ne_zero P (by omega) hmax
  rw [hmap] at h0
  have hbal : PowerSeries.coeff 1 M.det * (PowerSeries.constantCoeff M.det)⁻¹ =
      (∑ i, g (e i)) - ∑ i : Fin (originalSelectedCount (hD := hD) P - 2),
        f (e i.castSucc) (e i.succ) := by
    have h := c.originalInternal_first_normal_balance P hB hmax
    rw [hmap] at h
    exact h
  have hnative : PowerSeries.coeff 1 M.det * (PowerSeries.constantCoeff M.det)⁻¹ =
      (∑ i, g i) - ∑ i, ∑ j, if j.val = i.val + 1 then f i j else 0 := by
    calc
      _ = (∑ i, g (e i)) - ∑ i : Fin (originalSelectedCount (hD := hD) P - 2),
          f (e i.castSucc) (e i.succ) := hbal
      _ = _ := by rw [hons, ← hs, ← he]
  dsimp only
  rw [normalized_log_coeff_one M.det h0, hnative]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hij : j.val = i.val + 1
  · rw [ite_eq_left hij, ite_eq_left hij,
      adjacent_pair_interval_product _ i j hij]
    dsimp only [f]
    ring
  · rw [ite_eq_right hij, ite_eq_right hij, mul_zero]

end SkewCornerDescent.Matrix.SelectedCoordinate
