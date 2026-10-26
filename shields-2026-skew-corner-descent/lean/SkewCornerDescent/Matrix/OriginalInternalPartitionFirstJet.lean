/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.HessenbergPartitionFirstJet
import SkewCornerDescent.Matrix.OriginalInternalFirstJet
import SkewCornerDescent.Matrix.OriginalInternalInverseJets
import SkewCornerDescent.Matrix.AdjacentPairIndexing

/-!
# Actual full partition first coefficient is its adjacent-pair sum

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
The exact internal-state index equivalence retains every original position.
Both the determinant and its full reciprocal-diagonal product are transported.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Complete onsite cancellation leaves precisely the actual adjacent-pair residues
in the first normalized internal partition coefficient. -/
theorem originalInternal_partition_coeff_one {n : ℕ} (P : Profile n)
    (hB : 2 ≤ originalSelectedCount (hD := hD) P)
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ)) :
    let M := (c.originalInternalResponseMatrix P).map c.normalSeries
    let e : Fin (originalSelectedCount (hD := hD) P - 2 + 1) ≃
        Fin (originalSelectedCount (hD := hD) P - 1) := finCongr (by omega)
    let A := M.submatrix e e
    PowerSeries.coeff 1 (M.det * ∏ i, (M i i)⁻¹) =
      -(∑ i : Fin (originalSelectedCount (hD := hD) P - 2),
        c.normalCoefficient⁻¹ * PowerSeries.constantCoeff (A i.castSucc i.succ) *
          (PowerSeries.constantCoeff (A i.castSucc i.castSucc))⁻¹ *
          (PowerSeries.constantCoeff (A i.succ i.succ))⁻¹) := by
  let M := (c.originalInternalResponseMatrix P).map c.normalSeries
  let e : Fin (originalSelectedCount (hD := hD) P - 2 + 1) ≃
      Fin (originalSelectedCount (hD := hD) P - 1) := finCongr (by omega)
  let A := M.submatrix e e
  have hval (i) : (e i).val = i.val := rfl
  have hshape : IsUpperHessenberg A := by
    intro i j hij
    exact c.originalInternal_normal_shape P (e i) (e j) (by rw [hval, hval]; exact hij)
  have hsub (i j) (hij : i.val = j.val + 1) :
      A i j = PowerSeries.X * PowerSeries.C c.normalCoefficient⁻¹ :=
    c.originalInternal_normal_subdiagonal P (e i) (e j) (by rw [hval, hval]; exact hij)
  have hunit (i) : PowerSeries.constantCoeff (A i i) ≠ 0 :=
    c.originalInternal_normal_diagonal_ne_zero P (by omega) hmax (e i)
  have hdet : M.det = A.det := (Matrix.det_submatrix_equiv_self e M).symm
  have hprod : (∏ i, (M i i)⁻¹) = ∏ i, (A i i)⁻¹ := by
    symm
    apply Fintype.prod_equiv e
    intro i
    rfl
  dsimp only
  change PowerSeries.coeff 1 (M.det * ∏ i, (M i i)⁻¹) = _
  rw [hdet, hprod]
  exact hessenberg_partition_coeff_one A hshape c.normalCoefficient⁻¹ hsub hunit

/-- The actual first partition coefficient in the original endpoint-pair indexing.
Every adjacent pair occurs exactly once; no reindexed state is left in the contract. -/
theorem originalInternal_partition_coeff_one_pairs {n : ℕ} (P : Profile n)
    (hB : 2 ≤ originalSelectedCount (hD := hD) P)
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ)) :
    let M := (c.originalInternalResponseMatrix P).map c.normalSeries
    PowerSeries.coeff 1 (M.det * ∏ i, (M i i)⁻¹) =
      -(∑ i : Fin (originalSelectedCount (hD := hD) P - 1), ∑ j,
        if j.val = i.val + 1 then
          c.normalCoefficient⁻¹ * PowerSeries.constantCoeff (M i j) *
            (PowerSeries.constantCoeff (M i i))⁻¹ *
            (PowerSeries.constantCoeff (M j j))⁻¹ else 0) := by
  let M := (c.originalInternalResponseMatrix P).map c.normalSeries
  let e : Fin (originalSelectedCount (hD := hD) P - 2 + 1) ≃
      Fin (originalSelectedCount (hD := hD) P - 1) := finCongr (by omega)
  let f := fun (i j : Fin (originalSelectedCount (hD := hD) P - 1)) =>
    c.normalCoefficient⁻¹ * PowerSeries.constantCoeff (M i j) *
      (PowerSeries.constantCoeff (M i i))⁻¹ *
      (PowerSeries.constantCoeff (M j j))⁻¹
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
  have hfirst : PowerSeries.coeff 1 (M.det * ∏ i, (M i i)⁻¹) =
      -(∑ i : Fin (originalSelectedCount (hD := hD) P - 2),
        f (e i.castSucc) (e i.succ)) :=
    c.originalInternal_partition_coeff_one P hB hmax
  dsimp only
  exact hfirst.trans (congrArg Neg.neg (he.trans hs).symm)

/-- The actual adjacent-pair coefficient in full closed-interval activity form.
The interval-product bridge is proved for every finite adjacent pair. -/
theorem originalInternal_partition_coeff_one_intervals {n : ℕ} (P : Profile n)
    (hB : 2 ≤ originalSelectedCount (hD := hD) P)
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ)) :
    let A := (c.originalInternalResponseMatrix P).map c.normalSeries
    PowerSeries.coeff 1 (A.det * ∏ i, (A i i)⁻¹) =
      -c.normalCoefficient⁻¹ *
        (∑ i : Fin (originalSelectedCount (hD := hD) P - 1), ∑ j,
          if j.val = i.val + 1 then PowerSeries.constantCoeff (A i j) *
            ∏ k ∈ Finset.Icc i j, (PowerSeries.constantCoeff (A k k))⁻¹ else 0) := by
  have h := c.originalInternal_partition_coeff_one_pairs P hB hmax
  dsimp only at h ⊢
  refine h.trans ?_
  rw [neg_mul]
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
    ring
  · rw [ite_eq_right hij, ite_eq_right hij, mul_zero]

end SkewCornerDescent.Matrix.SelectedCoordinate
