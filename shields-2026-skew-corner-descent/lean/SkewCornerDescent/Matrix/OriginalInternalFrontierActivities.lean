/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.HessenbergFrontierActivities
import SkewCornerDescent.Matrix.OriginalInternalInverseJets

/-!
# Complete actual internal activities on both normal determinant frontiers

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
The original source supplies every diagonal's full inverse identity and exact
selected subdiagonal. Each signed permutation term retains its complete normal
interval activity, or that activity and its actual disjoint adjacent pair.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing
open scoped BigOperators

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- A complete cost-exhausting original internal term has its whole interval
activity. Source-produced diagonal units justify every full inverse weight. -/
theorem originalInternal_single_interval_activity {n : ℕ} (P : Profile n)
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ))
    (σ : Equiv.Perm (Fin (originalSelectedCount (hD := hD) P - 1)))
    (hσ : ∀ j, j.val ≤ (σ j).val + 1) (m : ℕ) (hm : 0 < m)
    (hcost : (Finset.univ.filter (fun j => (σ j).val < j.val)).card = m)
    (i : Fin (originalSelectedCount (hD := hD) P - 1))
    (hi : (σ i).val - i.val = m) :
    let A := (c.originalInternalResponseMatrix P).map c.normalSeries
    let w := fun j => (A j j)⁻¹
    (Equiv.Perm.sign σ : ℤ) • (∏ j, A j (σ j)) * (∏ j, w j) =
      (-1 : PowerSeries (OtherField c.top)) ^ m *
        (PowerSeries.X * PowerSeries.C c.normalCoefficient⁻¹) ^ m *
        (A i (σ i) * ∏ j ∈ Finset.Icc i (σ i), w j) := by
  have hB : 0 < originalSelectedCount (hD := hD) P := by have := i.isLt; omega
  let A := (c.originalInternalResponseMatrix P).map c.normalSeries
  have hdiag (j) : A j j * (A j j)⁻¹ = 1 :=
    PowerSeries.mul_inv_cancel _ (c.originalInternal_normal_diagonal_ne_zero P hB hmax j)
  have hiup : i.val ≤ (σ i).val := by omega
  have hlen : (σ i).val - i.val =
      (Finset.univ.filter (fun j => (σ j).val < j.val)).card := hi.trans hcost.symm
  have he := hessenberg_single_interval_weighted_product A σ hσ
    (PowerSeries.X * PowerSeries.C c.normalCoefficient⁻¹)
    (c.originalInternal_normal_subdiagonal P) (fun j => (A j j)⁻¹) hdiag i hiup hlen
  rw [hi] at he
  exact he

/-- Every complete actual one-shy internal term retains the entire long activity
and one genuine disjoint adjacent pair, including every normal inverse jet. -/
theorem originalInternal_one_shy_activity {n : ℕ} (P : Profile n)
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ))
    (σ : Equiv.Perm (Fin (originalSelectedCount (hD := hD) P - 1)))
    (hσ : ∀ j, j.val ≤ (σ j).val + 1) (m : ℕ) (hm : 2 ≤ m)
    (hcost : (Finset.univ.filter (fun j => (σ j).val < j.val)).card = m)
    (i : Fin (originalSelectedCount (hD := hD) P - 1))
    (hi : (σ i).val - i.val = m - 1) :
    let A := (c.originalInternalResponseMatrix P).map c.normalSeries
    let w := fun j => (A j j)⁻¹
    ∃ k, k ≠ i ∧ (σ k).val = k.val + 1 ∧
      Disjoint (Finset.Icc i (σ i)) (Finset.Icc k (σ k)) ∧
      (Equiv.Perm.sign σ : ℤ) • (∏ j, A j (σ j)) * (∏ j, w j) =
        (-1 : PowerSeries (OtherField c.top)) ^ m *
          (PowerSeries.X * PowerSeries.C c.normalCoefficient⁻¹) ^ m *
          (A i (σ i) * ∏ j ∈ Finset.Icc i (σ i), w j) *
          (A k (σ k) * ∏ j ∈ Finset.Icc k (σ k), w j) := by
  have hB : 0 < originalSelectedCount (hD := hD) P := by have := i.isLt; omega
  let A := (c.originalInternalResponseMatrix P).map c.normalSeries
  have hdiag (j) : A j j * (A j j)⁻¹ = 1 :=
    PowerSeries.mul_inv_cancel _ (c.originalInternal_normal_diagonal_ne_zero P hB hmax j)
  exact hessenberg_one_shy_weighted_product A σ hσ
    (PowerSeries.X * PowerSeries.C c.normalCoefficient⁻¹)
    (c.originalInternal_normal_subdiagonal P) (fun j => (A j j)⁻¹) hdiag hm hcost i hi

end SkewCornerDescent.Matrix.SelectedCoordinate
