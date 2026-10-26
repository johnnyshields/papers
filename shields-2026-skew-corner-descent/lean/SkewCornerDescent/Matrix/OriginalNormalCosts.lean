/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.OriginalNormalHessenberg

/-!
# Exact normal cost of original interval contractions

Supports `shields-2026-skew-corner-descent.tex` (`lem:original-transfer`).
The coefficient of every original determinant is expanded in its full response
series. An interval with more selected subdiagonals than the requested order
contributes zero, without truncating any inverse or imposing a coefficient identity.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Multiplication by genuine selected subdiagonals has exactly its stated normal cost. -/
theorem normalSubdiagonal_coeff (p : PowerSeries (OtherField c.top)) (j m : ℕ) :
    PowerSeries.coeff m
      ((PowerSeries.X * PowerSeries.C (c.normalCoefficient)⁻¹) ^ j * p) =
        if j ≤ m then (c.normalCoefficient)⁻¹ ^ j * PowerSeries.coeff (m - j) p
        else 0 := by
  rw [mul_pow, mul_assoc, PowerSeries.coeff_X_pow_mul']
  split_ifs with h
  · simp only [← map_pow, PowerSeries.coeff_C_mul]
  · rfl

/-- Every original interval is retained; intervals exceeding the cost vanish internally. -/
theorem originalHessenberg_normalSeries_coeff {n : ℕ} (P : Profile n) (m : ℕ) :
    let A := (c.originalHessenbergResponse P).map c.normalSeries
    PowerSeries.coeff m (c.normalSeries (c.originalHessenbergResponse P).det) =
      ∑ j : Fin (originalSelectedCount (hD := hD) P + 1),
        if (j : ℕ) ≤ m then
          (-1) ^ (j : ℕ) * (c.normalCoefficient)⁻¹ ^ (j : ℕ) *
            PowerSeries.coeff (m - (j : ℕ)) (A 0 j * (contractionTail A j).det)
        else 0 := by
  dsimp only
  rw [c.originalHessenberg_normalSeries_det]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  have he :
      (-1) ^ (j : ℕ) * (c.originalHessenbergResponse P).map c.normalSeries 0 j *
        ((PowerSeries.X * PowerSeries.C (c.normalCoefficient)⁻¹) ^ (j : ℕ) *
          (contractionTail ((c.originalHessenbergResponse P).map c.normalSeries) j).det) =
      PowerSeries.C ((-1 : OtherField c.top) ^ (j : ℕ)) *
        ((PowerSeries.X * PowerSeries.C (c.normalCoefficient)⁻¹) ^ (j : ℕ) *
          ((c.originalHessenbergResponse P).map c.normalSeries 0 j *
            (contractionTail ((c.originalHessenbergResponse P).map c.normalSeries) j).det)) := by
    simp only [map_pow, map_neg, map_one]
    ring
  rw [he, PowerSeries.coeff_C_mul, c.normalSubdiagonal_coeff]
  split_ifs <;> ring
end SkewCornerDescent.Matrix.SelectedCoordinate
