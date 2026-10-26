/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.OriginalNormalCosts
import SkewCornerDescent.Matrix.NormalInverseCoefficient

/-!
# Complete differentiated original interval recurrence

Supports `shields-2026-skew-corner-descent.tex` (`lem:original-transfer`).
Every complete interval contraction remains present. Generator independence
of its actual cofactor cost is produced from strict lower-field support.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The actual signed selected-subdiagonal cost has zero derivative in every higher
surviving generator, independently of its exponent. -/
theorem normalCost_derivative (K : ℕ+) (hK : c.top < K) (j : ℕ) :
    residueGeneratorDeriv c.top ⟨K, ne_of_gt hK⟩
      ((-1 : OtherField c.top) ^ j * (c.normalCoefficient)⁻¹ ^ j) = 0 := by
  apply residueGeneratorDeriv_lower
  apply Subfield.mul_mem
  · exact Subfield.pow_mem _ (Subfield.neg_mem _ (Subfield.one_mem _)) j
  · exact Subfield.pow_mem _ (Subfield.inv_mem _
      (residueLowerField_mono hK.le c.normalCoordinate_mem_lower.1)) j

/-- Differentiating the actual determinant preserves every full interval and its exact cost.
The derivative of the cofactor cost is discharged internally; all shorter-response and tail
coefficients remain available for the geometric minimum-cost assembly. -/
theorem originalHessenberg_normalSeries_coeff_derivative {n : ℕ} (P : Profile n)
    (K : ℕ+) (hK : c.top < K) (m : ℕ) :
    let A := (c.originalHessenbergResponse P).map c.normalSeries
    let generatorDeriv := residueGeneratorDeriv c.top ⟨K, ne_of_gt hK⟩
    generatorDeriv (PowerSeries.coeff m (c.normalSeries (c.originalHessenbergResponse P).det)) =
      ∑ j : Fin (originalSelectedCount (hD := hD) P + 1),
        if (j : ℕ) ≤ m then
          (-1) ^ (j : ℕ) * (c.normalCoefficient)⁻¹ ^ (j : ℕ) *
            generatorDeriv (PowerSeries.coeff (m - (j : ℕ)) (A 0 j * (contractionTail A j).det))
        else 0 := by
  dsimp only
  rw [c.originalHessenberg_normalSeries_coeff, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs
  · rw [Derivation.leibniz, c.normalCost_derivative K hK (j : ℕ), smul_zero, add_zero]
    rfl
  · exact map_zero _

end SkewCornerDescent.Matrix.SelectedCoordinate
