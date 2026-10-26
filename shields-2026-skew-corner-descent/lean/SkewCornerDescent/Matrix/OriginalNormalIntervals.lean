/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.OriginalNormalFrontier
import SkewCornerDescent.Matrix.HessenbergIntervalFrontier
import SkewCornerDescent.Matrix.HessenbergIntervalDistances

/-!
# Actual original first-fresh literal interval sums

Supports `shields-2026-skew-corner-descent.tex` (`lem:original-transfer`).
Every interval is indexed by its actual ordered positions. Normalization removes only
its exterior diagonal factors, leaving the complete inverse window and both endpoints.
The complete cyclic chart must still supply its literal distance inequalities and counts.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- At a bounded literal upper distance, the actual residue derivative detects exactly
equality with the protected generator. The correction's lower support is produced. -/
theorem originalHessenberg_residue_derivative_indicator {n : ℕ} (P : Profile n)
    (hB : 0 < originalSelectedCount (hD := hD) P)
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ))
    (K : ℕ+) (hK : c.top < K)
    (i j : Fin (originalSelectedCount (hD := hD) P + 1)) (hij : i ≤ j)
    (hdistance : originalHessenbergDistance (hD := hD) P i j ≤ (K : ℤ)) :
    residueGeneratorDeriv c.top ⟨K, ne_of_gt hK⟩
      (c.regularResidue (c.originalHessenbergResponse P i j)) =
        if originalHessenbergDistance (hD := hD) P i j = (K : ℤ) then 1 else 0 := by
  classical
  rw [← c.normalSeries_constant_apply, ← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  by_cases he : originalHessenbergDistance (hD := hD) P i j = (K : ℤ)
  · rw [ite_eq_left he]
    have h := c.originalLocalResponse_normalSeries_derivative P
      (originalHessenbergRows P i) (originalHessenbergCols P j) K hK he hmax 0
    simpa only [originalHessenbergResponse, Matrix.submatrix_apply, ite_true, eq_self] using h
  · rw [ite_eq_right he]
    exact c.originalHessenberg_normalSeries_derivative_below P hB hmax K hK i j hij
      (lt_of_le_of_ne hdistance he) 0

/-- The actual original determinant's first-fresh derivative is the full literal interval sum.
All earlier-jet independence is produced from the shorter endpoint distances. -/
theorem originalHessenberg_normalSeries_coeff_intervals {n : ℕ} (P : Profile n)
    (hB : 0 < originalSelectedCount (hD := hD) P)
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ))
    (K : ℕ+) (hK : c.top < K) (m : ℕ) (hm : 0 < m)
    (hdistance : ∀ i j : Fin (originalSelectedCount (hD := hD) P + 1),
      (i : ℕ) ≤ (j : ℕ) → (j : ℕ) - (i : ℕ) < m →
      originalHessenbergDistance (hD := hD) P i j < (K : ℤ)) :
    residueGeneratorDeriv c.top ⟨K, ne_of_gt hK⟩
      (PowerSeries.coeff m (c.normalSeries (c.originalHessenbergResponse P).det)) =
      ∑ i : Fin (originalSelectedCount (hD := hD) P + 1),
        ∑ j : Fin (originalSelectedCount (hD := hD) P + 1),
          if (i : ℕ) ≤ (j : ℕ) ∧ (j : ℕ) - (i : ℕ) = m then
            (-1 : OtherField c.top) ^ m * (c.normalCoefficient)⁻¹ ^ m *
              (∏ k ∈ Finset.univ.filter (fun k => k < i ∨ j < k),
                c.regularResidue (c.originalHessenbergResponse P k k)) *
                  residueGeneratorDeriv c.top ⟨K, ne_of_gt hK⟩
                    (c.regularResidue (c.originalHessenbergResponse P i j))
          else 0 := by
  classical
  rw [RingHom.map_det]
  change residueGeneratorDeriv c.top ⟨K, ne_of_gt hK⟩
    (PowerSeries.coeff m ((c.originalHessenbergResponse P).map c.normalSeries).det) = _
  have he := hessenberg_coeff_deriv_intervals (residueGeneratorDeriv c.top ⟨K, ne_of_gt hK⟩)
    ((c.originalHessenbergResponse P).map c.normalSeries)
    (a := (c.normalCoefficient)⁻¹) (m := m) (hm := hm)
  have hshape : IsUpperHessenberg ((c.originalHessenbergResponse P).map c.normalSeries) := by
    intro i j hij
    change c.normalSeries (c.originalHessenbergResponse P i j) = 0
    rw [c.originalHessenbergResponse_isUpperHessenberg P i j hij, map_zero]
  have ha : residueGeneratorDeriv c.top ⟨K, ne_of_gt hK⟩ (c.normalCoefficient)⁻¹ = 0 := by
    apply residueGeneratorDeriv_lower
    exact Subfield.inv_mem _ (residueLowerField_mono hK.le c.normalCoordinate_mem_lower.1)
  have hsub : ∀ i j : Fin (originalSelectedCount (hD := hD) P + 1),
      (i : ℕ) = (j : ℕ) + 1 →
      c.normalSeries (c.originalHessenbergResponse P i j) =
        PowerSeries.X * PowerSeries.C (c.normalCoefficient)⁻¹ := by
    intro i j hij
    let t : Fin (originalSelectedCount (hD := hD) P) := ⟨j.val, by omega⟩
    have hi : i = t.succ := by apply Fin.ext; exact hij
    have hj : j = t.castSucc := by apply Fin.ext; rfl
    rw [hi, hj]
    exact c.originalHessenberg_normalSeries_subdiagonal P t
  have hshort : ∀ i j : Fin (originalSelectedCount (hD := hD) P + 1),
      (i : ℕ) ≤ (j : ℕ) → (j : ℕ) - (i : ℕ) < m → ∀ l,
      residueGeneratorDeriv c.top ⟨K, ne_of_gt hK⟩
        (PowerSeries.coeff l (c.normalSeries (c.originalHessenbergResponse P i j))) = 0 := by
    intro i j hij hcost l
    exact c.originalHessenberg_normalSeries_derivative_below P hB hmax K hK i j hij
      (hdistance i j hij hcost) l
  simpa only [Matrix.map_apply, c.normalSeries_constant_apply, smul_eq_mul,
    zsmul_eq_mul, Int.cast_pow, Int.cast_neg, Int.cast_one, mul_assoc] using
    he hshape ha hsub hshort

/-- Normalizing the full original determinant yields the complete inverse interval window.
Both cap occurrences remain when they coincide; all nonzero factors are produced. -/
theorem originalHessenberg_normalized_log_intervals {n : ℕ} (P : Profile n)
    (hB : 0 < originalSelectedCount (hD := hD) P)
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ))
    (K : ℕ+) (hK : c.top < K) (m : ℕ) (hm : 0 < m)
    (hdistance : ∀ i j : Fin (originalSelectedCount (hD := hD) P + 1),
      (i : ℕ) ≤ (j : ℕ) → (j : ℕ) - (i : ℕ) < m →
      originalHessenbergDistance (hD := hD) P i j < (K : ℤ)) :
    let p := c.normalSeries (c.originalHessenbergResponse P).det
    residueGeneratorDeriv c.top ⟨K, ne_of_gt hK⟩
      (PowerSeries.coeff m
        (PowerSeries.logOf (PowerSeries.C (PowerSeries.constantCoeff p)⁻¹ * p))) =
      ∑ i : Fin (originalSelectedCount (hD := hD) P + 1),
        ∑ j : Fin (originalSelectedCount (hD := hD) P + 1),
          if (i : ℕ) ≤ (j : ℕ) ∧ (j : ℕ) - (i : ℕ) = m then
            (-1 : OtherField c.top) ^ m * (c.normalCoefficient)⁻¹ ^ m *
              (∏ k ∈ Finset.Icc i j,
                (c.regularResidue (c.originalHessenbergResponse P k k))⁻¹) *
                  residueGeneratorDeriv c.top ⟨K, ne_of_gt hK⟩
                    (c.regularResidue (c.originalHessenbergResponse P i j))
          else 0 := by
  classical
  dsimp only
  rw [c.originalHessenberg_normalized_log_minimum_cost P hB hmax K hK m hm hdistance,
    c.originalHessenberg_normalSeries_coeff_intervals P hB hmax K hK m hm hdistance,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs with hij
  · have hconstant : PowerSeries.constantCoeff
        (c.normalSeries (c.originalHessenbergResponse P).det) =
        ∏ k, c.regularResidue (c.originalHessenbergResponse P k k) := by
      rw [c.normalSeries_constant_apply, RingHom.map_det]
      exact c.originalHessenbergResponse_residue_det P
    rw [hconstant]
    have he := diagonal_product_inverse_interval
      (fun k => c.regularResidue (c.originalHessenbergResponse P k k))
      (fun k => c.originalHessenberg_residue_ne_zero P hB hmax k) i j
    calc
      _ = (-1 : OtherField c.top) ^ m * (c.normalCoefficient)⁻¹ ^ m *
          ((∏ k, c.regularResidue (c.originalHessenbergResponse P k k))⁻¹ *
            ∏ k ∈ Finset.univ.filter (fun k => k < i ∨ j < k),
              c.regularResidue (c.originalHessenbergResponse P k k)) *
            residueGeneratorDeriv c.top ⟨K, ne_of_gt hK⟩
              (c.regularResidue (c.originalHessenbergResponse P i j)) := by ring
      _ = _ := by rw [he]
  · rw [mul_zero]

/-- The normalized original logarithm detects exactly the full literal windows whose
endpoint distance is the fresh top. The shorter-jet and nonzero-normalization inputs are
produced; the geometric distance bounds remain explicit obligations of the cyclic chart. -/
theorem originalHessenberg_normalized_log_detected_intervals {n : ℕ} (P : Profile n)
    (hB : 0 < originalSelectedCount (hD := hD) P)
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ))
    (K : ℕ+) (hK : c.top < K) (m : ℕ) (hm : 0 < m)
    (hshort : ∀ i j : Fin (originalSelectedCount (hD := hD) P + 1),
      (i : ℕ) ≤ (j : ℕ) → (j : ℕ) - (i : ℕ) < m →
      originalHessenbergDistance (hD := hD) P i j < (K : ℤ))
    (hlong : ∀ i j : Fin (originalSelectedCount (hD := hD) P + 1),
      (i : ℕ) ≤ (j : ℕ) → (j : ℕ) - (i : ℕ) = m →
      originalHessenbergDistance (hD := hD) P i j ≤ (K : ℤ)) :
    let p := c.normalSeries (c.originalHessenbergResponse P).det
    residueGeneratorDeriv c.top ⟨K, ne_of_gt hK⟩
      (PowerSeries.coeff m
        (PowerSeries.logOf (PowerSeries.C (PowerSeries.constantCoeff p)⁻¹ * p))) =
      ∑ i : Fin (originalSelectedCount (hD := hD) P + 1),
        ∑ j : Fin (originalSelectedCount (hD := hD) P + 1),
          if (i : ℕ) ≤ (j : ℕ) ∧ (j : ℕ) - (i : ℕ) = m ∧
              originalHessenbergDistance (hD := hD) P i j = (K : ℤ) then
            (-1 : OtherField c.top) ^ m * (c.normalCoefficient)⁻¹ ^ m *
              (∏ k ∈ Finset.Icc i j,
                (c.regularResidue (c.originalHessenbergResponse P k k))⁻¹)
          else 0 := by
  classical
  dsimp only
  rw [c.originalHessenberg_normalized_log_intervals P hB hmax K hK m hm hshort]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  by_cases hij : (i : ℕ) ≤ (j : ℕ) ∧ (j : ℕ) - (i : ℕ) = m
  · rw [ite_eq_left hij, c.originalHessenberg_residue_derivative_indicator P hB hmax K hK
      i j hij.1 (hlong i j hij.1 hij.2)]
    split_ifs <;> simp_all
  · rw [ite_eq_right hij, ite_eq_right (fun h => hij ⟨h.1, h.2.1⟩)]

/-- A single geometric bound on the exact-cost windows supplies every earlier independence
statement and the complete detected inverse-window formula. No shorter-jet premise leaks out. -/
theorem originalHessenberg_normalized_log_from_length_bound {n : ℕ} (P : Profile n)
    (hB : 0 < originalSelectedCount (hD := hD) P)
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ))
    (K : ℕ+) (hK : c.top < K) (m : ℕ) (hm : 0 < m)
    (hmB : m ≤ originalSelectedCount (hD := hD) P)
    (hbound : ∀ i j : Fin (originalSelectedCount (hD := hD) P + 1),
      (i : ℕ) ≤ (j : ℕ) → (j : ℕ) - (i : ℕ) = m →
      originalHessenbergDistance (hD := hD) P i j ≤ (K : ℤ)) :
    let p := c.normalSeries (c.originalHessenbergResponse P).det
    (∀ k, k < m → residueGeneratorDeriv c.top ⟨K, ne_of_gt hK⟩
      (PowerSeries.coeff k p) = 0) ∧
    residueGeneratorDeriv c.top ⟨K, ne_of_gt hK⟩
      (PowerSeries.coeff m
        (PowerSeries.logOf (PowerSeries.C (PowerSeries.constantCoeff p)⁻¹ * p))) =
      ∑ i : Fin (originalSelectedCount (hD := hD) P + 1),
        ∑ j : Fin (originalSelectedCount (hD := hD) P + 1),
          if (i : ℕ) ≤ (j : ℕ) ∧ (j : ℕ) - (i : ℕ) = m ∧
              originalHessenbergDistance (hD := hD) P i j = (K : ℤ) then
            (-1 : OtherField c.top) ^ m * (c.normalCoefficient)⁻¹ ^ m *
              (∏ k ∈ Finset.Icc i j,
                (c.regularResidue (c.originalHessenbergResponse P k k))⁻¹)
          else 0 := by
  have hshort : ∀ i j : Fin (originalSelectedCount (hD := hD) P + 1),
      (i : ℕ) ≤ (j : ℕ) → (j : ℕ) - (i : ℕ) < m →
      originalHessenbergDistance (hD := hD) P i j < (K : ℤ) :=
    fun i j hij hlen => c.originalHessenbergDistance_short_of_length_bound P hB m hmB
      (K : ℤ) hbound i j hij hlen
  exact ⟨c.originalHessenberg_normalSeries_coeff_independent P hB K hK m hmax hshort,
    c.originalHessenberg_normalized_log_detected_intervals P hB hmax K hK m hm hshort hbound⟩

end SkewCornerDescent.Matrix.SelectedCoordinate
