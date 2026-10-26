/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.OriginalNormalLog
import SkewCornerDescent.Matrix.HessenbergNormalIndependence

/-!
# Actual determinant independence from literal interval distances

Supports `shields-2026-skew-corner-descent.tex` (`lem:original-transfer`).
All lower normal coefficients are produced from the actual interval distances
and selected-subdiagonal costs. No coefficient independence is assumed.
The full cyclic chart must still supply its literal distance inequalities.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- A literal original upper interval strictly below the fresh generator has no derivative
at any normal order. Its positive protected top is supplied by the actual endpoint geometry. -/
theorem originalHessenberg_normalSeries_derivative_below {n : ℕ} (P : Profile n)
    (hB : 0 < originalSelectedCount (hD := hD) P)
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ))
    (K : ℕ+) (hK : c.top < K)
    (i j : Fin (originalSelectedCount (hD := hD) P + 1)) (hij : i ≤ j)
    (hdistance : originalHessenbergDistance (hD := hD) P i j < (K : ℤ)) (m : ℕ) :
    residueGeneratorDeriv c.top ⟨K, ne_of_gt hK⟩
      (PowerSeries.coeff m (c.normalSeries (c.originalHessenbergResponse P i j))) = 0 := by
  let J := c.originalHessenbergTop P hB i j hij
  have he : (J : ℤ) = originalHessenbergDistance (hD := hD) P i j :=
    c.originalHessenbergTop_coe P hB i j hij
  have hNJ : c.top < J := by
    have ht := c.originalHessenbergDistance_gt_top P hB i j hij
    exact_mod_cast (show (c.top : ℤ) < (J : ℤ) by omega)
  have hJK : J < K := by
    exact_mod_cast (show (J : ℤ) < (K : ℤ) by omega)
  exact c.originalLocalResponse_normalSeries_derivative_below P
    (originalHessenbergRows P i) (originalHessenbergCols P j) J K hNJ hJK he.symm hmax m

/-- Literal distances of eligible original upper intervals produce independence of every
lower determinant coefficient. Longer intervals have too many actual selected subdiagonals
and need no distance or jet-independence premise. -/
theorem originalHessenberg_normalSeries_coeff_independent {n : ℕ} (P : Profile n)
    (hB : 0 < originalSelectedCount (hD := hD) P)
    (K : ℕ+) (hK : c.top < K) (m : ℕ)
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ))
    (hdistance : ∀ i j : Fin (originalSelectedCount (hD := hD) P + 1),
      (i : ℕ) ≤ (j : ℕ) → (j : ℕ) - (i : ℕ) < m →
      originalHessenbergDistance (hD := hD) P i j < (K : ℤ)) :
    ∀ k, k < m → residueGeneratorDeriv c.top ⟨K, ne_of_gt hK⟩
      (PowerSeries.coeff k (c.normalSeries (c.originalHessenbergResponse P).det)) = 0 := by
  classical
  intro k hk
  rw [RingHom.map_det]
  refine hessenberg_coeff_deriv_zero _ _ ?_ (c.normalCoefficient)⁻¹ ?_ ?_ k ?_
  · intro i j hij
    change c.normalSeries (c.originalHessenbergResponse P i j) = 0
    rw [c.originalHessenbergResponse_isUpperHessenberg P i j hij, map_zero]
  · apply residueGeneratorDeriv_lower
    exact Subfield.inv_mem _ (residueLowerField_mono hK.le c.normalCoordinate_mem_lower.1)
  · intro i j hij
    let t : Fin (originalSelectedCount (hD := hD) P) := ⟨j.val, by omega⟩
    have hi : i = t.succ := by apply Fin.ext; exact hij
    have hj : j = t.castSucc := by apply Fin.ext; rfl
    rw [hi, hj]
    exact c.originalHessenberg_normalSeries_subdiagonal P t
  · intro i j hij hcost l hl
    exact c.originalHessenberg_normalSeries_derivative_below P hB hmax K hK i j hij
      (hdistance i j hij (hcost.trans_lt hk)) l

/-- The actual first-fresh normalized logarithm needs only literal eligible-interval
inequalities: its earlier-independence premise and nonzero normal constant are both produced. -/
theorem originalHessenberg_normalized_log_minimum_cost {n : ℕ} (P : Profile n)
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
          (PowerSeries.constantCoeff p)⁻¹ *
            residueGeneratorDeriv c.top ⟨K, ne_of_gt hK⟩ (PowerSeries.coeff m p) := by
  exact c.originalHessenberg_normalized_log_derivative P hB hmax K hK m hm
    (c.originalHessenberg_normalSeries_coeff_independent P hB K hK m hmax hdistance)

end SkewCornerDescent.Matrix.SelectedCoordinate
