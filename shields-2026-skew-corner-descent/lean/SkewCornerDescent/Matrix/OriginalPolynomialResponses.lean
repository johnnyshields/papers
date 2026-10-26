/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.PolynomialLowerField
import SkewCornerDescent.Matrix.OriginalDenominators

/-!
# Polynomial correction numerators of the complete original responses

Formalizes `shields-2026-skew-corner-descent.tex`, «Equal windows and the determinant defect»
(`sec:normal-chart`, `lem:actual-elimination`). The full adjugate contraction has the actual
removed determinant as its denominator. Its polynomial numerator uses only generators below
the retained top, even when the complete inverse has high off-diagonal couplings. Sorry-free.
-/

namespace SkewCornerDescent.Matrix

open SkewGluing MvPolynomial

attribute [local instance] Classical.propDecidable

/-- The complete polynomial adjugate contraction, without deleting off-diagonal terms. -/
noncomputable def polynomialContraction {ν : Type*} [Fintype ν] [DecidableEq ν]
    (r s : ν → Lambda) (M : Matrix ν ν Lambda) : Lambda :=
  ∑ i, ∑ j, r i * M.adjugate i j * s j

/-- Clearing the complete inverse contraction uses exactly its polynomial determinant. -/
theorem inverseContraction_polynomial_fraction {ν : Type*} [Fintype ν] [DecidableEq ν]
    (r s : ν → Lambda) (M : Matrix ν ν Lambda) :
    inverseContraction (originalMap ∘ r) (originalMap ∘ s) (M.map originalMap) =
      originalMap (polynomialContraction r s M) / originalMap M.det := by
  have hd : (M.map originalMap).det = originalMap M.det := (RingHom.map_det originalMap M).symm
  have ha : (M.map originalMap).adjugate = originalMap.mapMatrix M.adjugate :=
    (RingHom.map_adjugate originalMap M).symm
  unfold inverseContraction polynomialContraction
  rw [map_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  rw [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv, hd, ha,
    map_mul, map_mul]
  change originalMap (r i) * ((originalMap M.det)⁻¹ * originalMap (M.adjugate i j)) *
    originalMap (s j) = _
  rw [div_eq_mul_inv]
  ring

namespace SelectedCoordinate

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The complete actual correction has a lower polynomial numerator and a produced regular
polynomial denominator using only indices at most the selected span. -/
theorem originalLocalResponse_triangular_fraction {n : ℕ} (P : Profile n)
    (b d : Option (OriginalSelectedBlocks (hD := hD) P)) (K : ℕ+) (hNK : c.top < K)
    (hK : P.xi (originalRowSplitEquiv (hD := hD) P (.inl b)) -
      P.zeta (originalColSplitEquiv (hD := hD) P (.inl d)) = (K : ℤ))
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ)) :
    ∃ R ∈ supported ℚ {j : ℕ+ | j < K}, ∃ q : Lambda,
      q ≠ 0 ∧ ¬cellSchur D hD.1 ∣ q ∧ polynomialSpan q ≤ (c.top : ℕ) ∧
      c.regularEmbedding (c.originalLocalResponse P b d) =
        originalMap (X K) + originalMap R / originalMap q := by
  let M := originalRemovedMatrix (hD := hD) P
  let r := fun j : OriginalRemainingIndices (hD := hD) P =>
    hh (P.xi (originalRowSplitEquiv (hD := hD) P (.inl b)) - originalResponseCols P j)
  let s := fun j : OriginalRemainingIndices (hD := hD) P =>
    hh (originalResponseRows P j - P.zeta (originalColSplitEquiv (hD := hD) P (.inl d)))
  let R := -polynomialContraction r s M
  let q := M.det
  have hreg : ¬cellSchur D hD.1 ∣ q := not_dvd_originalRemovedMatrix P
  have hq0 : q ≠ 0 := by intro hz; exact hreg (hz ▸ dvd_zero _)
  have hqspan : polynomialSpan q ≤ (c.top : ℕ) :=
    originalRemovedMatrix_det_span_le P _ (originalBlock_span_le_of_components P _ hmax)
  have hmq0 : originalMap q ≠ 0 := by simpa only [ne_eq, originalMap_eq_zero] using hq0
  have hresp : c.regularEmbedding (c.originalLocalResponse P b d) =
      originalMap (X K) + originalMap R / originalMap q := by
    let := c.originalRemovedFieldInverse P
    rw [c.originalLocalResponse_embedding_interval, intervalResponse_eq_sub_inverseContraction]
    rw [hK, hh_pnat]
    change originalMap (X K) - inverseContraction (originalMap ∘ r)
      (originalMap ∘ s) (M.map originalMap) = _
    rw [inverseContraction_polynomial_fraction, show originalMap R =
      -originalMap (polynomialContraction r s M) from map_neg originalMap _]
    rw [neg_div, sub_eq_add_neg]
  have hqlo : originalMap q ∈ lowerGeneratorField K := by
    apply originalMap_mem_lower_iff.mpr
    apply mem_supported.mpr
    intro j hj
    change (j : ℕ) < (K : ℕ)
    exact lt_of_le_of_lt ((Finset.le_sup hj).trans hqspan) hNK
  obtain ⟨A, hA, he, _⟩ := c.originalLocalResponse_triangular P b d K hK
  have hRa : originalMap R / originalMap q = A := by
    rw [hresp] at he
    exact add_left_cancel he
  have hRlo : originalMap R ∈ lowerGeneratorField K := by
    have hm : originalMap R = A * originalMap q := (div_eq_iff hmq0).mp hRa
    rw [hm]
    exact (lowerGeneratorField K).mul_mem hA hqlo
  exact ⟨R, originalMap_mem_lower_iff.mp hRlo, q, hq0, hreg, hqspan, hresp⟩

end SelectedCoordinate
end SkewCornerDescent.Matrix
