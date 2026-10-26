/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.OriginalNormalHessenberg
import SkewCornerDescent.Matrix.ResidueLowerBounds
import SkewCornerDescent.Matrix.OriginalNormalResponses

/-!
# Lower-generator support of complete normal series

Supports `shields-2026-skew-corner-descent.tex` (`lem:original-transfer`).
Coefficient subfields are closed under full series products and full inverse jets.
The actual affine normal substitution introduces only the genuine lower cofactor
and remainder, never a protected higher generator.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix

open SkewGluing MvPolynomial

noncomputable local instance normalSeriesSupportRatAlgebra (N : ℕ+) : Algebra ℚ (OtherField N) :=
  OreLocalization.instAlgebra

/-- Convolution does not introduce a generator absent from both coefficient fields. -/
theorem series_coeff_mul_mem_subfield {F : Type*} [Field F] (S : Subfield F)
    (p q : PowerSeries F) (hp : ∀ n, PowerSeries.coeff n p ∈ S)
    (hq : ∀ n, PowerSeries.coeff n q ∈ S) (n : ℕ) :
    PowerSeries.coeff n (p * q) ∈ S := by
  rw [PowerSeries.coeff_mul]
  exact S.sum_mem fun j _ => S.mul_mem (hp j.1) (hq j.2)

/-- Every inverse jet stays in the original coefficient subfield, not just its residue. -/
theorem series_coeff_inv_mem_subfield {F : Type*} [Field F] (S : Subfield F)
    (p : PowerSeries F) (hp : ∀ n, PowerSeries.coeff n p ∈ S) (n : ℕ) :
    PowerSeries.coeff n p⁻¹ ∈ S := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [PowerSeries.coeff_inv]
    have h0 : PowerSeries.constantCoeff p ∈ S := by
      simpa only [PowerSeries.coeff_zero_eq_constantCoeff_apply] using hp 0
    split_ifs with hn
    · exact S.inv_mem h0
    · apply S.mul_mem (S.neg_mem (S.inv_mem h0))
      apply S.sum_mem
      intro j _
      split_ifs with hj
      · exact S.mul_mem (hp j.1) (ih j.2 hj)
      · exact S.zero_mem

namespace SelectedCoordinate

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The actual selected original generator has its complete affine normal series. -/
theorem normalPolynomialSeries_top :
    c.normalPolynomialSeries (X c.top) =
      (PowerSeries.X - PowerSeries.C c.normalRemainder) *
        PowerSeries.C (c.normalCoefficient)⁻¹ := by
  let := invertibleOfNonzero c.normalCoefficient_ne_zero
  change ((Polynomial.algEquivCMulXAddC c.normalCoefficient c.normalRemainder).symm
    (splitOverField c.top (X c.top)) : PowerSeries (OtherField c.top)) = _
  simp [splitOverField, splitGenerator_top,
    Polynomial.algEquivCMulXAddC_symm_apply, mul_comm]

/-- Both actual affine-coordinate constants use strictly lower surviving generators. -/
theorem normalCoordinate_mem_lower :
    c.normalCoefficient ∈ residueLowerField c.top c.top ∧
      c.normalRemainder ∈ residueLowerField c.top c.top := by
  have hc : c.residueMap c.coefficient = c.normalCoefficient := by
    rw [← c.normalPolynomialSeries_constant]
    simp [normalPolynomialSeries,
      c.normalChart_of_top_notMem c.coefficient c.top_notMem_coefficient, normalCoefficient]
  have hr : c.residueMap c.remainder = c.normalRemainder := by
    rw [← c.normalPolynomialSeries_constant]
    simp [normalPolynomialSeries,
      c.normalChart_of_top_notMem c.remainder c.top_notMem_remainder, normalRemainder]
  exact ⟨hc ▸ c.residue_lower_polynomial c.coefficient_lower,
    hr ▸ c.residue_lower_polynomial c.remainder_lower⟩

/-- Every full normal jet of an original lower-supported polynomial remains lower-supported. -/
theorem normalPolynomialSeries_coeff_mem_lower (K : ℕ+) (hK : c.top < K) {p : Lambda}
    (hp : p ∈ supported ℚ {j : ℕ+ | j < K}) (n : ℕ) :
    PowerSeries.coeff n (c.normalPolynomialSeries p) ∈ residueLowerField c.top K := by
  have all : ∀ n, PowerSeries.coeff n (c.normalPolynomialSeries p) ∈
      residueLowerField c.top K := by
    induction hp using Algebra.adjoin_induction with
    | mem p hp =>
      obtain ⟨j, hj, rfl⟩ := hp
      intro n
      by_cases he : j = c.top
      · subst j
        rw [c.normalPolynomialSeries_top]
        apply series_coeff_mul_mem_subfield
        · intro m
          rw [map_sub]
          apply Subfield.sub_mem
          · simp only [PowerSeries.coeff_X]
            split_ifs <;> simp
          · simp only [PowerSeries.coeff_C]
            split_ifs
            · exact residueLowerField_mono hK.le c.normalCoordinate_mem_lower.2
            · exact Subfield.zero_mem _
        · intro m
          simp only [PowerSeries.coeff_C]
          split_ifs
          · exact Subfield.inv_mem _ (residueLowerField_mono hK.le
              c.normalCoordinate_mem_lower.1)
          · exact Subfield.zero_mem _
      · simp only [normalPolynomialSeries, RingHom.comp_apply,
          Polynomial.coeToPowerSeries.ringHom_apply, c.normalChart_other j he,
          Polynomial.coe_C, PowerSeries.coeff_C]
        split_ifs
        · rw [← c.residueMap_other j he]
          exact c.residue_other_mem_lower K j he hj
        · exact Subfield.zero_mem _
    | algebraMap q =>
      intro n
      have he := RingHom.map_rat_algebraMap c.normalPolynomialSeries q
      rw [he, PowerSeries.algebraMap_apply, PowerSeries.coeff_C]
      split_ifs
      · have hq : algebraMap ℚ (OtherField c.top) q = (q : OtherField c.top) := by
          simp
        rw [hq]
        exact SubfieldClass.ratCast_mem (residueLowerField c.top K) q
      · exact Subfield.zero_mem _
    | add p q _ _ hp hq =>
      intro n
      rw [map_add, map_add]
      exact Subfield.add_mem _ (hp n) (hq n)
    | mul p q _ _ hp hq =>
      intro n
      rw [map_mul]
      exact series_coeff_mul_mem_subfield _ _ _ hp hq n
  exact all n

/-- Every jet of a regular original lower fraction omits the protected generator. -/
theorem normalSeries_fraction_coeff_mem_lower (K : ℕ+) (hK : c.top < K) {p : Lambda}
    (hp : p ∈ supported ℚ {j : ℕ+ | j < K}) (y : c.selectedIdeal.primeCompl)
    (hy : polynomialSpan (y : Lambda) ≤ (c.top : ℕ)) (n : ℕ) :
    PowerSeries.coeff n (c.normalSeries (IsLocalization.mk' c.RegularRing p y)) ∈
      residueLowerField c.top K := by
  rw [c.normalSeries_fraction]
  apply series_coeff_mul_mem_subfield
  · exact c.normalPolynomialSeries_coeff_mem_lower K hK hp
  · apply series_coeff_inv_mem_subfield
    apply c.normalPolynomialSeries_coeff_mem_lower K hK
    apply mem_supported.mpr
    intro j hj
    exact lt_of_le_of_lt ((Finset.le_sup hj).trans hy) hK

/-- The full lower-jet correction is produced from the complete original response.
In particular, no positive-order inverse jet acquires its protected leading generator. -/
theorem originalLocalResponse_normalSeries_lower_jets {n : ℕ} (P : Profile n)
    (b d : Option (OriginalSelectedBlocks (hD := hD) P)) (K : ℕ+) (hNK : c.top < K)
    (hK : P.xi (originalRowSplitEquiv (hD := hD) P (.inl b)) -
      P.zeta (originalColSplitEquiv (hD := hD) P (.inl d)) = (K : ℤ))
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ)) :
    ∃ A : PowerSeries (OtherField c.top),
      (∀ m, PowerSeries.coeff m A ∈ residueLowerField c.top K) ∧
      c.normalSeries (c.originalLocalResponse P b d) =
        PowerSeries.C (algebraMap (OtherPolynomial c.top) (OtherField c.top)
          (X ⟨K, ne_of_gt hNK⟩)) + A := by
  obtain ⟨R, hR, y, hy, he⟩ := c.originalLocalResponse_normalSeries P b d K hNK hK hmax
  refine ⟨c.normalPolynomialSeries R * (c.normalPolynomialSeries y)⁻¹, ?_, he⟩
  intro m
  rw [← c.normalSeries_fraction]
  exact c.normalSeries_fraction_coeff_mem_lower K hNK hR y hy m

end SelectedCoordinate
end SkewCornerDescent.Matrix
