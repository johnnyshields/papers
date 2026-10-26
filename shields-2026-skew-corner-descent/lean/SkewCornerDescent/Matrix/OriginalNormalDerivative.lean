/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.ResidueGeneratorDerivation
import SkewCornerDescent.Matrix.OriginalNormalExclusion

/-!
# Actual protected-generator derivatives of full original response jets

Supports `shields-2026-skew-corner-descent.tex` (`lem:original-transfer`).
All strictly lower coefficient-field fractions are annihilated by the genuine
surviving-generator partial derivative. The complete original response consequently
has leading derivative one only at normal order zero and zero at every higher order.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix

open SkewGluing MvPolynomial


/-- The actual protected-generator derivative annihilates all strictly lower fractions. -/
theorem residueGeneratorDeriv_lower (N : ℕ+) (j : {j : ℕ+ // j ≠ N})
    {x : OtherField N} (hx : x ∈ residueLowerField N j.1) :
    residueGeneratorDeriv N j x = 0 := by
  have hAlg : instAlgebraRatOtherField N =
      DivisionRing.toRatAlgebra := Subsingleton.elim _ _
  unfold residueLowerField at hx
  rw [hAlg] at hx
  change x ∈ IntermediateField.adjoin ℚ
    (residueGenerator N '' {k : {k : ℕ+ // k ≠ N} | k.1 < j.1}) at hx
  induction hx using IntermediateField.adjoin_induction with
  | mem x hx =>
    obtain ⟨k, hk, rfl⟩ := hx
    change k.1 < j.1 at hk
    have hkj : k ≠ j := by intro h; subst k; exact lt_irrefl _ hk
    simp [hkj]
  | algebraMap q => exact (residueGeneratorDeriv N j).map_algebraMap q
  | add x y _ _ hx hy => simp only [map_add, hx, hy, add_zero]
  | inv x _ hx => rw [Derivation.leibniz_inv, hx, smul_zero]
  | mul x y _ _ hx hy => simp only [Derivation.leibniz, hx, hy, smul_zero, add_zero]

namespace SelectedCoordinate

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The protected original generator occurs with coefficient one at order zero only.
Every higher-order derivative of the full response is produced from lower-jet support. -/
theorem originalLocalResponse_normalSeries_derivative {n : ℕ} (P : Profile n)
    (b d : Option (OriginalSelectedBlocks (hD := hD) P)) (K : ℕ+) (hNK : c.top < K)
    (hK : P.xi (originalRowSplitEquiv (hD := hD) P (.inl b)) -
      P.zeta (originalColSplitEquiv (hD := hD) P (.inl d)) = (K : ℤ))
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ))
    (m : ℕ) :
    residueGeneratorDeriv c.top ⟨K, ne_of_gt hNK⟩
      (PowerSeries.coeff m (c.normalSeries (c.originalLocalResponse P b d))) =
        if m = 0 then 1 else 0 := by
  obtain ⟨A, hA, he⟩ := c.originalLocalResponse_normalSeries_lower_jets P b d K hNK hK hmax
  rw [he, map_add, map_add, residueGeneratorDeriv_lower c.top ⟨K, ne_of_gt hNK⟩ (hA m),
    add_zero, PowerSeries.coeff_C]
  split_ifs
  · simp
  · exact map_zero _

/-- Every jet of a shorter literal interval has zero derivative in the later generator. -/
theorem originalLocalResponse_normalSeries_derivative_below {n : ℕ} (P : Profile n)
    (b d : Option (OriginalSelectedBlocks (hD := hD) P)) (J K : ℕ+)
    (hNJ : c.top < J) (hJK : J < K)
    (hJ : P.xi (originalRowSplitEquiv (hD := hD) P (.inl b)) -
      P.zeta (originalColSplitEquiv (hD := hD) P (.inl d)) = (J : ℤ))
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ))
    (m : ℕ) :
    residueGeneratorDeriv c.top ⟨K, ne_of_gt (hNJ.trans hJK)⟩
      (PowerSeries.coeff m (c.normalSeries (c.originalLocalResponse P b d))) = 0 :=
  residueGeneratorDeriv_lower _ _
    (c.originalLocalResponse_normalSeries_coeff_below P b d J K hNJ hJK hJ hmax m)

end SelectedCoordinate
end SkewCornerDescent.Matrix
