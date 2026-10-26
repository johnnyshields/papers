/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.OriginalNormalSeries
import SkewCornerDescent.Matrix.OriginalPolynomialResponses

/-!
# Full original response series with protected leading generator

Supports `shields-2026-skew-corner-descent.tex` (`lem:original-transfer`).
The original complete inverse contraction produces its own regular denominator.
The protected high generator is constant in the normal variable; the correction
retains every normal-dependent inverse jet of that denominator.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing MvPolynomial

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The entire original higher response has its protected generator plus full lower jets.
The numerator and denominator are produced from the actual removed matrix, including ties. -/
theorem originalLocalResponse_normalSeries {n : ℕ} (P : Profile n)
    (b d : Option (OriginalSelectedBlocks (hD := hD) P)) (K : ℕ+) (hNK : c.top < K)
    (hK : P.xi (originalRowSplitEquiv (hD := hD) P (.inl b)) -
      P.zeta (originalColSplitEquiv (hD := hD) P (.inl d)) = (K : ℤ))
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ)) :
    ∃ R ∈ supported ℚ {j : ℕ+ | j < K}, ∃ y : c.selectedIdeal.primeCompl,
      polynomialSpan (y : Lambda) ≤ (c.top : ℕ) ∧
      c.normalSeries (c.originalLocalResponse P b d) =
        PowerSeries.C (algebraMap (OtherPolynomial c.top) (OtherField c.top)
          (X ⟨K, ne_of_gt hNK⟩)) +
        c.normalPolynomialSeries R * (c.normalPolynomialSeries y)⁻¹ := by
  obtain ⟨R, hR, q, _, hreg, hspan, he⟩ :=
    c.originalLocalResponse_triangular_fraction P b d K hNK hK hmax
  let y : c.selectedIdeal.primeCompl := ⟨q, by
    change q ∉ c.selectedIdeal
    simpa only [mem_selectedIdeal] using hreg⟩
  have hl : c.originalLocalResponse P b d =
      algebraMap Lambda c.RegularRing (X K) + IsLocalization.mk' c.RegularRing R y := by
    apply c.regularEmbedding_injective
    simpa only [map_add, c.regularEmbedding_polynomial, c.regularEmbedding_fraction] using he
  refine ⟨R, hR, y, hspan, ?_⟩
  rw [hl, map_add, c.normalSeries_polynomial, c.normalSeries_fraction]
  simp only [normalPolynomialSeries, RingHom.comp_apply,
    Polynomial.coeToPowerSeries.ringHom_apply,
    c.normalChart_other K (ne_of_gt hNK), Polynomial.coe_C]

end SkewCornerDescent.Matrix.SelectedCoordinate
