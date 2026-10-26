/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.OriginalPolynomialResponses
import SkewCornerDescent.Matrix.OriginalHessenbergTops

/-!
# Polynomial response coefficients over the actual lower residue field

Formalizes `shields-2026-skew-corner-descent.tex`, «Equal windows and the determinant defect»
(`sec:normal-chart`, `lem:actual-elimination`, `lem:component-elimination`). The coefficient
band is polynomial, not merely rational, in the surviving generators above the selected span
and below the protected top. Every inverted denominator lies in the lower field. Sorry-free.
-/

namespace SkewCornerDescent.Matrix

open SkewGluing MvPolynomial

noncomputable local instance (N : ℕ+) : Algebra ℚ (OtherField N) := OreLocalization.instAlgebra

/-- The polynomial algebra over the lower residue field in the indicated higher generators. -/
noncomputable def residuePolynomialBand (N K : ℕ+) : Subalgebra ℚ (OtherField N) :=
  Algebra.adjoin ℚ ((residueLowerField N N : Set (OtherField N)) ∪
    {x | ∃ j : {j : ℕ+ // j ≠ N}, N < j.val ∧ j.val < K ∧ x = residueGenerator N j})

/-- The whole lower field, including its inverses, is part of the polynomial coefficient band. -/
theorem residueLowerField_mem_band (N K : ℕ+) {x : OtherField N}
    (hx : x ∈ residueLowerField N N) : x ∈ residuePolynomialBand N K :=
  Algebra.subset_adjoin (Or.inl hx)

namespace SelectedCoordinate

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Each original generator below the retained top becomes a polynomial-band element. -/
theorem residue_generator_mem_band (K j : ℕ+) (hj : j < K) :
    c.residueMap (X j) ∈ residuePolynomialBand c.top K := by
  by_cases hlow : j ≤ c.top
  · apply residueLowerField_mem_band
    by_cases he : j = c.top
    · subst j
      exact c.residue_top_mem_lower
    · exact c.residue_other_mem_lower c.top j he (lt_of_le_of_ne hlow he)
  · have hN : c.top < j := lt_of_not_ge hlow
    rw [c.residueMap_other j (ne_of_gt hN)]
    exact Algebra.subset_adjoin (Or.inr ⟨⟨j, ne_of_gt hN⟩, hN, hj, rfl⟩)

/-- The normal substitution sends every lower polynomial into the polynomial coefficient band. -/
theorem residue_supported_mem_band (K : ℕ+) {p : Lambda}
    (hp : p ∈ supported ℚ {j : ℕ+ | j < K}) :
    c.residueMap p ∈ residuePolynomialBand c.top K := by
  induction hp using Algebra.adjoin_induction with
  | mem p hp =>
    obtain ⟨j, hj, rfl⟩ := hp
    exact c.residue_generator_mem_band K j hj
  | algebraMap q =>
    have he := map_ratCast (c.residueMap.comp (MvPolynomial.C : ℚ →+* Lambda)) q
    change c.residueMap (C q) = (q : OtherField c.top) at he
    change c.residueMap (C q) ∈ residuePolynomialBand c.top K
    rw [he]
    apply residueLowerField_mem_band
    exact SubfieldClass.ratCast_mem (residueLowerField c.top c.top) q
  | add p q _ _ hp hq =>
    rw [map_add]
    exact (residuePolynomialBand c.top K).add_mem hp hq
  | mul p q _ _ hp hq =>
    rw [map_mul]
    exact (residuePolynomialBand c.top K).mul_mem hp hq

/-- Inverting a regular lower denominator introduces no higher-generator denominator. -/
theorem residue_fraction_mem_band (K : ℕ+) {p q : Lambda}
    (hp : p ∈ supported ℚ {j : ℕ+ | j < K})
    (hq : polynomialSpan q ≤ (c.top : ℕ)) :
    c.residueMap p / c.residueMap q ∈ residuePolynomialBand c.top K := by
  rw [div_eq_mul_inv]
  exact (residuePolynomialBand c.top K).mul_mem (c.residue_supported_mem_band K hp)
    (residueLowerField_mem_band c.top K
      ((residueLowerField c.top c.top).inv_mem (c.residue_span_mem_lower hq)))

/-- The full actual retained response is monic over a polynomial algebra in the higher
surviving generators, with coefficients in the strict lower residue field. -/
theorem originalLocalResponse_residue_polynomial {n : ℕ} (P : Profile n)
    (b d : Option (OriginalSelectedBlocks (hD := hD) P)) (K : ℕ+) (hNK : c.top < K)
    (hK : P.xi (originalRowSplitEquiv (hD := hD) P (.inl b)) -
      P.zeta (originalColSplitEquiv (hD := hD) P (.inl d)) = (K : ℤ))
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ)) :
    ∃ A ∈ residuePolynomialBand c.top K,
      c.regularResidue (c.originalLocalResponse P b d) = c.residueMap (X K) + A := by
  obtain ⟨R, hR, q, _, hqreg, hqspan, he⟩ :=
    c.originalLocalResponse_triangular_fraction P b d K hNK hK hmax
  let y : c.selectedIdeal.primeCompl := ⟨q, by
    change q ∉ c.selectedIdeal
    rwa [c.mem_selectedIdeal]⟩
  have hl : c.originalLocalResponse P b d =
      algebraMap Lambda c.RegularRing (X K) + IsLocalization.mk' c.RegularRing R y := by
    apply c.regularEmbedding_injective
    rw [map_add, c.regularEmbedding_polynomial, c.regularEmbedding_fraction]
    exact he
  refine ⟨c.residueMap R / c.residueMap q, c.residue_fraction_mem_band K hR hqspan, ?_⟩
  rw [hl, map_add, c.regularResidue_polynomial, c.regularResidue_fraction]

/-- Each actual upper-Hessenberg response has polynomial higher-generator corrections over
the strict lower residue field, with its own literal protected top. -/
theorem originalHessenbergResponse_residue_polynomial {n : ℕ} (P : Profile n)
    (hB : 0 < originalSelectedCount (hD := hD) P)
    (i j : Fin (originalSelectedCount (hD := hD) P + 1)) (hij : i ≤ j)
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ)) :
    ∃ A ∈ residuePolynomialBand c.top (c.originalHessenbergTop P hB i j hij),
      c.regularResidue (c.originalHessenbergResponse P i j) =
        c.residueMap (X (c.originalHessenbergTop P hB i j hij)) + A := by
  apply c.originalLocalResponse_residue_polynomial
  · have h := c.originalHessenbergDistance_gt_top P hB i j hij
    have he := c.originalHessenbergTop_coe P hB i j hij
    exact_mod_cast (show (c.top : ℤ) < (c.originalHessenbergTop P hB i j hij : ℤ) by omega)
  · exact (c.originalHessenbergTop_coe P hB i j hij).symm
  · exact hmax

end SelectedCoordinate
end SkewCornerDescent.Matrix
