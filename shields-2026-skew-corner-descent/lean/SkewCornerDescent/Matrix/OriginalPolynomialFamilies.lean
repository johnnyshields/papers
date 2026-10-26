/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.ComponentElimination
import SkewCornerDescent.Matrix.ActualResiduePrimes

/-!
# Faithful polynomial families for complete original responses

Formalizes `shields-2026-skew-corner-descent.tex`, «Equal windows and the determinant defect»
(`sec:normal-chart`, `lem:component-elimination`, `lem:residue-classifier`). Each polynomial
uses the actual original endpoint top and the complete produced residue correction.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing MvPolynomial

noncomputable local instance originalFamilyRatAlgebra (N : ℕ+) :
    Algebra ℚ (OtherField N) := OreLocalization.instAlgebra

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Every complete original diagonal response has a faithful monic polynomial representative.
The family retains both exterior responses and all selected occurrences. -/
theorem originalHessenberg_polynomial_family {n : ℕ} (P : Profile n)
    (hB : 0 < originalSelectedCount (hD := hD) P)
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ)) :
    ∃ J : Fin (originalSelectedCount (hD := hD) P + 1) → ResidueHigherIndex c.top,
      ∃ B : Fin (originalSelectedCount (hD := hD) P + 1) → ResidueHigherPolynomial c.top,
        (∀ i, (∀ j ∈ (B i).vars, j < J i) ∧
          residueHigherEval c.top (X (J i) + B i) =
            c.regularResidue (c.originalHessenbergResponse P i i) ∧
          ((J i).val : ℤ) = originalHessenbergDistance (hD := hD) P i i) := by
  let K := fun i : Fin (originalSelectedCount (hD := hD) P + 1) =>
    c.originalHessenbergTop P hB i i le_rfl
  have hK (i) : c.top < K i := by
    have ht := c.originalHessenbergDistance_gt_top P hB i i le_rfl
    have hk := c.originalHessenbergTop_coe P hB i i le_rfl
    change (K i : ℤ) = _ at hk
    exact_mod_cast (show (c.top : ℤ) < (K i : ℤ) by omega)
  let J := fun i => (⟨K i, hK i⟩ : ResidueHigherIndex c.top)
  have hrep (i) : ∃ B : ResidueHigherPolynomial c.top,
      (∀ j ∈ B.vars, j < J i) ∧
        residueHigherEval c.top (X (J i) + B) =
          c.regularResidue (c.originalHessenbergResponse P i i) := by
    obtain ⟨A, hA, he⟩ :=
      c.originalHessenbergResponse_residue_polynomial P hB i i le_rfl hmax
    obtain ⟨B, hsupport, hval⟩ := residuePolynomialBand_representative c.top (K i) hA
    refine ⟨B, hsupport, ?_⟩
    rw [map_add, hval, he, c.residueMap_other (K i) (ne_of_gt (hK i))]
    simp only [residueHigherEval, aeval_X]
    rfl
  choose B hsupport hval using hrep
  exact ⟨J, B, fun i => ⟨hsupport i, hval i,
    c.originalHessenbergTop_coe P hB i i le_rfl⟩⟩

/-- Actual parent factorization in the faithful polynomial presentation, with the complete
removed lower determinant and orientation scalar produced by original elimination. -/
theorem originalHessenberg_polynomial_factorization {n : ℕ} (P : Profile n)
    (hB : 0 < originalSelectedCount (hD := hD) P)
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ)) :
    ∃ J : Fin (originalSelectedCount (hD := hD) P + 1) → ResidueHigherIndex c.top,
      ∃ B : Fin (originalSelectedCount (hD := hD) P + 1) → ResidueHigherPolynomial c.top,
        ∃ a : residueLowerField c.top c.top, a ≠ 0 ∧
          (∀ i, (∀ j ∈ (B i).vars, j < J i) ∧
            residueHigherEval c.top (X (J i) + B i) =
              c.regularResidue (c.originalHessenbergResponse P i i) ∧
            ((J i).val : ℤ) = originalHessenbergDistance (hD := hD) P i i) ∧
          c.residueMap P.schur = (a : OtherField c.top) *
            residueHigherEval c.top (∏ i, (X (J i) + B i)) := by
  obtain ⟨J, B, h⟩ := c.originalHessenberg_polynomial_family P hB hmax
  obtain ⟨a, ha, ha0, hf⟩ := c.originalHessenberg_residue_factorization P hmax
  refine ⟨J, B, ⟨a, ha⟩, ?_, h, ?_⟩
  · intro hz
    exact ha0 (congrArg (fun z : residueLowerField c.top c.top => (z : OtherField c.top)) hz)
  · rw [map_prod]
    exact hf.trans (congrArg (fun z => a * z)
      (Finset.prod_congr rfl (fun i _ => (h i).2.1.symm)))

end SkewCornerDescent.Matrix.SelectedCoordinate
