/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.OriginalResidueResponses

/-!
# Full original component residue factorization

Formalizes `shields-2026-skew-corner-descent.tex`, «Equal windows and the determinant defect»
(`sec:normal-chart`, `lem:component-elimination`). The lower scalar includes the complete
removed determinant and both original orientation signs. It is produced and nonzero.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

attribute [local instance] Classical.propDecidable

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The complete original removed determinant is a nonzero scalar in the actual lower
residue field. -/
theorem originalRemoved_residue_lower_scalar {n : ℕ} (P : Profile n)
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ)) :
    c.residueMap (originalRemovedMatrix (hD := hD) P).det ∈ residueLowerField c.top c.top ∧
      c.residueMap (originalRemovedMatrix (hD := hD) P).det ≠ 0 := by
  constructor
  · apply c.residue_span_mem_lower
    exact originalRemovedMatrix_det_span_le P _ (originalBlock_span_le_of_components P _ hmax)
  · exact (c.residueMap_ne_zero_iff _).mpr (not_dvd_originalRemovedMatrix (hD := hD) P)

/-- The actual parent Schur function factors into all ordered upper responses and a produced
nonzero lower scalar; neither the scalar nor a determinant identity is carried as a hypothesis. -/
theorem originalHessenberg_residue_factorization {n : ℕ} (P : Profile n)
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ)) :
    ∃ F ∈ residueLowerField c.top c.top, F ≠ 0 ∧
      c.residueMap P.schur = F * ∏ i, c.regularResidue (c.originalHessenbergResponse P i i) := by
  let σ := Equiv.Perm.sign ((originalHessenbergCols (hD := hD) P).symm.trans
    (originalHessenbergRows (hD := hD) P))
  let τ := Equiv.Perm.sign ((originalColSplitEquiv (hD := hD) P).symm.trans
    (originalRowSplitEquiv (hD := hD) P))
  let s : Lambda := (σ : Lambda) * (τ : Lambda)
  have hunit : IsUnit s := by
    exact (σ.isUnit.map (Int.castRingHom Lambda)).mul (τ.isUnit.map (Int.castRingHom Lambda))
  have hs0 : c.residueMap s ≠ 0 := (hunit.map c.residueMap).ne_zero
  have hsl : s ∈ MvPolynomial.supported ℚ {j : ℕ+ | j < c.top} := by
    apply Subalgebra.mul_mem
    · exact Subalgebra.intCast_mem _ _
    · exact Subalgebra.intCast_mem _ _
  have hslow := c.residue_lower_polynomial hsl
  obtain ⟨hF, hF0⟩ := c.originalRemoved_residue_lower_scalar P hmax
  let d := c.residueMap (originalRemovedMatrix (hD := hD) P).det
  refine ⟨d / c.residueMap s, (residueLowerField c.top c.top).div_mem hF hslow,
    div_ne_zero hF0 hs0, ?_⟩
  have he := congrArg c.regularResidue (c.originalHessenbergResponse_local_det P)
  have hm : c.regularResidue (c.originalHessenbergResponse P).det =
      ((c.originalHessenbergResponse P).map c.regularResidue).det :=
    RingHom.map_det c.regularResidue _
  rw [map_mul, c.regularResidue_polynomial, map_mul, c.regularResidue_polynomial,
    hm, c.originalHessenbergResponse_residue_det,
    originalSplitMatrix_det (hD := hD) P, map_mul] at he
  have hsign : c.regularResidue (σ : c.RegularRing) = c.residueMap (σ : Lambda) := by
    simp only [map_intCast]
  change c.regularResidue (σ : c.RegularRing) *
    (c.residueMap (τ : Lambda) * c.residueMap P.schur) =
      d * ∏ i, c.regularResidue (c.originalHessenbergResponse P i i) at he
  rw [hsign, ← mul_assoc] at he
  have hd : c.residueMap s * c.residueMap P.schur =
      d * ∏ i, c.regularResidue (c.originalHessenbergResponse P i i) := by
    simpa only [s, map_mul] using he
  apply (mul_left_cancel₀ hs0)
  rw [← mul_assoc, mul_div_cancel₀ _ hs0]
  exact hd

end SkewCornerDescent.Matrix.SelectedCoordinate
