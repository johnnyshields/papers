/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.OriginalClosureNormalQuotient
import SkewCornerDescent.Matrix.OriginalClosureCentralResponse
import SkewCornerDescent.Matrix.ResidueActiveFamily
import SkewCornerDescent.Matrix.TrueCapExposureTops
import SkewCornerDescent.Matrix.ResidueRationalFactorization

/-!
# Nonvanishing of every rational virtual factor on the actual closure chart

Supports `shields-2026-skew-corner-descent.tex` (`lem:residue-classifier`,
`lem:original-transfer`). The actual protected central response is transcendental
relative to its true cap pair. Its orientation-scaled original Schur quotient remains
transcendental, so every rational virtual factor is a unit. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing MvPolynomial

noncomputable local instance closureVirtualRatAlgebra (N : ℕ+) :
    Algebra ℚ (OtherField N) := OreLocalization.instAlgebra

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The literal closure quotient is transcendental without assuming residue dependence
or any class matching. Both true caps lie strictly below the central protected top. -/
theorem originalHorizontalClosure_residue_transcendental {n m : ℕ}
    (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalHorizontalClosure P = translate v Q.cells)
    (hB : 0 < originalSelectedCount (hD := hD) P)
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ)) :
    Transcendental ℚ (c.residueMap Q.schur / c.residueMap P.schur ^ 2) := by
  have hBQ : 0 < originalSelectedCount (hD := hD) Q := by
    rw [originalHorizontalClosure_profile_selected_count P Q v hQ]; omega
  let middle : Fin (originalSelectedCount (hD := hD) Q + 1) :=
    ⟨originalSelectedCount (hD := hD) P, by
      rw [originalHorizontalClosure_profile_selected_count P Q v hQ]; omega⟩
  obtain ⟨JP, BP, hfP⟩ := c.originalHessenberg_polynomial_family P hB hmax
  obtain ⟨JQ, BQ, hfQ⟩ := c.originalHessenberg_polynomial_family Q hBQ
    (c.originalHorizontalClosure_profile_component_span P Q v hQ hmax)
  have hcentral := c.originalHorizontalClosure_central_distance P Q v hQ hB
  dsimp only at hcentral
  change originalHessenbergDistance (hD := hD) Q middle middle = _ at hcentral
  rw [c.originalCompletedGap_last_eq_splice P hB,
    c.originalCapSpliceDistance_cap_sum] at hcentral
  have ht0 : JP 0 < JQ middle := by
    have hp := (hfP 0).2.2
    have hh := (hfQ middle).2.2
    rw [originalHessenbergDistance_first P hB] at hp
    have he := c.originalTrueCaps_below_closure P
      (originalSelectedEnumeration P ⟨0, hB⟩)
      (originalSelectedEnumeration P ⟨originalSelectedCount (hD := hD) P - 1, by omega⟩)
    rw [c.originalCapSpliceDistance_cap_sum] at he
    exact_mod_cast (show ((JP 0).val : ℤ) < ((JQ middle).val : ℤ) by omega)
  have ht1 : JP (Fin.last _) < JQ middle := by
    have hp := (hfP (Fin.last _)).2.2
    have hh := (hfQ middle).2.2
    rw [originalHessenbergDistance_last P hB] at hp
    have he := c.originalTrueCaps_below_closure P
      (originalSelectedEnumeration P ⟨0, hB⟩)
      (originalSelectedEnumeration P ⟨originalSelectedCount (hD := hD) P - 1, by omega⟩)
    rw [c.originalCapSpliceDistance_cap_sum] at he
    exact_mod_cast (show ((JP (Fin.last _)).val : ℤ) < ((JQ middle).val : ℤ) by omega)
  let F := (X (JP 0) + BP 0) * (X (JP (Fin.last _)) + BP (Fin.last _))
  have hF : ∀ j ∈ F.vars, j < JQ middle := by
    intro j hj
    rcases Finset.mem_union.mp (vars_mul _ _ hj) with hj | hj
    · exact monicTriangularPolynomial_vars_below ht0 (hfP 0).1 j hj
    · exact monicTriangularPolynomial_vars_below ht1 (hfP (Fin.last _)).1 j hj
  have hF0 : residueHigherEval c.top F ≠ 0 := by
    have hp : F ≠ 0 := mul_ne_zero (monicTriangularPolynomial_prime (hfP 0).1).ne_zero
      (monicTriangularPolynomial_prime (hfP (Fin.last _)).1).ne_zero
    intro hz
    exact hp (residueHigherEval_injective c.top (hz.trans (map_zero _).symm))
  have htrans : Transcendental ℚ
      ((residueHigherEval c.top (X (JQ middle)) +
        residueHigherEval c.top (BQ middle)) / residueHigherEval c.top F) := by
    intro halg
    obtain ⟨α, hα⟩ := residueField_algebraic_constants c.top _ halg
    exact actualResidue_plane_not_rational c.top (hfQ middle).1 hF hF0 α hα.symm
  have hactual : Transcendental ℚ
      (c.regularResidue (c.originalHessenbergResponse Q middle middle) /
        c.originalTrueCapProduct P) := by
    simpa only [F, map_mul, ← map_add, (hfP 0).2.1, (hfP (Fin.last _)).2.1,
      (hfQ middle).2.1, originalTrueCapProduct] using htrans
  obtain ⟨ε, hε, hquot⟩ := c.originalHorizontalClosure_residue_quotient P Q v hQ hB hmax
  have hεQ : (ε : ℚ) ≠ 0 := by rcases hε with rfl | rfl <;> norm_num
  have ht := hactual.aeval (Polynomial.C (ε : ℚ) * Polynomial.X)
    (by rw [Polynomial.natDegree_C_mul_X _ hεQ]; exact one_ne_zero)
    (by rw [Polynomial.leadingCoeff_C_mul_X]; exact mem_nonZeroDivisors_of_ne_zero hεQ)
  have ht' : Transcendental ℚ
      ((ε : OtherField c.top) *
        c.regularResidue (c.originalHessenbergResponse Q middle middle) /
          c.originalTrueCapProduct P) := by
    simpa only [map_mul, Polynomial.aeval_C, Polynomial.aeval_X, map_intCast,
      mul_div_assoc] using ht
  rw [← hquot] at ht'
  exact ht'

/-- Every rational virtual factor is nonzero in the actual residue field, supplied
from literal closure geometry rather than carried as an admissibility binder. -/
theorem originalVirtualClosure_residue_ne_zero {n m : ℕ}
    (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalHorizontalClosure P = translate v Q.cells)
    (hB : 0 < originalSelectedCount (hD := hD) P)
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ))
    (α : ℚ) :
    c.residueMap Q.schur - (α : OtherField c.top) * c.residueMap P.schur ^ 2 ≠ 0 := by
  have ht := c.originalHorizontalClosure_residue_transcendental P Q v hQ hB hmax
  have hf := c.originalSchur_residue_ne_zero P hB hmax
  intro hz
  have he : c.residueMap Q.schur / c.residueMap P.schur ^ 2 = (α : OtherField c.top) :=
    (div_eq_iff (pow_ne_zero 2 hf)).mpr (sub_eq_zero.mp hz)
  apply ht
  rw [he]
  have hcast : algebraMap ℚ (OtherField c.top) α = (α : OtherField c.top) := by
    simpa only [Rat.cast_id] using map_ratCast (algebraMap ℚ (OtherField c.top)) α
  rw [← hcast]
  exact isAlgebraic_algebraMap α

end SkewCornerDescent.Matrix.SelectedCoordinate
