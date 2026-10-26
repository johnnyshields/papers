/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.SquareWordDefect
import SkewCornerDescent.SquareWordRemainingMixed

/-!
# The complete original first-normal square-word coefficient

Supports `shields-2026-skew-corner-descent.tex` (`rem:square-word`).
The actual source, union, and closure determinants produce every residue and
mixed jet; the complete rational comparison retains both inverse jets.
Sorry-free.
-/

namespace SkewCornerDescent.SquareWordProfiles

open SkewGluing MvPolynomial SkewCornerDescent.Matrix

/-- The displayed mixed coefficient belongs to the complete original defect.
No jet, denominator unit, residue match, or scalar coefficient is supplied.

**Differs from the paper's route.** Complete original double-cofactor expansions
and the full first rational jet replace the short-bin transfer identity. -/
theorem defect_original_first_mixed_coeff :
    residueGeneratorDeriv coordinate.top ⟨7, by decide⟩ (PowerSeries.coeff 1 defect) =
      -2 * (coordinate.residueMap (X 4) - coordinate.residueMap (X 2) ^ 2) ^ 2 /
        (coordinate.residueMap (X 4) ^ 3 * coordinate.residueMap (X 2) ^ 2) := by
  let D := residueGeneratorDeriv coordinate.top ⟨7, by decide⟩
  let U := coordinate.normalPolynomialSeries source.schur
  let A := coordinate.normalPolynomialSeries amalgamation.schur
  let Q := coordinate.normalPolynomialSeries closure.schur
  have h2 := coordinate_residue_generator_ne_zero 2 (by decide)
  have h4 := coordinate_residue_generator_ne_zero 4 (by decide)
  have hs := coordinate_residue_square_difference_ne_zero
  have hx2 : D (coordinate.residueMap (X 2)) = 0 := by
    rw [coordinate_residue_pderiv 7 (by decide)]
    norm_num [pderiv_X, Pi.single_apply]
  have hx4 : D (coordinate.residueMap (X 4)) = 0 := by
    rw [coordinate_residue_pderiv 7 (by decide)]
    norm_num [pderiv_X, Pi.single_apply]
  have hu : PowerSeries.constantCoeff U ≠ 0 :=
    isUnit_iff_ne_zero.mp
      (PowerSeries.isUnit_iff_constantCoeff.mp coordinate_source_closure_units.1)
  have hq : PowerSeries.constantCoeff Q ≠ 0 :=
    isUnit_iff_ne_zero.mp
      (PowerSeries.isUnit_iff_constantCoeff.mp coordinate_source_closure_units.2)
  have hDu : D (PowerSeries.constantCoeff U) = 0 := by
    rw [SelectedCoordinate.normalPolynomialSeries_constant,
      source_residue_determinant coordinate.residueMap coordinate_residue_one]
    simp [Derivation.leibniz, smul_eq_mul, hx2, hx4]
  have hDa : D (PowerSeries.constantCoeff A) = 0 := by
    rw [SelectedCoordinate.normalPolynomialSeries_constant,
      amalgamation_residue_determinant coordinate.residueMap coordinate_residue_one]
    simp [Derivation.leibniz, smul_eq_mul, hx2, hx4]
  have hDq : D (PowerSeries.constantCoeff Q) = 0 := by
    rw [SelectedCoordinate.normalPolynomialSeries_constant,
      closure_residue_determinant coordinate.residueMap coordinate_residue_one]
    simp [Derivation.leibniz, smul_eq_mul, hx2, hx4]
  have hu1 : D (PowerSeries.coeff 1 U) =
      coordinate.residueMap (X 2) ^ 2 * coordinate.residueMap (X 4) *
        (2 * coordinate.residueMap (X 2) ^ 2 - 3 * coordinate.residueMap (X 4)) := by
    rw [coordinate_normal_coeff_one, coordinate_residue_pderiv 7 (by decide)]
    exact source_original_mixed_jet coordinate.residueMap coordinate_residue_one
  have ha1 : D (PowerSeries.coeff 1 A) =
      2 * coordinate.residueMap (X 2) ^ 2 * coordinate.residueMap (X 4) ^ 2 *
        (coordinate.residueMap (X 4) - coordinate.residueMap (X 2) ^ 2) ^ 2 *
        (2 * coordinate.residueMap (X 2) ^ 2 - 3 * coordinate.residueMap (X 4)) := by
    rw [coordinate_normal_coeff_one, coordinate_residue_pderiv 7 (by decide)]
    exact amalgamation_original_mixed_jet coordinate.residueMap coordinate_residue_one
  have hq1 : D (PowerSeries.coeff 1 Q) =
      -2 * coordinate.residueMap (X 2) ^ 2 * coordinate.residueMap (X 4) ^ 3 *
        (coordinate.residueMap (X 2) ^ 2 - 2 * coordinate.residueMap (X 4)) ^ 2 *
        (coordinate.residueMap (X 4) - coordinate.residueMap (X 2) ^ 2) ^ 2 := by
    rw [coordinate_normal_coeff_one, coordinate_residue_pderiv 7 (by decide)]
    exact closure_original_mixed_jet coordinate.residueMap coordinate_residue_one
  have hMul (x y : OtherField coordinate.top) : D (x * y) = x * D y + y * D x := by
    simpa only [smul_eq_mul] using D.leibniz x y
  have h := square_comparison_mixed_first_jet D.toAddMonoidHom hMul
    U A Q hu hq hDu hDa hDq
  have hfn (x : OtherField coordinate.top) : D.toAddMonoidHom x = D x := rfl
  simp only [hfn] at h
  change D (PowerSeries.coeff 1 defect) = _
  rw [defect_eq_full_comparison]
  change D (PowerSeries.coeff 1
    (U ^ 2 * (A * U⁻¹ ^ 2) ^ 5 - (1 - Q * U⁻¹ ^ 2) ^ 4 * (Q * U⁻¹ ^ 2)⁻¹)) = _
  rw [h]
  simp only [hu1, ha1, hq1, U, A, Q, SelectedCoordinate.normalPolynomialSeries_constant,
    source_residue_determinant coordinate.residueMap coordinate_residue_one,
    amalgamation_residue_determinant coordinate.residueMap coordinate_residue_one,
    closure_residue_determinant coordinate.residueMap coordinate_residue_one]
  field_simp
  ring

/-- The actual original first-normal coefficient cannot vanish. -/
theorem defect_coeff_one_ne_zero : PowerSeries.coeff 1 defect ≠ 0 := by
  have h2 := coordinate_residue_generator_ne_zero 2 (by decide)
  have h4 := coordinate_residue_generator_ne_zero 4 (by decide)
  have hs := coordinate_residue_square_difference_ne_zero
  have hn :
      -2 * (coordinate.residueMap (X 4) - coordinate.residueMap (X 2) ^ 2) ^ 2 /
        (coordinate.residueMap (X 4) ^ 3 * coordinate.residueMap (X 2) ^ 2) ≠ 0 :=
    div_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 hs))
      (mul_ne_zero (pow_ne_zero 3 h4) (pow_ne_zero 2 h2))
  intro hz
  have h := defect_original_first_mixed_coeff
  rw [hz, map_zero] at h
  exact hn h.symm

/-- The order of the complete original square-word defect is exactly one. -/
theorem defect_order_one : PowerSeries.order defect = 1 := by
  apply PowerSeries.order_eq_nat.mpr
  refine ⟨defect_coeff_one_ne_zero, ?_⟩
  intro i hi
  have hz : i = 0 := by omega
  subst i
  exact defect_coeff_zero

end SkewCornerDescent.SquareWordProfiles
