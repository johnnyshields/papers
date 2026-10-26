/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.SquareWordFirstJet
import SkewCornerDescent.Matrix.OriginalTransfer

/-!
# The complete original defect of the five-copy square word

Supports `shields-2026-skew-corner-descent.tex` (`rem:square-word`).
The actual source, shared-window union, horizontal closure, and selected one-cell
chart define the paper's original rational defect, with full series inverses.
Sorry-free.
-/

namespace SkewCornerDescent.SquareWordProfiles

open SkewGluing MvPolynomial SkewCornerDescent.Matrix

/-- The complete paper defect for the actual five-copy square configuration. -/
noncomputable def defect : PowerSeries (OtherField coordinate.top) :=
  coordinate.originalDeterminantDefect source amalgamation closure 2 5
    ((1 - Polynomial.X) ^ 4) Polynomial.X

/-- The defining rational pair evaluates to the full original comparison series. -/
theorem defect_eq_full_comparison :
    defect =
      coordinate.normalPolynomialSeries source.schur ^ 2 *
        (coordinate.normalPolynomialSeries amalgamation.schur *
          (coordinate.normalPolynomialSeries source.schur)⁻¹ ^ 2) ^ 5 -
      (1 - coordinate.normalPolynomialSeries closure.schur *
          (coordinate.normalPolynomialSeries source.schur)⁻¹ ^ 2) ^ 4 *
        (coordinate.normalPolynomialSeries closure.schur *
          (coordinate.normalPolynomialSeries source.schur)⁻¹ ^ 2)⁻¹ := by
  simp [defect, SelectedCoordinate.originalDeterminantDefect,
    SelectedCoordinate.originalRationalFunctionSeries]

/-- Exact residue matching makes the actual full defect's constant coefficient zero. -/
theorem defect_coeff_zero : PowerSeries.coeff 0 defect = 0 := by
  have h2 := coordinate_residue_generator_ne_zero 2 (by decide)
  have h4 := coordinate_residue_generator_ne_zero 4 (by decide)
  have hs := coordinate_residue_square_difference_ne_zero
  have hu : coordinate.residueMap source.schur ≠ 0 := by
    rw [source_residue_determinant coordinate.residueMap coordinate_residue_one]
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero 2 h2) (pow_ne_zero 2 h4))
      (pow_ne_zero 2 hs)
  rw [PowerSeries.coeff_zero_eq_constantCoeff, defect_eq_full_comparison]
  simp only [map_sub, map_mul, map_pow, map_one, PowerSeries.constantCoeff_inv,
    SelectedCoordinate.normalPolynomialSeries_constant]
  apply sub_eq_zero.mpr
  have h := square_word_original_residue_matching coordinate.residueMap
    coordinate_residue_one h2 h4 hs
  calc
    _ = coordinate.residueMap amalgamation.schur ^ 5 /
        coordinate.residueMap source.schur ^ 8 := by field_simp
    _ = _ := by simpa only [div_eq_mul_inv, inv_pow] using h

end SkewCornerDescent.SquareWordProfiles
