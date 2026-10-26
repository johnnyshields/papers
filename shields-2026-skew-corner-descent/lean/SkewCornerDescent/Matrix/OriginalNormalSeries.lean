/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.RegularResidue
import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# Faithful normal series of original regular fractions

Supports `shields-2026-skew-corner-descent.tex` (`lem:original-transfer`).
The actual affine normal chart extends to the original local ring as a formal power
series map. Only regular original denominators are inverted; its constant coefficient
is the actual residue. Every normal coefficient retains the full denominator series.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The original polynomial expressed in the actual normal coordinate, as a series. -/
noncomputable def normalPolynomialSeries : Lambda →+* PowerSeries (OtherField c.top) :=
  Polynomial.coeToPowerSeries.ringHom.comp c.normalChart

@[simp]
theorem normalPolynomialSeries_constant (f : Lambda) :
    PowerSeries.constantCoeff (c.normalPolynomialSeries f) = c.residueMap f := by
  simp only [normalPolynomialSeries, RingHom.comp_apply, Polynomial.coeToPowerSeries.ringHom_apply,
    Polynomial.constantCoeff_coe]
  rfl

theorem normalPolynomialSeries_injective : Function.Injective c.normalPolynomialSeries :=
  (Polynomial.coe_injective _).comp c.normalChart_injective

/-- Regularity of the original denominator produces the complete invertible normal series. -/
theorem normalPolynomialSeries_denominator_unit (y : c.selectedIdeal.primeCompl) :
    IsUnit (c.normalPolynomialSeries y) :=
  PowerSeries.isUnit_iff_constantCoeff.mpr
    ((c.normalPolynomialSeries_constant y).symm ▸
      (c.regularDenominator_residue_ne_zero y).isUnit)

/-- The full original local ring embeds into normal series, without an arbitrary-field
specialization and without truncating any inverse denominator. -/
noncomputable def normalSeries : c.RegularRing →+* PowerSeries (OtherField c.top) :=
  IsLocalization.lift c.normalPolynomialSeries_denominator_unit

@[simp]
theorem normalSeries_polynomial (f : Lambda) :
    c.normalSeries (algebraMap Lambda c.RegularRing f) = c.normalPolynomialSeries f :=
  IsLocalization.lift_eq _ f

theorem normalSeries_injective : Function.Injective c.normalSeries := by
  apply (IsLocalization.lift_injective_iff _).mpr
  intro x y
  rw [(FaithfulSMul.algebraMap_injective Lambda c.RegularRing).eq_iff,
    c.normalPolynomialSeries_injective.eq_iff]

/-- The constant coefficient of a complete original fraction is precisely its residue. -/
theorem normalSeries_constant :
    PowerSeries.constantCoeff.comp c.normalSeries = c.regularResidue := by
  apply IsLocalization.ringHom_ext c.selectedIdeal.primeCompl
  apply RingHom.ext
  intro f
  simp only [RingHom.comp_apply, c.normalSeries_polynomial, c.regularResidue_polynomial,
    c.normalPolynomialSeries_constant]

@[simp]
theorem normalSeries_constant_apply (f : c.RegularRing) :
    PowerSeries.constantCoeff (c.normalSeries f) = c.regularResidue f :=
  RingHom.congr_fun c.normalSeries_constant f

@[simp]
theorem normalSeries_prime :
    c.normalSeries (algebraMap Lambda c.RegularRing (cellSchur D hD.1)) = PowerSeries.X := by
  simp only [c.normalSeries_polynomial, normalPolynomialSeries, RingHom.comp_apply,
    c.normalChart_prime, Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_X]

/-- The normal series of a regular fraction retains its entire denominator inverse. -/
theorem normalSeries_fraction (f : Lambda) (y : c.selectedIdeal.primeCompl) :
    c.normalSeries (IsLocalization.mk' c.RegularRing f y) =
      c.normalPolynomialSeries f * (c.normalPolynomialSeries y)⁻¹ := by
  apply (IsLocalization.lift_mk'_spec _ _ _ _).2
  rw [mul_left_comm, PowerSeries.mul_inv_cancel _
    (by simpa only [c.normalPolynomialSeries_constant] using
      c.regularDenominator_residue_ne_zero y), mul_one]

end SkewCornerDescent.Matrix.SelectedCoordinate
