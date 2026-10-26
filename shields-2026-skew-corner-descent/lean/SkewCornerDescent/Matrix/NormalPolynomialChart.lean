/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.VariableSplit
import Mathlib.RingTheory.Localization.FractionRing

/-!
# The polynomial normal coordinate

Supports `shields-2026-skew-corner-descent.tex`, «Equal windows and the determinant defect»
(`sec:normal-chart`). The actual connected prime becomes the polynomial variable over the
fraction field of the other original generators. The change of coordinate is injective and
fixes those generators. Sorry-free.
-/

namespace SkewCornerDescent.Matrix

open SkewGluing

/-- The coefficient field omits exactly the selected original generator. -/
abbrev OtherField (N : ℕ+) := FractionRing (OtherPolynomial N)

/-- Embed the selected-generator presentation into its coefficient field. -/
noncomputable def splitOverField (N : ℕ+) : Lambda →+* Polynomial (OtherField N) :=
  (Polynomial.mapRingHom (algebraMap (OtherPolynomial N) (OtherField N))).comp
    (splitGenerator N).toRingHom

theorem splitOverField_injective (N : ℕ+) : Function.Injective (splitOverField N) :=
  (Polynomial.map_injective _ (IsFractionRing.injective _ _)).comp
    (splitGenerator N).injective

namespace SelectedCoordinate

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The genuine top cofactor in the coefficient field. -/
noncomputable def normalCoefficient : OtherField c.top :=
  algebraMap _ _ ((splitGenerator c.top c.coefficient).coeff 0)

/-- The genuine lower remainder in the coefficient field. -/
noncomputable def normalRemainder : OtherField c.top :=
  algebraMap _ _ ((splitGenerator c.top c.remainder).coeff 0)

theorem normalCoefficient_ne_zero : c.normalCoefficient ≠ 0 :=
  (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 c.split_coefficient_ne_zero

/-- The inverse affine substitution makes the actual prime the new variable. -/
noncomputable def normalChart : Lambda →+* Polynomial (OtherField c.top) := by
  letI := invertibleOfNonzero c.normalCoefficient_ne_zero
  exact (Polynomial.algEquivCMulXAddC c.normalCoefficient c.normalRemainder).symm.toRingHom.comp
    (splitOverField c.top)

theorem normalChart_injective : Function.Injective c.normalChart := by
  let := invertibleOfNonzero c.normalCoefficient_ne_zero
  exact (Polynomial.algEquivCMulXAddC c.normalCoefficient c.normalRemainder).symm.injective.comp
    (splitOverField_injective c.top)

@[simp]
theorem normalChart_prime : c.normalChart (cellSchur D hD.1) = Polynomial.X := by
  let := invertibleOfNonzero c.normalCoefficient_ne_zero
  change (Polynomial.algEquivCMulXAddC c.normalCoefficient c.normalRemainder).symm
    (splitOverField c.top (cellSchur D hD.1)) = Polynomial.X
  have hs : splitOverField c.top (cellSchur D hD.1) =
      Polynomial.C c.normalCoefficient * Polynomial.X + Polynomial.C c.normalRemainder := by
    simp [splitOverField, c.split_prime, normalCoefficient, normalRemainder]
  rw [hs]
  simpa using (Polynomial.algEquivCMulXAddC c.normalCoefficient c.normalRemainder).symm_apply_apply
    Polynomial.X

@[simp]
theorem normalChart_other (j : ℕ+) (hj : j ≠ c.top) :
    c.normalChart (MvPolynomial.X j) =
      Polynomial.C (algebraMap (OtherPolynomial c.top) (OtherField c.top)
        (MvPolynomial.X ⟨j, hj⟩)) := by
  let := invertibleOfNonzero c.normalCoefficient_ne_zero
  simp [normalChart, splitOverField, splitGenerator_other _ _ hj]

/-- Original polynomials embed into the fraction field of the normal-coordinate ring. -/
noncomputable def normalFractionMap : Lambda →+* FractionRing (Polynomial (OtherField c.top)) :=
  (algebraMap _ _).comp c.normalChart

theorem normalFractionMap_injective : Function.Injective c.normalFractionMap :=
  (IsFractionRing.injective (Polynomial (OtherField c.top))
    (FractionRing (Polynomial (OtherField c.top)))).comp c.normalChart_injective

/-- The original rational field embeds into rational functions of the actual normal variable. -/
noncomputable def normalFieldMap :
    actualField →+* FractionRing (Polynomial (OtherField c.top)) :=
  IsFractionRing.lift c.normalFractionMap_injective

@[simp]
theorem normalFieldMap_originalMap (f : Lambda) :
    c.normalFieldMap (originalMap f) = c.normalFractionMap f :=
  IsFractionRing.lift_algebraMap _ f

@[simp]
theorem normalFieldMap_prime :
    c.normalFieldMap (originalMap (cellSchur D hD.1)) =
      algebraMap _ _ (Polynomial.X : Polynomial (OtherField c.top)) := by
  simp [normalFractionMap]

end SelectedCoordinate
end SkewCornerDescent.Matrix
