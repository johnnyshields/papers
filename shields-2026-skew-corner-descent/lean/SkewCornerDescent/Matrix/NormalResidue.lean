/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.NormalPolynomialChart
import Mathlib.RingTheory.Polynomial.GaussLemma

/-!
# Residue at the actual selected prime

Supports `shields-2026-skew-corner-descent.tex`, «Equal windows and the determinant defect»
(`sec:normal-chart`). Evaluation of the normal variable at zero has kernel precisely the
actual connected prime, by its primitive univariate presentation and Gauss's lemma.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Irreducibility of the connected prime makes its univariate presentation primitive. -/
theorem split_prime_isPrimitive :
    (splitGenerator c.top (cellSchur D hD.1)).IsPrimitive := by
  apply ((irreducible_cellSchur hD).map (splitGenerator c.top)).isPrimitive
  rw [c.split_prime, Polynomial.natDegree_linear c.split_coefficient_ne_zero]
  exact one_ne_zero

/-- No divisibility is lost by extending the coefficient ring to its fraction field. -/
theorem splitOverField_prime_dvd_iff (f : Lambda) :
    splitOverField c.top (cellSchur D hD.1) ∣ splitOverField c.top f ↔
      cellSchur D hD.1 ∣ f := by
  change (splitGenerator c.top (cellSchur D hD.1)).map (algebraMap _ (OtherField c.top)) ∣
    (splitGenerator c.top f).map (algebraMap _ (OtherField c.top)) ↔ _
  rw [← c.split_prime_isPrimitive.dvd_iff_fraction_map_dvd_fraction_map (OtherField c.top)]
  exact map_dvd_iff (splitGenerator c.top)

/-- The normal chart vanishes at zero exactly on multiples of the actual prime. -/
theorem normalChart_coeff_zero_iff (f : Lambda) :
    (c.normalChart f).coeff 0 = 0 ↔ cellSchur D hD.1 ∣ f := by
  let := invertibleOfNonzero c.normalCoefficient_ne_zero
  rw [← Polynomial.X_dvd_iff, ← c.normalChart_prime]
  change (Polynomial.algEquivCMulXAddC c.normalCoefficient c.normalRemainder).symm
      (splitOverField c.top (cellSchur D hD.1)) ∣
    (Polynomial.algEquivCMulXAddC c.normalCoefficient c.normalRemainder).symm
      (splitOverField c.top f) ↔ _
  rw [map_dvd_iff]
  exact c.splitOverField_prime_dvd_iff f

/-- Polynomial residue in the coefficient field, constructed from the actual coordinate. -/
noncomputable def residueMap : Lambda →+* OtherField c.top :=
  Polynomial.constantCoeff.comp c.normalChart

@[simp]
theorem residueMap_eq_zero_iff (f : Lambda) :
    c.residueMap f = 0 ↔ cellSchur D hD.1 ∣ f :=
  c.normalChart_coeff_zero_iff f

/-- A polynomial denominator is regular precisely when its actual residue is nonzero. -/
theorem residueMap_ne_zero_iff (f : Lambda) :
    c.residueMap f ≠ 0 ↔ ¬ cellSchur D hD.1 ∣ f :=
  not_congr (c.residueMap_eq_zero_iff f)

@[simp]
theorem residueMap_other (j : ℕ+) (hj : j ≠ c.top) :
    c.residueMap (MvPolynomial.X j) =
      algebraMap (OtherPolynomial c.top) (OtherField c.top) (MvPolynomial.X ⟨j, hj⟩) := by
  simp [residueMap, c.normalChart_other j hj]

end SkewCornerDescent.Matrix.SelectedCoordinate
