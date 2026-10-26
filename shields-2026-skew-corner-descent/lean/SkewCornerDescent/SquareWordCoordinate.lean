/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.SquareWordRationalMatch
import SkewCornerDescent.Matrix.OriginalNormalSeries
import SkewCornerDescent.Matrix.ResidueGeneratorDerivation

/-!
# The genuine selected one-cell coordinate of the square word

Supports `shields-2026-skew-corner-descent.tex` (`rem:square-word`).
The selected prime is the actual one-cell function h-one, with cofactor one and
zero lower remainder. Its actual chart, not an arbitrary residue map, is used.
Sorry-free.
-/

namespace SkewCornerDescent.SquareWordProfiles

open SkewGluing MvPolynomial SkewCornerDescent.Matrix

/-- The selected component, distinct from the square parent. -/
def selectedCell : Profile 0 where
  r := ![1]
  g := Fin.elim0
  r_pos := by decide
  g_lt_castSucc := fun i => Fin.elim0 i
  g_lt_succ := fun i => Fin.elim0 i

/-- The actual connected component has exactly the h-one function. -/
theorem selectedCell_schur : selectedCell.schur = X (1 : ℕ+) := by
  simp [Profile.schur, Matrix.det_unique, selectedCell, Profile.xi, Profile.zeta, hh, hPos]

/-- The actual geometric normal coordinate has no extra proof-gap fields. -/
noncomputable def coordinate :
    SelectedCoordinate selectedCell.cells selectedCell.isConnectedSkew_cells where
  top := 1
  span_eq := by decide
  coefficient := 1
  remainder := 0
  coefficient_ne_zero := one_ne_zero
  coefficient_lower := Subalgebra.one_mem _
  remainder_lower := Subalgebra.zero_mem _
  prime_eq := by
    rw [cellSchur_cells, selectedCell_schur]
    simp [affineCoordinate]

/-- The true selected coordinate's complete chart sends h-one to the normal variable. -/
theorem coordinate_chart_one : coordinate.normalChart (X (1 : ℕ+)) = Polynomial.X := by
  have h := coordinate.normalChart_prime
  rw [cellSchur_cells, selectedCell_schur] at h
  exact h

/-- The actual selected residue kills h-one, as required by the full determinant proofs. -/
theorem coordinate_residue_one : coordinate.residueMap (X (1 : ℕ+)) = 0 := by
  simp [SelectedCoordinate.residueMap, coordinate_chart_one]

/-- Original h-one differentiation is complete normal differentiation in this
actual chart; the identity holds for every original polynomial. -/
theorem coordinate_chart_pderiv_one (p : Lambda) :
    coordinate.normalChart (pderiv (1 : ℕ+) p) =
      (coordinate.normalChart p).derivative := by
  have hconst (q : ℚ) : (coordinate.normalChart (C q)).derivative = 0 := by
    simp [SelectedCoordinate.normalChart, splitOverField, splitGenerator]
  have hgen (j : ℕ+) : (coordinate.normalChart (X j)).derivative =
      if j = 1 then 1 else 0 := by
    by_cases hj : j = 1
    · subst j
      rw [coordinate_chart_one]
      simp
    · rw [coordinate.normalChart_other j hj]
      simp [hj]
  induction p using MvPolynomial.induction_on with
  | C q => simp only [pderiv_C, map_zero, hconst]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p j hp =>
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, map_add, map_mul, map_mul,
      map_mul, Polynomial.derivative_mul, hp, pderiv_X]
    simp only [Pi.single_apply, apply_ite, map_one, map_zero, hgen]
    split_ifs <;> ring

/-- The full first normal jet is the actual residue of the original h-one derivative. -/
theorem coordinate_normal_coeff_one (p : Lambda) :
    PowerSeries.coeff 1 (coordinate.normalPolynomialSeries p) =
      coordinate.residueMap (pderiv (1 : ℕ+) p) := by
  simp [SelectedCoordinate.normalPolynomialSeries, SelectedCoordinate.residueMap,
    coordinate_chart_pderiv_one, Polynomial.coeff_derivative]

/-- Every surviving original partial derivative commutes with the actual
one-cell residue. The removed generator is fixed at zero, not differentiated. -/
theorem coordinate_residue_pderiv (j : ℕ+) (hj : j ≠ 1) (p : Lambda) :
    residueGeneratorDeriv coordinate.top ⟨j, hj⟩ (coordinate.residueMap p) =
      coordinate.residueMap (pderiv j p) := by
  let D := residueGeneratorDeriv coordinate.top ⟨j, hj⟩
  have hconst (q : ℚ) : D (coordinate.residueMap (C q)) = 0 := by
    simp [D, SelectedCoordinate.residueMap, SelectedCoordinate.normalChart,
      splitOverField, splitGenerator]
  have hgen (k : ℕ+) : D (coordinate.residueMap (X k)) =
      if k = j then 1 else 0 := by
    by_cases hk : k = 1
    · subst k
      rw [coordinate_residue_one, map_zero, ite_eq_right (Ne.symm hj)]
    · rw [coordinate.residueMap_other k hk]
      change residueGeneratorDeriv coordinate.top ⟨j, hj⟩
        (residueGenerator coordinate.top ⟨k, hk⟩) = _
      have he : (⟨k, hk⟩ : {k : ℕ+ // k ≠ coordinate.top}) = ⟨j, hj⟩ ↔ k = j :=
        Subtype.ext_iff
      simp only [residueGeneratorDeriv_generator, he]
  change D (coordinate.residueMap p) = _
  induction p using MvPolynomial.induction_on with
  | C q => simp only [pderiv_C, map_zero, hconst]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p k hp =>
    rw [map_mul, Derivation.leibniz, smul_eq_mul, smul_eq_mul, hp,
      Derivation.leibniz, smul_eq_mul, smul_eq_mul, map_add, map_mul, map_mul, pderiv_X]
    simp only [Pi.single_apply, apply_ite, map_one, map_zero, hgen]

/-- Every actual surviving generator remains nonzero in the selected residue field. -/
theorem coordinate_residue_generator_ne_zero (j : ℕ+) (hj : j ≠ 1) :
    coordinate.residueMap (X j) ≠ 0 := by
  intro hz
  have hd := congrArg (residueGeneratorDeriv coordinate.top ⟨j, hj⟩) hz
  rw [coordinate_residue_pderiv j hj] at hd
  simp [pderiv_X] at hd

/-- The two distinct full response factors do not collapse in the actual chart. -/
theorem coordinate_residue_square_difference_ne_zero :
    coordinate.residueMap (X 4) - coordinate.residueMap (X 2) ^ 2 ≠ 0 := by
  intro hz
  have hp : coordinate.residueMap (X 4 - X 2 ^ 2) = 0 := by
    simpa only [map_sub, map_pow] using hz
  have hd := congrArg (residueGeneratorDeriv coordinate.top ⟨4, by decide⟩) hp
  rw [coordinate_residue_pderiv 4 (by decide)] at hd
  norm_num [pderiv_X, Pi.single_apply] at hd

/-- The complete source and full closure series are genuine units, from their
computed actual determinants rather than a supplied denominator condition. -/
theorem coordinate_source_closure_units :
    IsUnit (coordinate.normalPolynomialSeries source.schur) ∧
      IsUnit (coordinate.normalPolynomialSeries closure.schur) := by
  have h2 := coordinate_residue_generator_ne_zero 2 (by decide)
  have h4 := coordinate_residue_generator_ne_zero 4 (by decide)
  have hs := coordinate_residue_square_difference_ne_zero
  constructor
  · apply PowerSeries.isUnit_iff_constantCoeff.mpr
    rw [SelectedCoordinate.normalPolynomialSeries_constant,
      source_residue_determinant coordinate.residueMap coordinate_residue_one]
    apply isUnit_iff_ne_zero.mpr
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero 2 h2) (pow_ne_zero 2 h4))
      (pow_ne_zero 2 hs)
  · apply PowerSeries.isUnit_iff_constantCoeff.mpr
    rw [SelectedCoordinate.normalPolynomialSeries_constant,
      closure_residue_determinant coordinate.residueMap coordinate_residue_one]
    apply isUnit_iff_ne_zero.mpr
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero 2 h2) (pow_ne_zero 5 h4))
      (pow_ne_zero 4 hs)

end SkewCornerDescent.SquareWordProfiles
