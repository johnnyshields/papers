/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.OriginalNormalDerivative
import SkewCornerDescent.Matrix.OriginalNormalCosts
import SkewCornerDescent.Matrix.OriginalNormalOrders

/-!
# Complete original normal jet axiom guards

Pins the full inverse-jet support, protected-generator derivatives, interval costs
and detected prime-order bound.
-/

/--
info: 'SkewCornerDescent.Matrix.SelectedCoordinate.normalSeries_fraction_order_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.normalSeries_fraction_order_le

/--
info: 'SkewCornerDescent.Matrix.SelectedCoordinate.normalSubdiagonal_coeff' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.normalSubdiagonal_coeff

/--
info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalHessenberg_normalSeries_coeff' depends on
axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalHessenberg_normalSeries_coeff

/--
info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalLocalResponse_normalSeries' depends on
axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalLocalResponse_normalSeries

/--
info: 'SkewCornerDescent.Matrix.series_coeff_mul_mem_subfield' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.series_coeff_mul_mem_subfield

/--
info: 'SkewCornerDescent.Matrix.series_coeff_inv_mem_subfield' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.series_coeff_inv_mem_subfield

/--
info: 'SkewCornerDescent.Matrix.SelectedCoordinate.normalPolynomialSeries_top' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.normalPolynomialSeries_top

/--
info: 'SkewCornerDescent.Matrix.SelectedCoordinate.normalCoordinate_mem_lower' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.normalCoordinate_mem_lower

/--
info: 'SkewCornerDescent.Matrix.SelectedCoordinate.normalPolynomialSeries_coeff_mem_lower' depends on
axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.normalPolynomialSeries_coeff_mem_lower

/--
info: 'SkewCornerDescent.Matrix.SelectedCoordinate.normalSeries_fraction_coeff_mem_lower' depends on
axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.normalSeries_fraction_coeff_mem_lower

/--
info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalLocalResponse_normalSeries_lower_jets'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalLocalResponse_normalSeries_lower_jets

/--
info: 'SkewCornerDescent.Matrix.series_coeff_det_mem_subfield' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.series_coeff_det_mem_subfield

/--
info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalLocalResponse_normalSeries_coeff_below'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalLocalResponse_normalSeries_coeff_below

/--
info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalLocalResponse_normalSeries_positive_coeff'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalLocalResponse_normalSeries_positive_coeff

/--
info: 'SkewCornerDescent.Matrix.residueGeneratorDeriv_generator' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.residueGeneratorDeriv_generator

/--
info: 'SkewCornerDescent.Matrix.residueGeneratorDeriv_lower' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.residueGeneratorDeriv_lower

/--
info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalLocalResponse_normalSeries_derivative'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalLocalResponse_normalSeries_derivative

/--
info: 
'SkewCornerDescent.Matrix.SelectedCoordinate.originalLocalResponse_normalSeries_derivative_below'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalLocalResponse_normalSeries_derivative_below
