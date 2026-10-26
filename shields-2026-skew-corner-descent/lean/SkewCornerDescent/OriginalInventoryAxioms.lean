/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.OriginalPolynomialFamilies
import SkewCornerDescent.Matrix.OriginalSingleWindowGaps
import SkewCornerDescent.Matrix.OriginalRemovedFactors

/-!
# Original polynomial family and determinant inventory guards

Pins complete original response representatives, literal gap consequences and full removed factors.
-/

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalHessenberg_polynomial_family' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.originalHessenberg_polynomial_family

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalHessenberg_polynomial_factorization' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalHessenberg_polynomial_factorization

/-- info: 'SkewCornerDescent.Matrix.sum_two_caps_internal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.sum_two_caps_internal

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalSelected_gap_of_common_top' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.originalSelected_gap_of_common_top

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalSpan_of_common_top' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.originalSpan_of_common_top

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalRemovedMatrix_det_product' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.originalRemovedMatrix_det_product

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalRemovedDiagonal_selected_cofactor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.originalRemovedDiagonal_selected_cofactor

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalRemovedMatrix_det_inventory' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.originalRemovedMatrix_det_inventory
