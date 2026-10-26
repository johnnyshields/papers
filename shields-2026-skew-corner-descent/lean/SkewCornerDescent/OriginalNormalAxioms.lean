/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.ResidueActiveFamily
import SkewCornerDescent.Matrix.OriginalNormalOrders
import SkewCornerDescent.Matrix.OriginalNormalHessenberg

/-!
# Full source classifier and normal series axiom guards

Pins the full original class-count bridges, regular normal-series embedding,
prime power orders and complete original Hessenberg contractions.
-/

/--
info: 'SkewCornerDescent.Matrix.residueHigherResponse_associated_iff' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.residueHigherResponse_associated_iff

/--
info: 'SkewCornerDescent.Matrix.triangularClassCount_eq_source_count' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.triangularClassCount_eq_source_count

/--
info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalHessenberg_class_counts' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalHessenberg_class_counts

/--
info: 'SkewCornerDescent.Matrix.actualResidue_active_family' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.actualResidue_active_family

/--
info: 'SkewCornerDescent.Matrix.SelectedCoordinate.normalSeries_injective' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.normalSeries_injective

/--
info: 'SkewCornerDescent.Matrix.SelectedCoordinate.normalSeries_constant' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.normalSeries_constant

/--
info: 'SkewCornerDescent.Matrix.SelectedCoordinate.normalSeries_prime' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.normalSeries_prime

/--
info: 'SkewCornerDescent.Matrix.SelectedCoordinate.normalSeries_fraction' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.normalSeries_fraction

/--
info: 'SkewCornerDescent.Matrix.SelectedCoordinate.normalChart_prime_pow_dvd_iff' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.normalChart_prime_pow_dvd_iff

/--
info: 'SkewCornerDescent.Matrix.SelectedCoordinate.normalPolynomialSeries_coeff_vanish_iff' depends on
axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.normalPolynomialSeries_coeff_vanish_iff

/--
info: 'SkewCornerDescent.Matrix.SelectedCoordinate.normalSeries_fraction_coeff_vanish_iff' depends on
axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.normalSeries_fraction_coeff_vanish_iff

/--
info: 'SkewCornerDescent.Matrix.SelectedCoordinate.normalChart_of_top_notMem' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.normalChart_of_top_notMem

/--
info: 'SkewCornerDescent.Matrix.SelectedCoordinate.normalSeries_coefficient' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.normalSeries_coefficient

/--
info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalSelected_normalSeries' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalSelected_normalSeries

/--
info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalHessenberg_normalSeries_subdiagonal'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalHessenberg_normalSeries_subdiagonal

/--
info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalHessenberg_normalSeries_det' depends on
axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalHessenberg_normalSeries_det
