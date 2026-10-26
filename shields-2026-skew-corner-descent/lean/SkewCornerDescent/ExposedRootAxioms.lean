/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.OriginalExposedRootOrders

/-!
# Exact original-response root-order footprint guards

Supports `shields-2026-skew-corner-descent.tex` (`lem:peeling`, `thm:dual-period`).
Pins the coordinate slice, simple anchor root and complete maximal-window order producers.
Sorry-free.
-/

/-- info: 'SkewCornerDescent.coordinatePolynomial_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.coordinatePolynomial_eval

/-- info: 'SkewCornerDescent.coordinatePolynomial_constant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.coordinatePolynomial_constant

/-- info: 'SkewCornerDescent.coordinatePolynomial_affine' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.coordinatePolynomial_affine

/-- info: 'SkewCornerDescent.coordinatePolynomial_affine_rootMultiplicity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.coordinatePolynomial_affine_rootMultiplicity

/-- info: 'SkewCornerDescent.CyclicWindows.simpleRoot_pow_order' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.CyclicWindows.simpleRoot_pow_order

/-- info: 'SkewCornerDescent.CyclicWindows.cyclic_inverse_window_root_orders' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.CyclicWindows.cyclic_inverse_window_root_orders

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.simultaneousActualChamber_cyclic_root_orders' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.simultaneousActualChamber_cyclic_root_orders

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalResponses_cyclic_root_orders' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalResponses_cyclic_root_orders
