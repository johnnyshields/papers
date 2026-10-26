/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.ActualExposedWindowPoles

/-!
# Exposed original-response pole footprint guards

Supports `shields-2026-skew-corner-descent.tex` (`lem:peeling`, `thm:dual-period`).
Guards the exact cyclic clearing, same-sign leading specialization, and original-matrix
chamber composition. Sorry-free.
-/

/-- info: 'SkewCornerDescent.clearedPoleSum_fraction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.clearedPoleSum_fraction

/-- info: 'SkewCornerDescent.clearedPoleSum_eval_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.clearedPoleSum_eval_pos

/-- info: 'SkewCornerDescent.clearedPoleSum_not_dvd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.clearedPoleSum_not_dvd

/-- info: 'SkewCornerDescent.clearedPoleSum_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.clearedPoleSum_ne_zero

/-- info: 'SkewCornerDescent.clearedInverseResponseSum_eval_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.clearedInverseResponseSum_eval_pos

/-- info: 'SkewCornerDescent.clearedInverseResponseSum_not_dvd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.clearedInverseResponseSum_not_dvd

/-- info: 'SkewCornerDescent.clearedInverseResponseSum_fraction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.clearedInverseResponseSum_fraction

/-- info: 'SkewCornerDescent.normalizedResponseNumerator_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.normalizedResponseNumerator_pos

/-- info: 'SkewCornerDescent.CyclicWindows.sum_class_window_counts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.CyclicWindows.sum_class_window_counts

/-- info: 'SkewCornerDescent.CyclicWindows.windowProduct_eq_class_product' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.CyclicWindows.windowProduct_eq_class_product

/-- info: 'SkewCornerDescent.CyclicWindows.exists_maximal_class_window' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.CyclicWindows.exists_maximal_class_window

/-- info: 'SkewCornerDescent.CyclicWindows.cyclic_inverse_window_numerator_eval_pos' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.CyclicWindows.cyclic_inverse_window_numerator_eval_pos

/-- info: 'SkewCornerDescent.CyclicWindows.cyclic_inverse_window_numerator_not_dvd' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.CyclicWindows.cyclic_inverse_window_numerator_not_dvd

/-- info: 'SkewCornerDescent.CyclicWindows.cyclic_inverse_window_numerator_fraction' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.CyclicWindows.cyclic_inverse_window_numerator_fraction

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.simultaneousActualChamber_cyclic_pole' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.simultaneousActualChamber_cyclic_pole

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalResponses_cyclic_poles' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalResponses_cyclic_poles

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.exposedResponse_fraction' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.exposedResponse_fraction

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.exposedCyclicWindow_fraction' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.exposedCyclicWindow_fraction
