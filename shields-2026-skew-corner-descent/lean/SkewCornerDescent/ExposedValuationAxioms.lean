/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.OriginalExposedValuations
import SkewCornerDescent.ExposedDetectorComparison

/-!
# Exposed cyclic valuation guards

Guards the producers supporting `lem:peeling` and `thm:dual-period`.
-/

/-- info: 'SkewCornerDescent.exposedRoot_constant_valuation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.exposedRoot_constant_valuation

/-- info: 'SkewCornerDescent.CyclicWindows.exposed_window_valuation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.CyclicWindows.exposed_window_valuation

/-- info: 'SkewCornerDescent.signedInverseResponses_pole' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.signedInverseResponses_pole

/-- info: 'SkewCornerDescent.CyclicWindows.exposed_short_detector_count' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.CyclicWindows.exposed_short_detector_count

/-- info: 'SkewCornerDescent.exposedRoot_intValuation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.exposedRoot_intValuation

/-- info: 'SkewCornerDescent.exposedRoot_fraction_valuation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.exposedRoot_fraction_valuation

/-- info: 'SkewCornerDescent.CyclicWindows.cyclic_inverse_window_valuation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.CyclicWindows.cyclic_inverse_window_valuation

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.simultaneousActualChamber_exposed_slice' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.simultaneousActualChamber_exposed_slice

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.simultaneousActualChamber_cyclic_valuation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.simultaneousActualChamber_cyclic_valuation

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalResponses_cyclic_valuations' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalResponses_cyclic_valuations
