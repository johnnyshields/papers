/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.OriginalDetectorSlices

/-!
# Original detector specialization axiom guards

Pins the footprint of finite-expression specialization and the actual chamber producers.
-/

/-- info: 'SkewCornerDescent.eval₂_fraction_zero_transfer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.eval₂_fraction_zero_transfer

/-- info: 'SkewCornerDescent.CyclicWindows.shortDetector_zero_specialize' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.CyclicWindows.shortDetector_zero_specialize

/-- info: 'SkewCornerDescent.CyclicWindows.fullDetector_zero_specialize' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.CyclicWindows.fullDetector_zero_specialize

/-- info: 'SkewCornerDescent.Matrix.originalExposedNumerator_fraction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.originalExposedNumerator_fraction

/-- info: 'SkewCornerDescent.Matrix.originalCoordinateSlice_regular' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.originalCoordinateSlice_regular

/-- info: 'SkewCornerDescent.Matrix.originalChamber_shortDetector_zero_slice' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.originalChamber_shortDetector_zero_slice

/-- info: 'SkewCornerDescent.Matrix.originalChamber_fullDetector_zero_slice' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.originalChamber_fullDetector_zero_slice
