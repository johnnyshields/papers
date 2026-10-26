/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.PeeledExposedSlices
import SkewCornerDescent.Matrix.OriginalResponseNonzero

/-!
# Original exposed alternatives and inactive replacement axiom guards

Pins produced exposure, original nonvanishing and finite replacement of actual responses.
-/

/-- info: 'SkewCornerDescent.Matrix.originalChamber_dual_exposed_alternative' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.originalChamber_dual_exposed_alternative

/-- info: 'SkewCornerDescent.CyclicWindows.peeledResponses_update' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.CyclicWindows.peeledResponses_update

/-- info: 'SkewCornerDescent.CyclicWindows.fullDetector_peel_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.CyclicWindows.fullDetector_peel_zero_iff

/-- info: 'SkewCornerDescent.CyclicWindows.shortDetector_update_zero_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.CyclicWindows.shortDetector_update_zero_iff

/-- info: 'SkewCornerDescent.CyclicWindows.fullDetector_update_zero_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.CyclicWindows.fullDetector_update_zero_iff

/-- info: 'SkewCornerDescent.CyclicWindows.replaceResponses_insert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.CyclicWindows.replaceResponses_insert

/-- info: 'SkewCornerDescent.CyclicWindows.shortDetector_replace_zero_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.CyclicWindows.shortDetector_replace_zero_iff

/-- info: 'SkewCornerDescent.CyclicWindows.fullDetector_replace_zero_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.CyclicWindows.fullDetector_replace_zero_iff

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.remainingActualChamber_exposed_slice' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.remainingActualChamber_exposed_slice

/-- info: 'SkewCornerDescent.Matrix.originalMonicResponse_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.originalMonicResponse_ne_zero
