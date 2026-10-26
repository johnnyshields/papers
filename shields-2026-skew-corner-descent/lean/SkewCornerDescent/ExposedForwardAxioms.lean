/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.ExposedDetectorComparison

/-!
# Exposed forward-window and full-period valuation guards

Guards the producers supporting `thm:dual-period`.
-/

/-- info: 'SkewCornerDescent.CyclicWindows.exists_minimal_class_window' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.CyclicWindows.exists_minimal_class_window

/-- info: 'SkewCornerDescent.CyclicWindows.forwardWindowNumerator_factor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.CyclicWindows.forwardWindowNumerator_factor

/-- info: 'SkewCornerDescent.CyclicWindows.forwardWindowLeadingNumerator_eval_pos' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.CyclicWindows.forwardWindowLeadingNumerator_eval_pos

/-- info: 'SkewCornerDescent.CyclicWindows.forwardWindowNumerator_fraction' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.CyclicWindows.forwardWindowNumerator_fraction

/-- info: 'SkewCornerDescent.CyclicWindows.cyclic_forward_window_valuation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.CyclicWindows.cyclic_forward_window_valuation

/-- info: 'SkewCornerDescent.CyclicWindows.exposed_full_detector_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.CyclicWindows.exposed_full_detector_count
