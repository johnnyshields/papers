/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalVerticalComparisonEndLogs
import SkewCornerDescent.Matrix.OriginalUnitMidpointBound

/-!
# Complete original comparison and protected component axiom guards

Guards the actual full-window transports, both closure cap logarithms,
weighted complete end cancellation, and protected unit-component geometry.
-/

/-- info: 'SkewCornerDescent.Matrix.normLog_offsets_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.normLog_offsets_congr

/-- info: 'SkewCornerDescent.Matrix.rightCap_offsets_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.rightCap_offsets_congr

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.original_unit_incoming_positions_high' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.original_unit_incoming_positions_high

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.original_unit_outgoing_positions_high' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.original_unit_outgoing_positions_high

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.original_unit_component_top_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.original_unit_component_top_le

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.original_unit_midpoint_unique' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.original_unit_midpoint_unique

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosure_normal_left_neighborhood' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosure_normal_left_neighborhood

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosure_left_log_coeff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosure_left_log_coeff

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosure_normal_right_neighborhood' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosure_normal_right_neighborhood

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosure_right_log_coeff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalClosure_right_log_coeff

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalWindow_upper_ordered_responses' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalWindow_upper_ordered_responses

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalWindow_upper_ordered_left_responses' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalWindow_upper_ordered_left_responses

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalWindow_lower_ordered_responses' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalWindow_lower_ordered_responses

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalWindow_lower_ordered_right_responses' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalWindow_lower_ordered_right_responses

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalWindow_normal_left_neighborhood' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalWindow_normal_left_neighborhood

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalWindow_normal_right_neighborhood' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalWindow_normal_right_neighborhood

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalWindow_left_log_coeff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalWindow_left_log_coeff

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalWindow_right_log_coeff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalWindow_right_log_coeff

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalAmalgamation_left_log_coeff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalAmalgamation_left_log_coeff

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalAmalgamation_right_log_coeff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalAmalgamation_right_log_coeff

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalComparison_end_log_balance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalHorizontalComparison_end_log_balance

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalVerticalClosure_profile_component_span' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalVerticalClosure_profile_component_span

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalVerticalClosure_profile_join_no_interior' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalVerticalClosure_profile_join_no_interior

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalVerticalClosure_left_log_coeff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalVerticalClosure_left_log_coeff

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalVerticalClosure_right_log_coeff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalVerticalClosure_right_log_coeff

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalVerticalComparison_end_log_balance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalVerticalComparison_end_log_balance

