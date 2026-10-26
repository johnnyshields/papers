/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalEndLogLocality
import SkewCornerDescent.Matrix.OriginalUnitEffectiveCoordinates

/-!
# Complete original endpoint locality and unit-fiber axiom guards

Guards the complete boundary logarithms and original full prefix/suffix producers
used by `prop:normal-interface` and `lem:early-recovery`.
-/

/-- info: 'SkewCornerDescent.Matrix.hessenberg_boundary_condensation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.hessenberg_boundary_condensation

/-- info: 'SkewCornerDescent.Matrix.hessenberg_boundary_log_coeff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.hessenberg_boundary_log_coeff

/-- info: 'SkewCornerDescent.Matrix.logOf_mul_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.logOf_mul_complete

/-- info: 'SkewCornerDescent.Matrix.leftCap_prefix_locality' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.leftCap_prefix_locality

/-- info: 'SkewCornerDescent.Matrix.rightCap_locality' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.rightCap_locality

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalNormalExtension_inside' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalNormalExtension_inside

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalNormalExtension_det' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalNormalExtension_det

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.original_left_log_prefix_locality' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.original_left_log_prefix_locality

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.original_right_log_suffix_locality' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.original_right_log_suffix_locality

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.original_unit_component_beta' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.original_unit_component_beta

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.original_unit_component_matrix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.original_unit_component_matrix

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.original_unit_prefix_separation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.original_unit_prefix_separation

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.original_unit_suffix_separation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.original_unit_suffix_separation

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.original_unit_prefix_matrix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.original_unit_prefix_matrix

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.original_unit_suffix_matrix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.original_unit_suffix_matrix

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalUnitPrefixInverse' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalUnitPrefixInverse

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalUnitSuffixInverse' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalUnitSuffixInverse

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.original_unit_effective_incoming' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.original_unit_effective_incoming

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.original_unit_effective_outgoing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.original_unit_effective_outgoing

