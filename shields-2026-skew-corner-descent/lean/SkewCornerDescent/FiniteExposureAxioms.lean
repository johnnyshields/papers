/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.UniformTopDualNonvanishing
import SkewCornerDescent.Matrix.ConstantActiveLabelDualNonvanishing

/-!
# Finite original exposure axiom guards

Pins the compiled footprints of the finite inactive peeling, actual slice bridges and
constant-label dual detector assemblies.
-/

/-- info: 'SkewCornerDescent.Matrix.remainingActualChamber_response_representatives' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.remainingActualChamber_response_representatives

/-- info: 'SkewCornerDescent.Matrix.remainingActualChamber_shortDetector_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.remainingActualChamber_shortDetector_zero

/-- info: 'SkewCornerDescent.Matrix.remainingActualChamber_fullDetector_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.remainingActualChamber_fullDetector_zero

/-- info: 'SkewCornerDescent.Matrix.remainingActualChamber_dual_exposed_alternative' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.remainingActualChamber_dual_exposed_alternative

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.anchor_slice_sign_implies_root_sign' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.anchor_slice_sign_implies_root_sign

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.simultaneousActualChamber_restrict' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.simultaneousActualChamber_restrict

/-- info: 'SkewCornerDescent.finite_inactive_peeling_reaches_active_extreme' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.finite_inactive_peeling_reaches_active_extreme

/-- info: 'SkewCornerDescent.Matrix.originalChamber_active_extreme_is_omitted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.originalChamber_active_extreme_is_omitted

/-- info: 'SkewCornerDescent.Matrix.uniformTop_original_dual_nonvanishing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.uniformTop_original_dual_nonvanishing

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.actual_anchor_root_eq_affine_label' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.actual_anchor_root_eq_affine_label

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.actual_anchor_root_order_of_labels' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.actual_anchor_root_order_of_labels

/-- info: 'SkewCornerDescent.Matrix.constantActiveLabels_original_dual_nonvanishing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.constantActiveLabels_original_dual_nonvanishing

/-- info: 'SkewCornerDescent.Matrix.fraction_affine_cross_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.fraction_affine_cross_identity

/-- info: 'SkewCornerDescent.Matrix.original_active_affine_representative' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.original_active_affine_representative
