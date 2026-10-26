/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.InactiveWindowPeeling
import SkewCornerDescent.DualInventoryClosure

/-!
# Axiom guards for inactive peeling and dual inventory closure

Pins the complete cyclic inventories, common-factor cancellation and produced omitted-phase
closure supporting `lem:peeling` and `thm:dual-period`.
-/

/-- info: 'SkewCornerDescent.exposedRoot_regular_fraction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.exposedRoot_regular_fraction

/-- info: 'SkewCornerDescent.CyclicWindows.zmod_periodic_gcd' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.CyclicWindows.zmod_periodic_gcd

/-- info: 'SkewCornerDescent.CyclicWindows.sum_reduced_classDefect' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.CyclicWindows.sum_reduced_classDefect

/-- info: 'SkewCornerDescent.CyclicWindows.inactive_class_average' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.CyclicWindows.inactive_class_average

/-- info: 'SkewCornerDescent.CyclicWindows.inactive_labelSum_valuation_le_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.CyclicWindows.inactive_labelSum_valuation_le_one

/-- info: 'SkewCornerDescent.CyclicWindows.inactive_short_detector_count_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.CyclicWindows.inactive_short_detector_count_le

/-- info: 'SkewCornerDescent.CyclicWindows.inactive_short_detector_mask' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.CyclicWindows.inactive_short_detector_mask

/-- info: 'SkewCornerDescent.CyclicWindows.inactive_short_detector_factor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.CyclicWindows.inactive_short_detector_factor

/-- info: 'SkewCornerDescent.CyclicWindows.exposedRoot_peel_inverse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.CyclicWindows.exposedRoot_peel_inverse

/-- info: 'SkewCornerDescent.CyclicWindows.exposedRoot_peel_forward' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.CyclicWindows.exposedRoot_peel_forward

/-- info: 'SkewCornerDescent.CyclicWindows.dual_counts_force_full_defect' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.CyclicWindows.dual_counts_force_full_defect

/-- info: 'SkewCornerDescent.CyclicWindows.exposed_dual_detector_omitted_class' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.CyclicWindows.exposed_dual_detector_omitted_class

/-- info: 'SkewCornerDescent.CyclicWindows.signedLabelSum_peel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.CyclicWindows.signedLabelSum_peel

/-- info: 'SkewCornerDescent.CyclicWindows.shortDetector_class_factor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.CyclicWindows.shortDetector_class_factor

/-- info: 'SkewCornerDescent.CyclicWindows.shortDetector_peel_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.CyclicWindows.shortDetector_peel_zero_iff

/-- info: 'SkewCornerDescent.CyclicWindows.fullDetector_class_factor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.CyclicWindows.fullDetector_class_factor

/-- info: 'SkewCornerDescent.CyclicWindows.inactive_short_detector_general_mask' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.CyclicWindows.inactive_short_detector_general_mask
