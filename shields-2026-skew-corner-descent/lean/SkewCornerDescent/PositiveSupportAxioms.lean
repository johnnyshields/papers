/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalSupportAlternative
import SkewCornerDescent.TruncatedCorePhase

/-!
# Axiom guards for actual support nullity and finite phase jets

Guards the complete actual class-support alternative and normalized finite
proper-core phase calculation supporting `shields-2026-skew-corner-descent.tex`
(`lem:positive-support`, `prop:closure-pin`).
-/

/-- info: 'SkewCornerDescent.truncated_core_phase_periodic'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.truncated_core_phase_periodic

/-- info: 'SkewCornerDescent.CyclicWindows.one_active_positive_null_primitive'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.CyclicWindows.one_active_positive_null_primitive

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalWindow_one_active_null_primitive'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.originalWindow_one_active_null_primitive

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalOneActive_alternative'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.originalOneActive_alternative

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalSupport_alternative'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.originalSupport_alternative

/-- info: 'SkewCornerDescent.linear_core_ratio_power'
depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.linear_core_ratio_power

/-- info: 'SkewCornerDescent.truncated_linear_core_phase_periodic'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.truncated_linear_core_phase_periodic

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalSelectedCore_literal_of_left_jet'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.originalSelectedCore_literal_of_left_jet

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalSelectedCore_phase_jets'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.originalSelectedCore_phase_jets

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalCompleted_selected_core_phase'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.originalCompleted_selected_core_phase
