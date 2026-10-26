/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.ResidueSingleWindowClasses

/-!
# Single-window and nonplane class axiom guards

Guards the full rational class classification derived from the actual residue equation.
-/

/-- info: 'SkewCornerDescent.triangularPlanePolynomial_not_dvd_of_root_classes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.triangularPlanePolynomial_not_dvd_of_root_classes

/-- info: 'SkewCornerDescent.Matrix.actualResidue_nonplane_not_dvd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.actualResidue_nonplane_not_dvd

/-- info: 'SkewCornerDescent.Matrix.actualResidue_nonplane_class_balance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.actualResidue_nonplane_class_balance

/-- info: 'SkewCornerDescent.triangularClassCount_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.triangularClassCount_le

/-- info: 'SkewCornerDescent.triangularClassCount_pos_of_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.triangularClassCount_pos_of_mem

/-- info: 'SkewCornerDescent.singleWindow_balanced_class_empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.singleWindow_balanced_class_empty

/-- info: 'SkewCornerDescent.Matrix.actualResidue_single_window_classes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.actualResidue_single_window_classes
