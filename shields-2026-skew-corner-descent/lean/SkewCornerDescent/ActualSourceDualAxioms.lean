/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.ActualSourceDualNonvanishing
import SkewCornerDescent.Matrix.ResidueActiveClasses
import SkewCornerDescent.Matrix.AutomaticOpenDetector

/-!
# Original source dual detector axiom guards

Pins the true cap fractions, residue classifier and original matrix assemblies.
-/

/-- info: 'SkewCornerDescent.Matrix.originalCapFraction_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.originalCapFraction_eq

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.simultaneousActualChamber_cap_fraction_pos' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.simultaneousActualChamber_cap_fraction_pos

/-- info: 'SkewCornerDescent.Matrix.trueCaps_original_dual_nonvanishing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.trueCaps_original_dual_nonvanishing

/-- info: 'SkewCornerDescent.Matrix.actualResidue_active_class' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.actualResidue_active_class

/-- info: 'SkewCornerDescent.Matrix.actualResidue_active_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.actualResidue_active_identity

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalMatrices_dual_nonvanishing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.originalMatrices_dual_nonvanishing

/-- info: 'SkewCornerDescent.CyclicWindows.one_position_short_detector_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.CyclicWindows.one_position_short_detector_zero

/-- info: 'SkewCornerDescent.Matrix.constantActiveLabels_automatic_full_nonvanishing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.constantActiveLabels_automatic_full_nonvanishing
