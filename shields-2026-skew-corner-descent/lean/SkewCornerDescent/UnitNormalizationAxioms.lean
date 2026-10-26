/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.ResidueUnitNormalization

/-!
# Triangular product and actual residue unit guards

Pins the footprints of the full monic product comparison and actual plane-unit normalization.
-/

/-- info: 'SkewCornerDescent.triangularProducts_associated_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.triangularProducts_associated_eq

/-- info: 'SkewCornerDescent.triangularProducts_scalar_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.triangularProducts_scalar_eq

/-- info: 'SkewCornerDescent.planeFactor_unit_normalization' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.planeFactor_unit_normalization

/-- info: 'SkewCornerDescent.Matrix.actualResidue_unit_normalization' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.actualResidue_unit_normalization
