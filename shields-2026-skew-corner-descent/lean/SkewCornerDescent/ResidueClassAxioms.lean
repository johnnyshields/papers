/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.ResiduePlaneClassBalance

/-!
# Residue class balance axiom guards

Guards the exact class-count identities and their actual residue assembly.
-/

/-- info: 'SkewCornerDescent.triangularResponse_factor_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.triangularResponse_factor_count

/-- info: 'SkewCornerDescent.triangularPlanePolynomial_not_dvd_of_top_ne' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.triangularPlanePolynomial_not_dvd_of_top_ne

/-- info: 'SkewCornerDescent.normalizedFactor_count_zero_of_not_dvd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.normalizedFactor_count_zero_of_not_dvd

/-- info: 'SkewCornerDescent.primeClass_cleared_balance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.primeClass_cleared_balance

/-- info: 'SkewCornerDescent.planeClass_off_top_balance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.planeClass_off_top_balance

/-- info: 'SkewCornerDescent.Matrix.actualResidue_off_top_class_balance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.actualResidue_off_top_class_balance
