/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.ActualExposureChambers

/-!
# Axiom guards for actual real response exposure

Pins supported residue fraction clearing, faithful real representatives, and the
nonempty open exposure construction supplied by complete original matrices.
-/

namespace SkewCornerDescent.Matrix

/--
info: 'SkewCornerDescent.Matrix.residueLowerField_fraction' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms residueLowerField_fraction

/--
info: 'SkewCornerDescent.Matrix.residuePolynomialBand_fraction' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms residuePolynomialBand_fraction

/--
info: 'SkewCornerDescent.Matrix.realResiduePolynomial_injective' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms realResiduePolynomial_injective

/--
info: 'SkewCornerDescent.Matrix.real_cross_difference_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms real_cross_difference_ne_zero

/--
info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalLocalResponse_residue_representatives' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SelectedCoordinate.originalLocalResponse_residue_representatives

/--
info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalResponses_real_representatives' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SelectedCoordinate.originalResponses_real_representatives

/--
info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalResponses_exposure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SelectedCoordinate.originalResponses_exposure

/--
info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalResponses_open_exposure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SelectedCoordinate.originalResponses_open_exposure

/--
info: 'SkewCornerDescent.rational_anchor_chamber_nonempty' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.rational_anchor_chamber_nonempty

end SkewCornerDescent.Matrix
