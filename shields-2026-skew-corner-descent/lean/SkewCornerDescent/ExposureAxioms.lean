/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.ExposureTopology

/-!
# Axiom guards for rational exposure chambers

Pins the kernel footprint of finite triangular sign choices, polynomial avoidance,
regular root separation, and the rational exposure assembly.
-/

/--
info: 'SkewCornerDescent.exists_signed_triangular_assignment' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.exists_signed_triangular_assignment

/--
info: 'SkewCornerDescent.exists_polynomial_ne_zero_on_open' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.exists_polynomial_ne_zero_on_open

/--
info: 'SkewCornerDescent.finite_polynomial_avoidance_chamber' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.finite_polynomial_avoidance_chamber

/--
info: 'SkewCornerDescent.exists_signed_above_anchor' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.exists_signed_above_anchor

/--
info: 'SkewCornerDescent.rational_triangular_chamber' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.rational_triangular_chamber

/--
info: 'SkewCornerDescent.exists_separated_rational_anchors' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.exists_separated_rational_anchors

/--
info: 'SkewCornerDescent.exists_rational_exposure' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.exists_rational_exposure

/--
info: 'SkewCornerDescent.rational_anchor_chamber_open' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.rational_anchor_chamber_open
