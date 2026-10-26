/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.NonVRectangle
import SkewCornerDescent.NonVInterfaces

/-!
# Axiom guards for the ordinary non-V family

Guards the actual legal family, its normalization, and its composed cofactors in
`shields-2026-skew-corner-descent.tex` (`sec:transport`, `eq:non-v-family`,
`eq:non-v-factors`, `eq:non-v-jt`, `eq:non-v-child`).
-/

/--
info: 'SkewCornerDescent.nonVMark_isLegal' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.nonVMark_isLegal

/--
info: 'SkewCornerDescent.nonVMark_fails_hypothesisV' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.nonVMark_fails_hypothesisV

/--
info: 'SkewCornerDescent.nonVDiagram_schur' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.nonVDiagram_schur

/--
info: 'SkewCornerDescent.nonVDiagram_pderiv' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.nonVDiagram_pderiv

/--
info: 'SkewCornerDescent.nonVMark_normalA' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.nonVMark_normalA

/--
info: 'SkewCornerDescent.nonVMark_normalB' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.nonVMark_normalB

/--
info: 'SkewCornerDescent.nonVMark_normalC' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.nonVMark_normalC

/--
info: 'SkewCornerDescent.nonVMark_normalTheta' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.nonVMark_normalTheta

/--
info: 'SkewCornerDescent.nonVMark_row_cofactor' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.nonVMark_row_cofactor

/--
info: 'SkewCornerDescent.nonVMark_rectangle_cofactor' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.nonVMark_rectangle_cofactor

/--
info: 'SkewCornerDescent.nonVMark_rectangle_spans' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.nonVMark_rectangle_spans
