/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.ResidueRationalFactorization

/-!
# Actual rational factorization axiom guards

Guards active integer root exponents and their exact actual field factorization.
-/

/-- info: 'SkewCornerDescent.splitActiveRoots_exponent_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.splitActiveRoots_exponent_ne_zero

/-- info: 'SkewCornerDescent.sum_root_counts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.sum_root_counts

/-- info: 'SkewCornerDescent.splitActiveRoots_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.splitActiveRoots_sum

/-- info: 'SkewCornerDescent.splitPolynomial_eval_grouped' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.splitPolynomial_eval_grouped

/-- info: 'SkewCornerDescent.splitRational_eval_factorization' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.splitRational_eval_factorization

/-- info: 'SkewCornerDescent.Matrix.actualResidue_plane_not_rational' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.actualResidue_plane_not_rational

/-- info: 'SkewCornerDescent.Matrix.actualResidue_rational_factorization' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SkewCornerDescent.Matrix.actualResidue_rational_factorization
