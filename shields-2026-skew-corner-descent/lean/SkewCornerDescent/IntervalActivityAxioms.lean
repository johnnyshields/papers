/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.HessenbergIntervalProducts

/-!
# Complete original interval activity axiom guards

Guards forced complete interval partitions, exact inversion-cost signs,
and the full signed determinant activity expansion used by `prop:normal-interface`.
-/

/-- info: 'SkewCornerDescent.Matrix.hessenberg_prefix_below_upper_endpoint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.hessenberg_prefix_below_upper_endpoint

/-- info: 'SkewCornerDescent.Matrix.hessenberg_forced_subdiagonals' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.hessenberg_forced_subdiagonals

/-- info: 'SkewCornerDescent.Matrix.hessenberg_upper_intervals_disjoint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.hessenberg_upper_intervals_disjoint

/-- info: 'SkewCornerDescent.Matrix.permutation_lower_crossing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.permutation_lower_crossing

/-- info: 'SkewCornerDescent.Matrix.hessenberg_lower_interval_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.hessenberg_lower_interval_unique

/-- info: 'SkewCornerDescent.Matrix.hessenberg_interval_partition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.hessenberg_interval_partition

/-- info: 'SkewCornerDescent.Matrix.hessenberg_inversion_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.hessenberg_inversion_iff

/-- info: 'SkewCornerDescent.Matrix.hessenberg_inversions_card' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.hessenberg_inversions_card

/-- info: 'SkewCornerDescent.Matrix.hessenberg_permutation_sign' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.hessenberg_permutation_sign

/-- info: 'SkewCornerDescent.Matrix.hessenberg_interval_prod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.hessenberg_interval_prod

/-- info: 'SkewCornerDescent.Matrix.hessenberg_signed_weighted_product' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.hessenberg_signed_weighted_product

/-- info: 'SkewCornerDescent.Matrix.hessenberg_det_weighted_intervals' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms
  SkewCornerDescent.Matrix.hessenberg_det_weighted_intervals

