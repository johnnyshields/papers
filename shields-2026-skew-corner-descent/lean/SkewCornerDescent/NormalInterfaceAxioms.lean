/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.DirectedRatioEnergy
import SkewCornerDescent.Matrix.OriginalInternalNormalFrontiers

/-!
# Axiom guards for actual normal-interface ingredients

Guards the complete directed profile-ratio energy, both normal-cost
frontiers, and their actual internal-source gap and independence producers.
Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
-/

/-- info: 'SkewCornerDescent.near_one_prod_jets'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.near_one_prod_jets

/-- info: 'SkewCornerDescent.directed_ratio_product_energy'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.directed_ratio_product_energy

/-- info: 'SkewCornerDescent.directed_profile_ratio_product'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.directed_profile_ratio_product

/-- info: 'SkewCornerDescent.directed_profile_ratio_first'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.directed_profile_ratio_first

/-- info: 'SkewCornerDescent.directed_profile_ratio_energy'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.directed_profile_ratio_energy

/-- info: 'SkewCornerDescent.directed_profile_ratio_energy_pos'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.directed_profile_ratio_energy_pos

/-- info: 'SkewCornerDescent.CyclicWindows.windowSum_short_period_lt'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.CyclicWindows.windowSum_short_period_lt

/-- info: 'SkewCornerDescent.Matrix.hessenberg_permutation_coeff_deriv_two_frontiers'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.hessenberg_permutation_coeff_deriv_two_frontiers

/-- info: 'SkewCornerDescent.Matrix.hessenberg_coeff_deriv_two_frontiers'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.hessenberg_coeff_deriv_two_frontiers

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalCompletedGap_gt_top'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.originalCompletedGap_gt_top

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalInternalDistance_short_period'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalInternalDistance_short_period

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.originalInternal_normal_two_frontiers'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.originalInternal_normal_two_frontiers
