/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.CyclicPeriodDetector

/-!
# Axiom guards for complete cyclic inventories

Pins the constructed closure-word inventories and their signed detector identities.
-/

/--
info: 'SkewCornerDescent.CyclicWindows.closureWord_crossing_product' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.CyclicWindows.closureWord_crossing_product

/--
info: 'SkewCornerDescent.CyclicWindows.inverseWindowSum_closure_short' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.CyclicWindows.inverseWindowSum_closure_short

/--
info: 'SkewCornerDescent.CyclicWindows.inverseWindowSum_closure_full' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.CyclicWindows.inverseWindowSum_closure_full

/--
info: 'SkewCornerDescent.CyclicWindows.windowDefect_short' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.CyclicWindows.windowDefect_short

/--
info: 'SkewCornerDescent.CyclicWindows.windowDefect_full_eq_short' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.CyclicWindows.windowDefect_full_eq_short

/--
info: 'SkewCornerDescent.CyclicWindows.closureWord_crossing_complement' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.CyclicWindows.closureWord_crossing_complement

/--
info: 'SkewCornerDescent.CyclicWindows.inverseWindowSum_closure_period' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.CyclicWindows.inverseWindowSum_closure_period

/--
info: 'SkewCornerDescent.CyclicWindows.windowDefect_period' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.CyclicWindows.windowDefect_period

/--
info: 'SkewCornerDescent.CyclicWindows.dual_period_normalization' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms SkewCornerDescent.CyclicWindows.dual_period_normalization
