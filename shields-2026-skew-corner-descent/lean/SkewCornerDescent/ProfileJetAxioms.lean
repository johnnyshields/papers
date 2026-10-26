/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalProfileProductJets
import SkewCornerDescent.CyclicPairCharges

/-!
# Axiom guards for original profile jets and complete directed pair charges

Guards `shields-2026-skew-corner-descent.tex`
(`lem:early-recovery`, `prop:normal-interface`, `eq:normal-interface`).
The expected footprints are produced by the elaborated declarations.
-/

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.original_equal_response_profile_product_jet'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  SkewCornerDescent.Matrix.SelectedCoordinate.original_equal_response_profile_product_jet

/-- info: 'SkewCornerDescent.Matrix.SelectedCoordinate.original_visible_first_difference'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.Matrix.SelectedCoordinate.original_visible_first_difference

/-- info: 'SkewCornerDescent.CyclicWindows.mem_pairOverlap_iff'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.CyclicWindows.mem_pairOverlap_iff

/-- info: 'SkewCornerDescent.CyclicWindows.card_stateWindow'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.CyclicWindows.card_stateWindow

/-- info: 'SkewCornerDescent.CyclicWindows.card_pairOverlap'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.CyclicWindows.card_pairOverlap

/-- info: 'SkewCornerDescent.CyclicWindows.card_internalPairs'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.CyclicWindows.card_internalPairs

/-- info: 'SkewCornerDescent.CyclicWindows.pairOverlap_sum'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.CyclicWindows.pairOverlap_sum

/-- info: 'SkewCornerDescent.CyclicWindows.sum_stateWindow'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.CyclicWindows.sum_stateWindow

/-- info: 'SkewCornerDescent.CyclicWindows.sum_pairOverlap'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.CyclicWindows.sum_pairOverlap

/-- info: 'SkewCornerDescent.CyclicWindows.pairOverlap_eq_univ_of_boundary'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.CyclicWindows.pairOverlap_eq_univ_of_boundary

/-- info: 'SkewCornerDescent.CyclicWindows.scaled_pair_charge'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SkewCornerDescent.CyclicWindows.scaled_pair_charge

